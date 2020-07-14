use core::{
    alloc::{GlobalAlloc, Layout},
    mem,
};
use memmap::MmapMut;
use spin::Mutex;

const SIZE: usize = 1024 * 1024;

struct Node {
    size: usize,
    next: Option<&'static mut Node>,
}

impl Node {
    const fn size() -> usize {
        mem::size_of::<Self>()
    }
}

#[derive(Debug)]
struct Allocator {
    pub head: usize,
    pub size: usize,
    pub total: usize,
    mmap: Option<MmapMut>,
}

impl Allocator {
    const fn new() -> Allocator {
        Allocator {
            head: 0,
            size: 0,
            total: 0,
            mmap: None,
        }
    }

    unsafe fn init(&mut self) {
        assert!(SIZE > Node::size());

        let mmap = MmapMut::map_anon(SIZE).unwrap();

        self.head = mmap.as_ptr() as usize;
        self.size = SIZE;
        self.mmap = Some(mmap);
        let ptr = self.head as *mut Node;

        ptr.write(Node {
            size: self.size - Node::size(),
            next: None,
        });
    }

    unsafe fn alloc(&mut self, layout: Layout) -> Result<*mut u8, ()> {
        if self.size == 0 {
            self.init();
        }

        assert_ne!(self.size, 0);

        let head = self.head as *mut Node;
        if layout.size() >= (*head).size {
            return Err(());
        }

        let addr = align(self.head, layout.align())?;
        let ptr = addr as *mut Node;
        ptr.write(Node {
            size: layout.size(),
            next: None,
        });

        self.total += layout.size() + Node::size();
        let ptr = addr + Node::size();
        self.head = layout.size() + ptr;
        let head = self.head as *mut Node;
        head.write(Node {
            size: self.size - self.total,
            next: None,
        });

        Ok(ptr as *mut _)
    }

    unsafe fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        self.total -= layout.size();
    }
}

pub struct LockedAllocator(Mutex<Allocator>);

impl LockedAllocator {
    pub const fn new() -> Self {
        Self(Mutex::new(Allocator::new()))
    }
}

unsafe impl GlobalAlloc for LockedAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut heap = self.0.lock();
        heap.alloc(layout).unwrap_or_else(|_| 0 as *mut u8)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.0.lock().dealloc(ptr, layout);
    }
}

fn align(addr: usize, align: usize) -> Result<usize, ()> {
    Ok((addr + align - 1) & !(align - 1))
}

#[cfg(test)]
mod tests {
    use super::*;

    type Result<T> = std::result::Result<T, ()>;

    #[test]
    fn alignment() -> Result<()> {
        assert_eq!(align(0x1010, 4)?, 0x1010);
        assert_eq!(align(0x1013, 4)?, 0x1014);
        Ok(())
    }

    #[test]
    fn new_heap() -> Result<()> {
        unsafe {
            let mut heap = Allocator::new();
            assert_eq!(heap.size, 0);

            heap.init();
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, SIZE - Node::size());

            let ptr = heap.alloc(Layout::from_size_align_unchecked(10, 4))?;

            assert_eq!(ptr as usize, node as usize + Node::size());

            let node = heap.head as *mut Node;
            assert_eq!((*node).size, SIZE - Node::size() - 10);
        }
        Ok(())
    }

    #[test]
    fn alloc_twice() -> Result<()> {
        unsafe {
            let mut heap = Allocator::new();
            assert_eq!(heap.size, 0);

            heap.init();
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, SIZE - Node::size());

            heap.alloc(Layout::from_size_align_unchecked(10, 4))?;
            let aligned = align(heap.head, 8)?;
            let ptr = heap.alloc(Layout::from_size_align_unchecked(17, 8))?;

            assert_eq!(ptr as usize, Node::size() + aligned);

            let node = heap.head as *mut Node;
            assert_eq!((*node).size, SIZE - 2 * Node::size() - 27);
        }
        Ok(())
    }
}
