use core::{
    alloc::{GlobalAlloc, Layout},
    mem,
};
use memmap::MmapMut;
use spin::Mutex;

const SIZE: usize = 1024 * 1024;

#[derive(Debug)]
struct Node {
    size: usize,
    next: usize,
}

impl Node {
    #[inline(always)]
    const fn size() -> usize {
        mem::size_of::<Self>()
    }

    #[inline(always)]
    const fn align() -> usize {
        mem::align_of::<Self>()
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
            next: 0,
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

        let addr = align(self.head, layout.align());
        let ptr = addr as *mut Node;
        let prev_size = (*ptr).size;
        ptr.write(Node {
            size: layout.size(),
            next: 0,
        });

        self.total += layout.size();
        let ptr = addr + Node::size();
        self.head = align(ptr + layout.size(), Node::align());
        let head = self.head as *mut Node;
        head.write(Node {
            size: prev_size - Node::size() - layout.size(),
            next: 0,
        });

        Ok(ptr as *mut _)
    }

    unsafe fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        assert!(!ptr.is_null());

        let addr = ptr as usize - Node::size();
        let prev = find_previous_node(addr, self.head);
        let ptr = addr as *mut Node;

        if prev == 0 {
            ptr.write(Node {
                size: (*ptr).size,
                next: self.head,
            });

            self.head = addr;
        } else {
            let prev_node = prev as *mut Node;
            ptr.write(Node {
                size: (*ptr).size,
                next: (*prev_node).next,
            });
            (*prev_node).next = ptr as usize;
        }

        // TODO: coalesce
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

#[inline(always)]
fn align(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}

#[inline]
fn find_previous_node(addr: usize, head: usize) -> usize {
    if addr < head {
        return 0;
    }

    let mut node = head as *mut Node;
    unsafe {
        while (*node).next < addr && (*node).next != 0 {
            node = (*node).next as *mut Node;
        }
    }

    node as usize
}

#[cfg(test)]
mod tests {
    use super::*;

    type Result<T> = std::result::Result<T, ()>;

    #[test]
    fn alignment() -> Result<()> {
        assert_eq!(align(0x1010, 4), 0x1010);
        assert_eq!(align(0x1013, 4), 0x1014);
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
            assert_eq!((*node).size, SIZE - 2 * Node::size() - 10);

            assert_eq!(heap.total, 10);
        }
        Ok(())
    }

    #[test]
    fn alloc_twice() -> Result<()> {
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            heap.alloc(Layout::from_size_align_unchecked(10, 4))?;
            let aligned = align(heap.head, 8);
            let ptr = heap.alloc(Layout::from_size_align_unchecked(17, 8))?;

            assert_eq!(ptr as usize, Node::size() + aligned);

            let node = heap.head as *mut Node;
            assert_eq!((*node).size, SIZE - 3 * Node::size() - 27);
            assert_eq!(heap.total, 27);
        }
        Ok(())
    }

    #[test]
    fn dealloc_backwards() -> Result<()> {
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            let first_head = heap.head;
            let first_ptr = heap.alloc(Layout::from_size_align_unchecked(10, 4))?;
            let layout = Layout::from_size_align_unchecked(17, 8);
            let ptr = heap.alloc(layout.clone())?;
            let final_head = heap.head;

            heap.dealloc(ptr, layout);

            assert_eq!(heap.head, ptr as usize - Node::size());
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, 17); // TODO: coalesce
            assert_eq!((*node).next, final_head);

            heap.dealloc(first_ptr, Layout::from_size_align_unchecked(10, 4));
            assert_eq!(heap.head, first_head);
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, 10); // TODO: coalesce
            assert_eq!((*node).next, ptr as usize - Node::size());

            assert_eq!(heap.total, 0);
        }
        Ok(())
    }

    #[test]
    fn dealloc_fifo() -> Result<()> {
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            let first_head = heap.head;
            let first_ptr = heap.alloc(Layout::from_size_align_unchecked(10, 4))?;
            let layout = Layout::from_size_align_unchecked(17, 8);
            let ptr = heap.alloc(layout.clone())?;
            let final_head = heap.head;

            heap.dealloc(first_ptr, Layout::from_size_align_unchecked(10, 4));

            assert_eq!(heap.head, first_head);
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, 10);
            assert_eq!((*node).next, final_head);
            assert_eq!(heap.total, 17);

            heap.dealloc(ptr, layout);
            assert_eq!((*node).next, ptr as usize - Node::size());
            let node = (ptr as usize - Node::size()) as *mut Node;
            assert_eq!((*node).next, final_head);
            assert_eq!((*node).size, 17);

            assert_eq!(heap.total, 0);
        }
        Ok(())
    }
}
