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

        let (addr, next) = allocate_first_fit(self.head, 0, layout);
        if addr == 0 {
            return Err(());
        }

        if addr == self.head {
            self.head = next;
        }

        self.total += layout.size();
        let ptr = addr + Node::size();

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

        if (*ptr).next != 0 {
            coalesce(addr, (*ptr).next);
        }

        if prev != 0 {
            coalesce(prev, addr);
        }

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
        heap.alloc(layout).unwrap_or_else(|_| std::ptr::null_mut())
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

#[inline]
unsafe fn coalesce(prev: usize, current: usize) {
    let prev_node = prev as *mut Node;
    let next_addr = align(prev + (*prev_node).size + Node::size(), Node::align());
    if next_addr == current {
        let ptr = current as *mut Node;
        (*prev_node).size += (*ptr).size + Node::size();
        (*prev_node).next = (*ptr).next;
    }
}

unsafe fn allocate_first_fit(addr: usize, prev: usize, layout: Layout) -> (usize, usize) {
    if addr == 0 {
        return (addr, 0);
    }

    let node = addr as *mut Node;
    if (*node).size >= layout.size() {
        let spill = (*node).size - layout.size();
        let mut next = (*node).next;
        let size = if spill > Node::size() {
            layout.size()
        } else {
            (*node).size
        };
        node.write(Node { size, next: 0 });

        if spill > Node::size() {
            let spill_addr = align(addr + size + Node::size(), Node::align());
            let spill_node = spill_addr as *mut Node;
            spill_node.write(Node {
                size: spill - Node::size(),
                next,
            });
            next = spill_addr;
        }

        if prev != 0 {
            let prev_node = prev as *mut Node;
            (*prev_node).next = next;
        }

        return (addr, next);
    }

    allocate_first_fit((*node).next, addr, layout)
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
        // Allocate two blocks
        // AAAABBB_____________
        // Free block B
        // AAAA________________
        // Free block A
        // ____________________
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            let original_size = (*(heap.head as *mut Node)).size;

            let first_head = heap.head;
            let ptr_a = heap.alloc(Layout::from_size_align_unchecked(10, 4))?;
            let layout = Layout::from_size_align_unchecked(17, 8);
            let ptr_b = heap.alloc(layout.clone())?;

            heap.dealloc(ptr_b, layout);

            assert_eq!(heap.head, ptr_b as usize - Node::size());
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, SIZE - 2 * Node::size() - 10);
            assert_eq!((*node).next, 0);

            heap.dealloc(ptr_a, Layout::from_size_align_unchecked(10, 4));
            assert_eq!(heap.head, first_head);
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, original_size);
            assert_eq!((*node).next, 0);

            assert_eq!(heap.total, 0);
        }
        Ok(())
    }

    #[test]
    fn dealloc_fifo() -> Result<()> {
        // Allocate two blocks
        // AAAABBB_____________
        // Free block A
        // ____BBB_____________
        // Free block B
        // ____________________
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            let first_head = heap.head;
            let ptr_a = heap.alloc(Layout::from_size_align_unchecked(10, 4))?;
            let layout = Layout::from_size_align_unchecked(17, 8);
            let ptr_b = heap.alloc(layout.clone())?;
            let final_head = heap.head;

            heap.dealloc(ptr_a, Layout::from_size_align_unchecked(10, 4));

            assert_eq!(heap.head, first_head);
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, 10);
            assert_eq!((*node).next, final_head);
            assert_eq!(heap.total, 17);

            heap.dealloc(ptr_b, layout);
            assert_eq!((*node).next, 0);
            let node = heap.head as *mut Node;
            assert_eq!((*node).next, 0);
            assert_eq!((*node).size, SIZE - Node::size());

            assert_eq!(heap.total, 0);
        }
        Ok(())
    }

    #[test]
    fn dealloc_middle() -> Result<()> {
        // Allocate four blocks
        // AAAABBBCCCDDD_______
        // Free block A
        // ____BBBCCCDDD_______
        // Free block C
        // ____BBB___DDD_______
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            let first_head = heap.head;
            let layout = Layout::new::<u32>();
            let ptr_a = heap.alloc(layout.clone())?;
            let _ptr_b = heap.alloc(layout.clone())?;
            let ptr_c = heap.alloc(layout.clone())?;
            let _ptr_d = heap.alloc(layout.clone())?;
            let final_head = heap.head; // After block D

            heap.dealloc(ptr_a, layout.clone());

            assert_eq!(heap.head, first_head);
            let node_a = heap.head as *mut Node;
            assert_eq!((*node_a).size, layout.size());
            assert_eq!((*node_a).next, final_head);
            assert_eq!(heap.total, layout.size() * 3);

            heap.dealloc(ptr_c, layout);
            let addr_c = ptr_c as usize - Node::size();
            assert_eq!((*node_a).next, addr_c);
            let node_c = addr_c as *mut Node;
            assert_eq!((*node_c).next, final_head);
            assert_eq!((*node_c).size, layout.size());

            assert_eq!(heap.total, layout.size() * 2);
        }
        Ok(())
    }

    #[test]
    fn dealloc_no_forward_coalescing() -> Result<()> {
        // Allocate three blocks
        // AAAABBBCCC__________
        // Free block A
        // ____BBBCCC__________
        // Free block B
        // _______CCC__________
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            let first_head = heap.head;
            let layout = Layout::new::<u32>();
            let ptr_a = heap.alloc(layout.clone())?;
            let ptr_b = heap.alloc(layout.clone())?;
            let _ptr_c = heap.alloc(layout.clone())?;
            let final_head = heap.head; // After block D

            heap.dealloc(ptr_a, layout.clone());

            assert_eq!(heap.head, first_head);
            let node_a = heap.head as *mut Node;
            assert_eq!((*node_a).size, layout.size());
            assert_eq!((*node_a).next, final_head);
            assert_eq!(heap.total, layout.size() * 2);

            heap.dealloc(ptr_b, layout);
            assert_eq!((*node_a).next, final_head);
            assert_eq!((*node_a).size, layout.size() * 2 + Node::size());

            assert_eq!(heap.total, layout.size());
        }
        Ok(())
    }

    #[test]
    fn realloc_same_size() -> Result<()> {
        // Allocate two blocks
        // AAAABBB_____________
        // Free block A
        // ____BBB_____________
        // Allocate block C same size as A
        // CCCCBBB_____________
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            let first_head = heap.head;
            let ptr_a = heap.alloc(Layout::from_size_align_unchecked(10, 4))?;
            let layout = Layout::from_size_align_unchecked(17, 8);
            let _ptr_b = heap.alloc(layout.clone())?;
            let final_head = heap.head;

            heap.dealloc(ptr_a, Layout::from_size_align_unchecked(10, 4));

            assert_eq!(heap.head, first_head);
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, 10);
            assert_eq!((*node).next, final_head);
            assert_eq!(heap.total, 17);

            let ptr_c = heap.alloc(Layout::from_size_align_unchecked(10, 4))?;
            assert_eq!(ptr_c as usize, ptr_a as usize);
            assert_eq!(heap.head, final_head);

            assert_eq!(heap.total, 27);
        }
        Ok(())
    }

    #[test]
    fn realloc_smaller_size() -> Result<()> {
        // Allocate two blocks
        // AAAABBB_____________
        // Free block A
        // ____BBB_____________
        // Allocate block C smaller than A
        // CC__BBB_____________
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            let first_head = heap.head;
            let layout = Layout::from_size_align_unchecked(64, 4);
            let ptr_a = heap.alloc(layout.clone())?;
            let _ptr_b = heap.alloc(layout.clone())?;
            let final_head = heap.head;

            heap.dealloc(ptr_a, layout.clone());

            assert_eq!(heap.head, first_head);
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, layout.size());
            assert_eq!((*node).next, final_head);
            assert_eq!(heap.total, layout.size());

            let ptr_c = heap.alloc(Layout::from_size_align_unchecked(32, 4))?;
            let node_c = (ptr_c as usize - Node::size()) as *mut Node;
            assert_eq!((*node_c).size, 32);
            assert_eq!(ptr_c as usize, ptr_a as usize);

            assert_ne!(heap.head, final_head);
            let head_node = heap.head as *mut Node;
            assert_eq!((*head_node).next, final_head);

            assert_eq!(heap.total, 96);
        }
        Ok(())
    }

    #[test]
    fn realloc_smaller_size_no_new_node() -> Result<()> {
        // Allocate two blocks
        // AAAABBB_____________
        // Free block A
        // ____BBB_____________
        // Allocate block C smaller than A but not enough to create a new node
        // In this case there will be some unused space in the C node
        // CCC~BBB_____________
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            let first_head = heap.head;
            let layout = Layout::from_size_align_unchecked(64, 4);
            let ptr_a = heap.alloc(layout.clone())?;
            let _ptr_b = heap.alloc(layout.clone())?;
            let final_head = heap.head;

            heap.dealloc(ptr_a, layout.clone());

            assert_eq!(heap.head, first_head);
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, layout.size());
            assert_eq!((*node).next, final_head);
            assert_eq!(heap.total, layout.size());

            let ptr_c = heap.alloc(Layout::from_size_align_unchecked(48, 4))?;
            let node_c = (ptr_c as usize - Node::size()) as *mut Node;
            assert_eq!((*node_c).size, 64);
            assert_eq!(ptr_c as usize, ptr_a as usize);

            assert_eq!(heap.head, final_head);

            assert_eq!(heap.total, 112);
        }
        Ok(())
    }

    #[test]
    fn realloc_bigger_size() -> Result<()> {
        // Allocate two blocks
        // AAAABBB_____________
        // Free block A
        // ____BBB_____________
        // Allocate block C greater than A
        // ____BBBCCCCCCCC_____
        unsafe {
            let mut heap = Allocator::new();
            heap.init();

            let first_head = heap.head;
            let layout = Layout::from_size_align_unchecked(64, 4);
            let ptr_a = heap.alloc(layout.clone())?;
            let _ptr_b = heap.alloc(layout.clone())?;
            let final_head = heap.head;

            heap.dealloc(ptr_a, layout.clone());

            assert_eq!(heap.head, first_head);
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, layout.size());
            assert_eq!((*node).next, final_head);
            assert_eq!(heap.total, layout.size());

            let ptr_c = heap.alloc(Layout::from_size_align_unchecked(128, 4))?;
            let node_c = (ptr_c as usize - Node::size()) as *mut Node;
            assert_eq!((*node_c).size, 128);
            assert_eq!(ptr_c as usize, final_head + Node::size());

            assert_eq!(heap.head, ptr_a as usize - Node::size());

            let head_node = heap.head as *mut Node;
            assert_eq!((*head_node).next, ptr_c as usize + 128);

            assert_eq!(heap.total, 192);
        }
        Ok(())
    }
}
