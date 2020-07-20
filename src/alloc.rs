use core::{
    alloc::{GlobalAlloc, Layout},
    mem,
};
use memmap::MmapMut;
use spin::Mutex;

const SIZE: usize = 1024 * 1024 * 100;

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

    #[inline(always)]
    fn adjust_size(size: usize) -> usize {
        Layout::from_size_align(size, Self::align())
            .expect("node layout")
            .pad_to_align()
            .size()
    }

    #[inline(always)]
    fn update(addr: usize, size: usize, next: usize) {
        let ptr = addr as *mut Node;
        unsafe {
            (*ptr).size = size;
            (*ptr).next = next;
        }
    }
}

#[derive(Debug)]
struct Allocator {
    pub head: usize,
    pub size: usize,
    pub total: usize, // including node size
    pub allocated: usize,
    mmap: Option<MmapMut>,
}

impl Allocator {
    const fn new() -> Allocator {
        Allocator {
            head: 0,
            size: 0,
            total: 0,
            allocated: 0,
            mmap: None,
        }
    }

    unsafe fn init(&mut self) {
        assert!(SIZE > Node::size());

        let mmap = MmapMut::map_anon(SIZE).unwrap();

        self.head = mmap.as_ptr() as usize;
        self.size = SIZE;
        self.mmap = Some(mmap);
        self.total = Node::size();

        Node::update(self.head, self.size - Node::size(), 0);
    }

    unsafe fn alloc(&mut self, layout: Layout) -> Result<*mut u8, ()> {
        if self.size == 0 {
            self.init();
        }

        assert!(self.size != 0);
        if self.total == self.size {
            return Err(());
        }

        if let Some((addr, next)) = self.allocate_first_fit(self.head, 0, layout) {
            if addr == self.head {
                self.head = next;
            }

            let ptr = addr as *mut Node;
            assert!((*ptr).next == 0);
            self.total += (*ptr).size;
            self.allocated += layout.size();
            let ptr = addr + Node::size();

            Ok(ptr as *mut _)
        } else {
            Err(())
        }
    }

    unsafe fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        assert!(!ptr.is_null());

        let addr = ptr as usize - Node::size();
        let prev = find_previous_node(addr, self.head);
        let ptr = addr as *mut Node;
        let size = (*ptr).size;

        if prev == 0 {
            assert!(addr != self.head);
            Node::update(addr, size, self.head);
            self.head = addr;
        } else {
            let prev_node = prev as *mut Node;
            Node::update(addr, size, (*prev_node).next);
            Node::update(prev, (*prev_node).size, addr);
        }

        if (*ptr).next != 0 {
            self.coalesce(addr, (*ptr).next);
        }

        if prev != 0 {
            self.coalesce(prev, addr);
        }

        self.allocated = self.allocated.saturating_sub(layout.size());
        self.total = self.total.saturating_sub(size);
    }

    unsafe fn allocate_first_fit(
        &mut self,
        addr: usize,
        prev: usize,
        layout: Layout,
    ) -> Option<(usize, usize)> {
        if addr == 0 {
            return None;
        }

        let mut prev = prev;
        let mut node = addr as *mut Node;
        while (*node).size < layout.size() {
            if (*node).next == 0 {
                return None;
            }
            prev = node as usize;
            node = (*node).next as *mut Node;
        }

        let addr = node as usize;
        let adjusted_size = Node::adjust_size(layout.size());
        let spill = (*node).size - adjusted_size;
        let mut next = (*node).next;
        Node::update(addr, adjusted_size, 0);

        if spill > Node::size() {
            let spill_addr = align(addr + adjusted_size + Node::size(), Node::align());
            let spill_size = Node::adjust_size(spill.saturating_sub(Node::size()));
            Node::update(spill_addr, spill_size, next);
            self.total += Node::size();
            next = spill_addr;
        }

        if prev != 0 {
            let prev_node = prev as *mut Node;
            Node::update(prev, (*prev_node).size, next);
        }

        Some((addr, next))
    }

    #[inline(always)]
    unsafe fn coalesce(&mut self, prev: usize, next: usize) {
        let prev_node = prev as *mut Node;
        let next_addr = align(prev + (*prev_node).size + Node::size(), Node::align());
        if next_addr == next {
            let ptr = next as *mut Node;
            let new_size = Node::adjust_size((*prev_node).size + (*ptr).size + Node::size());
            Node::update(prev, new_size, (*ptr).next);
            Node::update(next, 0, 0);
            self.total = self.total.saturating_sub(Node::size());
        }
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
    if addr < head as usize {
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
            let padding = 6;
            assert_eq!((*node).size, SIZE - 2 * Node::size() - 10 - padding);

            assert_eq!(heap.allocated, 10);
            assert_eq!(heap.total, 10 + padding + 2 * Node::size());
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
            let padding = 6 + 7;
            assert_eq!((*node).size, SIZE - 3 * Node::size() - 27 - padding);
            assert_eq!(heap.total, 27 + padding + 3 * Node::size());
            assert_eq!(heap.allocated, 27);
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
            let padding = 6;
            assert_eq!((*node).size, SIZE - 2 * Node::size() - 10 - padding);
            assert_eq!((*node).next, 0);

            heap.dealloc(ptr_a, Layout::from_size_align_unchecked(10, 4));
            assert_eq!(heap.head, first_head);
            let node = heap.head as *mut Node;
            assert_eq!((*node).size, original_size);
            assert_eq!((*node).next, 0);

            assert_eq!(heap.allocated, 0);
            assert_eq!(heap.total, Node::size());
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
            let padding_b = 7;
            assert_eq!((*node).size, 16); // + padding
            assert_eq!((*node).next, final_head);
            assert_eq!(heap.total, 17 + padding_b + 3 * Node::size());
            assert_eq!(heap.allocated, 17);

            heap.dealloc(ptr_b, layout);
            assert_eq!((*node).next, 0);
            let node = heap.head as *mut Node;
            assert_eq!((*node).next, 0);
            assert_eq!((*node).size, SIZE - Node::size());

            assert_eq!(heap.allocated, 0);
            assert_eq!(heap.total, Node::size());
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
            assert_eq!(
                (*node_a).size,
                Layout::from_size_align_unchecked(layout.size(), Node::align())
                    .pad_to_align()
                    .size()
            );
            assert_eq!((*node_a).next, final_head);
            assert_eq!(heap.allocated, layout.size() * 3);
            assert_eq!(
                heap.total,
                layout.size() * 3 + Node::size() * 5 + 3 * 4 /* padding */
            );

            heap.dealloc(ptr_c, layout);
            let addr_c = ptr_c as usize - Node::size();
            assert_eq!((*node_a).next, addr_c);
            let node_c = addr_c as *mut Node;
            assert_eq!((*node_c).next, final_head);
            assert_eq!(
                (*node_c).size,
                Layout::from_size_align_unchecked(layout.size(), Node::align())
                    .pad_to_align()
                    .size()
            );

            assert_eq!(heap.allocated, layout.size() * 2);
            assert_eq!(
                heap.total,
                layout.size() * 2 + Node::size() * 5 + 2 * 4 /* padding */
            );
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
            assert_eq!(
                (*node_a).size,
                Layout::from_size_align_unchecked(layout.size(), Node::align())
                    .pad_to_align()
                    .size()
            );
            assert_eq!((*node_a).next, final_head);
            assert_eq!(
                heap.total,
                layout.size() * 2 + Node::size() * 4 + 2 * 4 /* padding */
            );

            heap.dealloc(ptr_b, layout);
            assert_eq!((*node_a).next, final_head);
            assert_eq!(
                (*node_a).size,
                Node::size() + layout.size() * 2 * 2 /* padding for 2 pointers */
            );

            assert_eq!(heap.allocated, layout.size());
            assert_eq!(
                heap.total,
                layout.size() + 3 * Node::size() + 4 /* padding */
            );
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
            let padding = 6;
            assert_eq!((*node).size, 10 + padding);
            assert_eq!((*node).next, final_head);
            assert_eq!(heap.allocated, 17);
            assert_eq!(heap.total, 17 + 7 /* padding */ + 3 * Node::size());

            let ptr_c = heap.alloc(Layout::from_size_align_unchecked(10, 4))?;
            assert_eq!(ptr_c as usize, ptr_a as usize);
            assert_eq!(heap.head, final_head);
            let head_node = heap.head as *mut Node;
            assert_eq!((*head_node).next, 0);

            let padding = 6 + 7;
            assert_eq!(heap.allocated, 27);
            assert_eq!(heap.total, 27 + padding + 3 * Node::size());
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
            assert_eq!(heap.allocated, layout.size());
            assert_eq!(heap.total, layout.size() + 3 * Node::size());

            let ptr_c = heap.alloc(Layout::from_size_align_unchecked(32, 4))?;
            let node_c = (ptr_c as usize - Node::size()) as *mut Node;
            assert_eq!((*node_c).size, 32);
            assert_eq!(ptr_c as usize, ptr_a as usize);

            assert_ne!(heap.head, final_head);
            let head_node = heap.head as *mut Node;
            assert_eq!((*head_node).next, final_head);

            assert_eq!(heap.allocated, 96);
            assert_eq!(heap.total, 32 + 64 + 4 * Node::size());
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
            assert_eq!(heap.allocated, layout.size());
            assert_eq!(heap.total, layout.size() + 3 * Node::size());

            let ptr_c = heap.alloc(Layout::from_size_align_unchecked(48, 4))?;
            let node_c = (ptr_c as usize - Node::size()) as *mut Node;
            assert_eq!((*node_c).size, 48);
            assert_eq!(ptr_c as usize, ptr_a as usize);

            assert_eq!(heap.head, final_head);
            let head_node = heap.head as *mut Node;
            assert_eq!((*head_node).next, 0);

            assert_eq!(heap.allocated, 112);
            assert_eq!(heap.total, 64 + 48 + 3 * Node::size());
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
            assert_eq!(heap.allocated, layout.size());
            assert_eq!(heap.total, layout.size() + 3 * Node::size());

            let ptr_c = heap.alloc(Layout::from_size_align_unchecked(128, 4))?;
            let node_c = (ptr_c as usize - Node::size()) as *mut Node;
            assert_eq!((*node_c).size, 128);
            assert_eq!(ptr_c as usize, final_head + Node::size());

            assert_eq!(heap.head, ptr_a as usize - Node::size());

            let head_node = heap.head as *mut Node;
            assert_eq!((*head_node).next, ptr_c as usize + 128);

            assert_eq!(heap.allocated, 128 + 64);
            assert_eq!(heap.total, 128 + 64 + 4 * Node::size());
        }
        Ok(())
    }
}
