use core::{
    alloc::{GlobalAlloc, Layout},
    ops::Deref,
    ptr,
};
use memmap::MmapMut;
use spin::Mutex;
use std::{error::Error, fmt, mem};

const SIZE: usize = 1024 * 1024 * 8;

#[derive(Debug)]
enum AllocError {
    BadAlign,
    OutOfMemory,
}

impl fmt::Display for AllocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AllocError::BadAlign => write!(f, "bad align"),
            AllocError::OutOfMemory => write!(f, "out of memory"),
        }
    }
}

impl Error for AllocError {}

struct Node {
    size: usize,
    next: Option<&'static mut Node>,
}

impl Node {
    const fn size() -> usize {
        mem::size_of::<Self>()
    }
}

struct Allocator {
    head: usize,
    size: usize,
    total: usize,
    mmap: Option<MmapMut>,
}

impl Allocator {
    pub const fn new() -> Allocator {
        Allocator {
            head: 0,
            size: 0,
            total: 0,
            mmap: None,
        }
    }

    fn init(&mut self) {
        let mmap = MmapMut::map_anon(SIZE).unwrap();
        self.head = mmap.as_ptr() as usize;
        self.size = SIZE;
        self.mmap = Some(mmap);
        let ptr = self.head as *mut Node;

        unsafe {
            ptr.write(Node {
                size: self.size - Node::size(),
                next: None,
            });
        }
    }

    fn alloc(&mut self, layout: Layout) -> Result<*mut u8, impl Error> {
        if self.size == 0 {
            self.init();
        }

        let head = self.head as *mut Node;
        let size = unsafe { (*head).size };
        if layout.size() >= size {
            return Err(AllocError::OutOfMemory);
        }

        let addr = align(self.head, layout.align())?;
        let ptr = addr as *mut Node;
        unsafe {
            ptr.write(Node {
                size: layout.size(),
                next: None,
            });
        }

        self.total += layout.size() + Node::size();
        let ptr = addr + Node::size();
        self.head = layout.size() + ptr;
        let head = self.head as *mut Node;
        unsafe {
            head.write(Node {
                size: self.size - self.total,
                next: None,
            });
        }

        Ok(ptr as *mut _)
    }

    unsafe fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        self.total -= layout.size();
    }
}

struct LockedAllocator(Mutex<Allocator>);

impl Deref for LockedAllocator {
    type Target = Mutex<Allocator>;

    fn deref(&self) -> &Mutex<Allocator> {
        &self.0
    }
}

unsafe impl GlobalAlloc for LockedAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut heap = self.lock();
        heap.alloc(layout).unwrap_or_else(|_| 0 as *mut u8)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.lock().dealloc(ptr, layout);
    }
}

#[global_allocator]
static A: LockedAllocator = LockedAllocator(Mutex::new(Allocator::new()));

fn main() {
    let mut v = Vec::new();
    for i in 0..10000 {
        v.push(i + 1);
    }
    println!("{:?}", v);

    let f = Box::new(5);
    println!("{:p}", f);
}

fn align(addr: usize, align: usize) -> Result<usize, AllocError> {
    Ok((addr + align - 1) & !(align - 1))
}
