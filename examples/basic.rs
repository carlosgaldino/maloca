use maloca::LockedAllocator;

#[global_allocator]
static ALLOCATOR: LockedAllocator = LockedAllocator::new();

fn main() {
    let mut v = Vec::new();
    for i in 0..10000 {
        v.push(i + 1);
    }
    println!("{:?}", v);

    let f = Box::new(5);
    println!("{:p}", f);
}
