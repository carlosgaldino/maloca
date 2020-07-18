use maloca::LockedAllocator;
use rand::Rng;

#[global_allocator]
static ALLOCATOR: LockedAllocator = LockedAllocator::new();

const MAX_STRING_SIZE: usize = 100;

fn main() {
    let mut v = Vec::new();
    for i in 0..10000 {
        v.push(i + 1);
    }
    println!("{:?}", v);
    let total = v.iter().fold(0, |acc, x| acc + x);
    println!("{}", total);

    let f = Box::new(5);
    println!("{:p}", f);

    let mut strings = Vec::new();
    let mut rng = rand::thread_rng();
    let mut total = 0;
    for i in 0..100 {
        let random: f64 = rng.gen();
        let s = "x".repeat(rng.gen_range(1, MAX_STRING_SIZE));

        if random > 0.5 {
            strings.push(s.clone());

            if *strings.get(total).unwrap() != s {
                std::process::abort();
            }
            total += 1;
        }
    }

    println!("{:?}", strings);
    println!("len {}, total {}", strings.len(), total);
}
