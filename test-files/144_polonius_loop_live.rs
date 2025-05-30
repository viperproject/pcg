use std::cell::Cell;

thread_local! {
    static COUNTER: Cell<u32> = Cell::new(0);
}

fn random_bool() -> bool {
    COUNTER.with(|c| {
        let val = c.get();
        c.set(val + 1);
        val % 2 == 0
    })
}

fn main() {
    let mut x = 0;
    let mut y = 1;
    let mut r1 = &mut x;
    let mut r2 = &mut *r1;
    while random_bool() {
        if random_bool() {
            r1 = &mut y;
            r2 = &mut *r1;
        } else {
            r2 = &mut y;
            r1 = &mut *r2;
        }
    }
    let z = *r2;
    // let z = *r1;
}
