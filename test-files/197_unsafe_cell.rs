use std::cell::UnsafeCell;

fn main() {
    let mut x = 0;
    let mut cell = UnsafeCell::new(&mut x);
    let y = cell.get_mut();
}
