use std::cell::RefCell;
fn main() {
    let x = RefCell::new(0);
    *x.borrow_mut() = 1;
    x;
}
