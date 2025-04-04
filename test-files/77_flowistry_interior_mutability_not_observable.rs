use std::cell::RefCell;
use std::rc::Rc;

fn main() {
    let x = Rc::new(RefCell::new(0));
    let y = x.clone();
    *y.borrow_mut() = 1;
    x;
}
