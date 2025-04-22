fn reborrow_inner<'a, 'b, 'c: 'b>(x: &'a mut &'b mut i32, y: &'c mut i32) {
    *x = y;
}

fn main() {
    let mut a = 1;
    let mut ra = &mut a;
    let mut rra = &mut ra;

    let mut c = 2;
    let mut rc = &mut c;

    reborrow_inner(rra, rc);
}
