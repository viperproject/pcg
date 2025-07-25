struct T {}
fn test(cond: bool) {
    let mut x = T {};
    let mut y = T {};
    let x1: &mut T;
    let y1: &mut T;
    let mut a: &mut T;
    let mut b: &mut T;
    let mut c: &mut T;
    if cond {
        b = &mut x;
        a = &mut (*b);
        x1 = &mut (*a);
        c = &mut y;
        y1 = &mut c;
        // x1 -> a -> b -> x
        // y1 -> c -> y
    } else {
        a = &mut x;
        c = &mut a;
        x1 = &mut c;
        b = &mut y;
        y1 = &mut b;
        // x1 -> c -> a -> x
        // y1 -> b -> y
    }
    let test_x1 = x1;
    let test_y1 = y1;
    let test_x = x;
    let test_y = y;
}
fn main() {}
