struct T {}
fn test(cond: bool) {
    let mut x = T {};
    let mut y = T {};
    let x1: &mut T;
    let y1: &mut T;
    let mut a: &mut T;
    let mut b: &mut T;
    let mut c: &mut T;
    let mut d: &mut T;
    if cond {
        b = &mut x;
        a = &mut (*b);
        x1 = &mut (*a);
        d = &mut y;
        c = &mut d;
        y1 = &mut c;
        // x1 -> a -> b -> x
        // y1 -> c -> d -> y
    } else {
        c = &mut x;
        a = &mut c;
        x1 = &mut a;
        d = &mut y;
        b = &mut d;
        y1 = &mut b;
        // x1 -> a -> c -> x
        // y1 -> b -> d -> y
    }
    let test_x1 = x1;
    let test_y1 = y1;
    let test_x = x;
    let test_y = y;
}
fn main() {}
