struct T {}
fn test(cond: bool) {
    let mut x = T {};
    let mut y = T {};
    let mut a: &mut T;
    let x1: &mut T;
    let y1: &mut T;
    let mut a: &mut T;
    if cond {
        a = &mut x;
        x1 = &mut (*a);
        y1 = &mut y;
        // x1 -> a -> x
        // y1 -> y
    } else {
        a = &mut y;
        x1 = &mut x;
        y1 = &mut (*a);
        // x1 -> x
        // y1 -> a -> y
    }
    let test_x1 = x1;
    let test_y1 = y1;
    let test_x = x;
    let test_y = y;
}
fn main() {}
