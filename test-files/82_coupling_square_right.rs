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
        a = &mut x;
        c = &mut a;
        x1 = &mut c;
        b = &mut y;
        d = &mut b;
        y1 = &mut d;
        // x1 -> c -> a -> x
        // y1 -> d -> b -> y
    }
    let test_x1 = x1;
    let test_y1 = y1;
	let test_c = c;
	let test_a = a;
	let test_d = d;
	let test_b = b;
    let test_x = x;
    let test_y = y;
}
fn main() {}
