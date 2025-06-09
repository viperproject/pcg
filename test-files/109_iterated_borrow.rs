struct T {}
fn main () {}
fn test(b: bool) {
    let mut t = T {};
    let mut x : &mut T = &mut t;
    let y : &mut (&mut T) = &mut x;
    let test_y = y;
    // `x` RP shouldn't be labelled at line 10
    // PCG: bb0[20] pre_main: borrow: x = &mut  (*_4) after bb0[5]
    let test_x = x;
    let test_t = t;
}
