struct T {}
fn main () {}
fn test(b: bool) {
    let mut t = T {};
    let mut x : &mut T = &mut t;
    let y : &mut (&mut T) = &mut x;
    let test_y = y;
// PCG: bb0[20] post_main: x↓'?6 mid bb0[12] -> x↓'?6
    let test_x = x;
    let test_t = t;
}
