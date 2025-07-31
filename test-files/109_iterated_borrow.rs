struct T {}
fn main () {}
fn test(b: bool) {
    let mut t = T {};
    let mut x : &mut T = &mut t; // x -> t
    let y : &mut (&mut T) = &mut x; // y -> x -> t
    let test_y = y; // test_y -> x -> t
    // text_y should be dead, x should become accessible
    // x -> t
    // PCG: bb0[20] post_main: x↓'?6 before bb0[12]:PostMain -> x↓'?6
    let test_x = x; // test_x -> t
    // test_x should be dead,
    let test_t = t;
}
