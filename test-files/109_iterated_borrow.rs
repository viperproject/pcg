struct T {}
fn main () {}
fn test(b: bool) {
    let mut t = T {};
    let mut x : &mut T = &mut t;
    let y : &mut (&mut T) = &mut x;
    let test_y = y;
// PCG: bb0[20] post_main: (*_6) after bb0[12]↓'?11 after bb0[19] -> x↓'?6
// PCG: bb0[20] post_main: borrow: _4 after bb0[5] <after bb0[6]> = &mut  t
// PCG: bb0[20] post_main: borrow: x <after bb0[12]> = &mut  (*_4) after bb0[5]
// PCG: bb0[20] post_main: x↓'?6 after bb0[12] -> _6 after bb0[12]↓'?11 after bb0[12]
    let test_x = x;
    let test_t = t;
}
