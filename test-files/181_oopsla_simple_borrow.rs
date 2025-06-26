fn main() {
    let mut x = 0;
    let mut y = &mut x;
    // PCG: bb0[4] post_main: y: E
    *y = 5;
    // PCG_LIFETIME_DISPLAY: y 0 'a
    // PCG: bb0[6] post_main: borrow: y <mid bb0[6]> = &mut  x
    // PCG: bb0[6] post_main: {y} -> {*y}
    // PCG: bb0[6] post_main: *y: E
    // PCG: bb0[7] post_main: y: W
}
