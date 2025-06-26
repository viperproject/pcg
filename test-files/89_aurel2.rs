fn main() {
    let mut x = 1;
    let y = &mut x;
    *y = 2;
    // ~PCG: bb0[6] post_main: y: E
    // PCG: bb0[7] post_main: y: W
    let mut z = 2;
    let mut rz = &mut z;
    assert!(x == 2);
}
