fn main() {
    let mut x: i32 = 1;
    let mut y = &mut x;
    let z = &mut y;
    let w = &mut **z;
    *w = 2;
    *y;
}
