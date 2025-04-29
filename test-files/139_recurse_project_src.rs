fn other(x: &mut i32, y: (i32, i32)) {
    *x += y.0;
}
fn main() {
    let mut x = 1;
    let mut y = (0, 0);
    y.0 += 1;
    y.1 += 1;
    other(&mut x, y);
    (x);
}
