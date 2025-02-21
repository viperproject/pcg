fn other(x: &mut (i32, i32)) {
    (*x).0 = 1;
}
fn main() {
    let mut x = (0, 0);
    other(&mut x);
    x.1;
}
