/* recurse */
fn other(x: &mut i32) -> i32 {
    *x
}
fn main() {
    let mut x = 1;
    let y = other(&mut x);
    x;
}
