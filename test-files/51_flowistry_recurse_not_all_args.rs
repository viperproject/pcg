/* recurse */
fn other(x: &mut i32, y: i32, z: i32) { *x += y; }
fn main() {
  let mut x = 1;
  let y = 1;
  let z = 1;
  other(&mut x, y, z);
  (x);
}
