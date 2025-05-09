struct T {}
fn main () {}
fn test(b: bool) {
    let mut t = T {};
    let mut x : &mut T = &mut t;
    let y : &mut (&mut T) = &mut x;
    let test_y = y;
    let test_x = x;
    let test_t = t;
}
