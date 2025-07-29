fn main() {
    let mut a = 0;
    let mut b = 1;
    let mut x = &mut a;
    let mut y = &mut x;
    *y = &mut b;
    *x = 5;
}
