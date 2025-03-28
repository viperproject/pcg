fn main() {
    let x = 1;
    let mut y = &x;
    let z = &*y;
    y = &4;
    let zz = *z;
}
