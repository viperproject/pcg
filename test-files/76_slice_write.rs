fn main() {
    let mut x = [0u8; 2];
    let y = &mut x[..1];
    y[0] = 0;
    x;
}
