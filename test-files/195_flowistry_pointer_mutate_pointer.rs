fn main() {
    let mut x = 1;
    let mut y = 1;
    let mut a = &mut x;
    let b = &mut a;
    *b = &mut y;
    **b = 2;
    y;
}
