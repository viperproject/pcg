fn main() {
    let mut one = 2; let mut two = 2;

    let mut y = &mut one;
    let z = &mut (*y);
    y = &mut two;

    *z = 4;
}
