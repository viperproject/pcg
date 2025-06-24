fn main() {
    let mut x = 0;
    let mut y = 1;
    let mut z = 2;
    let mut rx = &mut x;
    let mut ry = &mut y;
    let mut rz = &mut z;
    while true {
        ry = &mut (*rx);
        rz = &mut (*ry);
    }
    *rz = 1;
    *ry = 2;
    *rx = 3;
}
