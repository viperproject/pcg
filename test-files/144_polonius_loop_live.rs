fn main() {
    let mut x = 0;
    let mut y = 1;
    let mut r1 = &mut x;
    let mut r2 = &mut *r1;
    let c = false;
    while true {
        if c {
            r1 = &mut y;
            r2 = &mut *r1;
        } else {
            r2 = &mut y;
            r1 = &mut *r2;
        }
    }
    let z = *r2;
}
