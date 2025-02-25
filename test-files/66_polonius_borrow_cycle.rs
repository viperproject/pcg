fn main() {
    let mut a: &mut i32;
    let mut b: &mut i32;
    let c = true;
    let mut y = 1;

    if c {
        a = &mut y;
        b = &mut *a;
    } else {
        b = &mut y;
        a = &mut *b;
    }
    let x = *a;
}
