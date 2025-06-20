struct T {}
fn main () {}
fn test(b: bool) {
    let t0 = T {};
    let t1 = T {};
    let mut x = &t0;
    if b {
        x = &t1;
    }
    // PCG: bb3[0] pre_operands: t0: R
    let test_x = x;
}
