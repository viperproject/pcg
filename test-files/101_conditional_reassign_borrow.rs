struct T {}
fn main () {}
fn test(b: bool) {
    let t0 = T {};
    let t1 = T {};
    let mut x = &t0;
    if b {
        // PCG: bb1[0] pre_operands: t0: R
        x = &t1;
    }
    let test_x = x;
}
