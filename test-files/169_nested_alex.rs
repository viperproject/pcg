fn main() {
    let mut x = 0;
    let mut a = 1;
    // PCG_LIFETIME_DISPLAY: b 0 'inner
    // PCG_LIFETIME_DISPLAY: z 0 'outer
    // PCG_LIFETIME_DISPLAY: z 1 'inner
    let mut b = &mut a;
    let mut z = &mut b;
    *z = &mut x;
    // Note: `a` should be accessible here, but the borrow checker is imprecise
    // (both polonius and NLL)

    // At this point `*b` should be an alias of x
    // **z should also be an alias of x
    let res = **z;
    *b = 5;
}
