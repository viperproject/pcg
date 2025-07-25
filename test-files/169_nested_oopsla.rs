fn main() {
    let mut a = 0;
    let mut b = 1;
    // PCG_LIFETIME_DISPLAY: x 0 'inner
    // PCG_LIFETIME_DISPLAY: y 0 'outer
    // PCG_LIFETIME_DISPLAY: y 1 'inner
    let mut x = &mut a; // x -> a
    let mut y = &mut x; // y -> x -> a
    *y = &mut b; // y -> x -> b
    // Note: `a` should be accessible here, but the borrow checker is imprecise
    // (both polonius and NLL)

    // At this point `**y` should be an alias of b
    // *x is also an alias of b
    *x = 5;
}
