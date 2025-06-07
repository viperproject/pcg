fn main() {
    let mut a = 0;
    let b = (1, &mut a);
    *b.1 += 1;
    // *b.1 should have `R` permission at the point when it's *read* (prior to the addition)
    // ~PCG: bb0[9] post_main: *b.1: E
    let c = b;
    c;
 }
