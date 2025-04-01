struct S {
    a: i32,
    b: i32,
}

fn main() {
    let x = S { a: 1, b: 2 };
    let y = &x.a;
    // x.b should have R, because `x` has r. It should not be possible to
    // have R to x and E for one of its fields.
    // PCG: bb0[4] post_main: x.b: R
    // PCG: bb0[4] post_main: x.a: R
    // PCG: bb0[4] post_main: x: R
    // ~PCG: bb0[4] pre_operands: Collapse(_1, _1.0, R)
    let z = &x;

    let a = z.b;
    let b = *y;
}
