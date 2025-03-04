struct S {
    a: i32,
    b: i32,
}

fn f(x: Result<Option<usize>, ()>) {
    if let Ok(s@Some(y)) = x {
        let r = &s;
        let d = *r;
    }
}

fn main() {
    let x = S { a: 1, b: 2 };
    let y = &x.a;
    // PCG: bb0[4] post_main: x.b: E
    // PCG: bb0[4] post_main: x.a: R
    // PCG: bb0[4] post_main: x: R
    // ~PCG: bb0[4] post_operands: Repacks Start: Collapse(_1, _1.0, R)
    let z = &x;

    let a = z.b;
    let b = *y;
}
