struct S<'a> {
    x: &'a mut i32,
}

fn g<'a, 'b>(s: &'a mut S<'b>) {}

fn f<'a, 'b>(s: &'a mut S<'b>) {
    // The lifetime projection should be labelled at this point
    // ~PCG: bb0[2] post_operands: Remote(_1)↓'?5 -> s↓'?5
    g(s);
}

fn main() {}
