struct T<'a> {
    a: &'a mut i32,
}
struct S<'a> {
    x: T<'a>,
    y: T<'a>,
}

fn f<'a>(s: S<'a>) {
    let x = s.x; // PCG: bb0[1] pre_operands: _1.1: E
                 // PCG: bb0[1] pre_operands: _1.1↓'?6: E
    let y = s.y.a;

}

fn main() {}
