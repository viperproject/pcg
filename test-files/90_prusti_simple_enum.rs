// TODO: Actually this is never tested currently because the span isn't matched :/
// The not expected annotation might erroneously come from the PartialEq impl
// ~PCG: bb5[0] pre_operands: Collapse(_10, _10.0, E)

#[derive(Clone,PartialEq,Eq)]
enum A {
    ANone(u32),
    ASome(i32),
}

fn test(_x: &A, _y: &A) -> i32 {
    17
}

fn main() {
}
