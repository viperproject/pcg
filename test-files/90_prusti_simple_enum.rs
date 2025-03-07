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
