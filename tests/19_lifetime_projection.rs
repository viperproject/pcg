struct T<'a> {
    a: &'a mut i32,
}
struct S<'a> {
    x: T<'a>,
    y: T<'a>,
}

fn f<'a>(s: S<'a>) {
    let x = s.x; // PCG: (s|'6: 0)
    let y = s.y.a;
}

fn main() {}
