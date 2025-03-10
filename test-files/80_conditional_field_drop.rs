struct T {}
struct S {f: T, g: T}
fn test(b: bool) {
    let mut s = S {f: T{}, g: T{}};
    if b {
        drop(s.f);
    }
}
fn main(){}
