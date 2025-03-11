struct T {}
struct S {f: T, g: T}
fn test(b: bool) {
    let mut s = S {f: T{}, g: T{}};
    if b {
        drop(s.f);
        // PCG: bb1[3] post_main: s.g: E
        // PCG: bb1[3] post_main: s.f: W
    }
}
fn main(){}
