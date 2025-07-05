struct T(i32);
struct S {
    x: T,
    y: T,
}
fn main(){

    let mut s = S { x: T(1), y: T(2) };
    let mut t = S { x: T(1), y: T(2) };
    let (r1, r2) = if true {
        (&mut s, &mut t.x)
    } else{
        (&mut t, &mut s.x)
    };
    *r2 = T(4);
}
