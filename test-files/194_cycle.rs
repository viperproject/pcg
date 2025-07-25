fn main() {
    let mut x = 0;
    let mut ra: &i32;
    let mut rb: &i32;
    if true {
        ra = &x;
        rb = &*ra;
    } else {
        rb = &x;
        ra = &*rb;
    }
    let y = *ra;
    let z = *rb;
}
