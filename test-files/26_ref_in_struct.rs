struct S<'a> {
    x: &'a mut i32,
    y: &'a mut i32,
}

fn main() {
    let mut x = 1;
    let mut y = 2;
    let s = S { x: &mut x, y: &mut y };
    let rx = s.x;
    *rx = 1;
}
