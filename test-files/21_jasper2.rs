struct T {
    f: i64,
    g: i64
}
struct S<'a> {f: &'a mut T, g: &'a mut T}

fn main() {
    // let mut y = T { f: 1, g: 2 };
    // let mut z = T { f: 1, g: 2 };
    // let j = &mut z;
    let mut f: &mut T = &mut T { f: 0, g: 0 };
    let mut k: &mut T = &mut T { f: 0, g: 0 };
    if true {
        k = &mut *f;
    } else {
        f = &mut k;
    }
    // z.f;
    // let _x = f.f;
    // k.f = 2;
    // f.f = 1;
    // y.f = 1;
    // let _k = j.f;
}
