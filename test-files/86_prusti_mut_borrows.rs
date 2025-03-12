// This test fails if the expansion edge y -> *y does not block borrow edge y = &mut a.f.

struct T {
    f: u32,
}

struct U {
    f: u32,
    g: u32,
}

pub fn test6() {
    let mut a = U { f: 6, g: 1 };
    let y = &mut a.f;
    let z = &mut a.g;
    *y = 7;
    let y2 = &mut *y;
    let z2 = &mut *z;
    *y2 = 3;
    // PCG: bb0[17] pre_operands: a.f: E
    *z2 = 4;
    assert!(a.f == 3);
    assert!(a.g == 4);
}

fn main() {}
