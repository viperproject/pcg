#[allow(dead_code)]
#[allow(unused_variables)]

struct T0 (u32);

struct T1 {
    f: T0,
    g: u32,
    h: u32,
}

enum T2 {
    E2a(),
    E2b(u32),
    E2c(T1),
    E2d {
        f: T1,
        g: T1,
        h: T1,
    }

}

struct T3 {
    f: T1,
    g: T2,
    h: T2,
}

fn test2(x: T3, y: T2) {
    let mut x = x;
    if let T2::E2c(T1 { f: z, .. }) = x.g {}
// ~PCG: bb4[3] pre_main: Collapse(_3, _3.0, W)
// ~PCG: bb4[3] pre_main: Expand(_3, _3.1, W)
    x.g = y;
}

fn main() {}
