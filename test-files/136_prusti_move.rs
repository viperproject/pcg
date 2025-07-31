fn go(mut t0: u32) {
    // PCG: bb0[4] post_main: Add Edge: x before bb0[4]:PostOperands↓'?4 -> tmp↓'?5
    let mut x = &mut t0;
    let tmp = x;
    *tmp = 0;
    assert!(t0 == 0);
}

fn main() {}
