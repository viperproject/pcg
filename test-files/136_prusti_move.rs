fn go(mut t0: u32) {
    // PCG: bb0[4] post_main: Add Edge: x after bb0[1]↓'?4 -> tmp↓'?5; for read: false
    let mut x = &mut t0;
    let tmp = x;
    *tmp = 0;
    assert!(t0 == 0);
}

fn main() {}
