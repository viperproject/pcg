struct U32Pair<'a>(&'a mut u32, &'a mut u32);

fn main() {
    let mut x = 0;
    let mut y = 1;
    let mut rx = &mut x;
    let mut ry = &mut y;
    let pair = U32Pair(rx, ry);
    // PCG: bb0[17] post_main: _6 after bb0[14]↓'?10 -> pair↓'?9
    // PCG: bb0[17] post_main: _7 after bb0[16]↓'?11 -> pair↓'?9
}
