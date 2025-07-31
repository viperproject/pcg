struct U32Pair<'a>(&'a mut u32, &'a mut u32);

fn main() {
    let mut x = 0;
    let mut y = 1;
    let mut rx = &mut x;
    let mut ry = &mut y;
    let pair = U32Pair(rx, ry);
    // PCG: bb0[17] pre_main: borrow: _6 before bb0[17]:PostOperands = &mut  *rx
    // PCG: bb0[17] pre_main: borrow: _7 before bb0[17]:PostOperands = &mut  *ry
    // PCG: bb0[17] post_main: Add Edge: _6 before bb0[17]:PostOperands↓'?10 -> pair↓'?9
    // PCG: bb0[17] post_main: Add Edge: _7 before bb0[17]:PostOperands↓'?11 -> pair↓'?9
}
