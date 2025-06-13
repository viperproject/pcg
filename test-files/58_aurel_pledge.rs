fn basic<'l, 's>(num: &'l mut i32) -> &'s mut i32
where
    'l: 's,
{
    &mut *num
}

fn basic_user() {
    let mut x = 42;
    let y = basic(&mut x);
    // PCG: bb0[8] post_main: call basic at bb0[8]: [_3 after bb0[7]↓'?7] -> [y↓'?6]
    *y = 72;
    // PCG: bb1[4] pre_operands: Remove Edge call basic at bb0[8]: [_3 after bb0[7]↓'?7] -> [y↓'?6 mid bb1[3]]
    drop(x);
}

fn main() {}
