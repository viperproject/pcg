fn basic<'l, 's>(num: &'l mut i32) -> &'s mut i32
where 'l: 's
{
    &mut *num
}

fn basic_user() {
    let mut x = 42;
    let y = basic(&mut x);
    // PCG: bb0[8] post_main: Add Abstraction Edge: FunctionCall(DefId(0:3 ~ 58_aurel_pledge[d8c8]::basic), ['?4, '?5]); path conditions: bb0
    *y = 72;
    // PCG: bb1[4] pre_operands: Remove Edge FunctionCall(DefId(0:3 ~ 58_aurel_pledge[d8c8]::basic), ['?4, '?5]) under conditions bb0 -> bb1,
    drop(x);
}

fn main(){}
