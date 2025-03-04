struct T {
    val: i32
}

fn identity_use2() {
    let mut t = T { val: 5 };
    assert!(t.val == 5);
    // PCG: bb0[7] pre_operands: Repacks Start: Collapse(_1, _1.0, E)
    let y = &mut t;
}

fn main() {}
