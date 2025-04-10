struct Point {
    x: u32,
    y: u32,
}


fn shift_end(tuple: (Point, Point)) {
    let x = tuple.0.x;
    // ~PCG: bb0[1] pre_operands: Collapse(_1, _1.0, R)
}

fn main(){}
