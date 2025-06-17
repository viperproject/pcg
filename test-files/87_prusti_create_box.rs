fn use_box(v: i32) -> Box<i32> {
    let x = Box::new(v);
    let y = *x;
    // *x should be in the PCG because x is a box type
    // It should NOT return the fields inside the box adt
    // PCG: bb1[3] pre_operands: *x: R
    assert!(v == y);
    let z = Box::new(y);
    assert!(v == *z);
    Box::new(*z)
}

fn main() {}
