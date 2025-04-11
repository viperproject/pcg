fn f<'a, 'b, 'c>(
    // 'c : 'b : 'a
    x: &'a mut &'b mut &'c mut i32,
    y: &'b mut &'c mut i32,
    z: &'c mut i32,
) {
    // std::mem::swap(**x, *y);
    *y = z;
    *x = y;

    // PCG_LIFETIME_DISPLAY: x 0 'a
    // PCG_LIFETIME_DISPLAY: y 0 'b
    // PCG_LIFETIME_DISPLAY: z 0 'c
}

fn main() {
    let mut a = 1;
    let mut b = 2;
    let mut c = 3;
    let mut ra = &mut a; // &'c mut i32
    let mut rb = &mut b; // &'c mut i32
    let mut rc = &mut c; // &'c mut i32
    let mut rra = &mut ra; // &'b mut &'c mut i32
    let mut rrb = &mut rb; // &'b mut &'c mut i32
    let mut rrra = &mut rra; // &'a mut &'b mut &'c mut i32


    // let trrra = &mut *rrra;
    // let trrb = &mut *rrb;
    // let trc = &mut *rc;
    f(rrra, rrb, rc);


    // If the order were changed, the program would not compile
    ***rrra = 1; // 'a dies here
    **rrb = 1; // 'b dies here
    *rc = 4; // 'c dies here

    // PCG_LIFETIME_DISPLAY: rc 0 'rc
    // PCG_LIFETIME_DISPLAY: rrb 1 'c
    // PCG_LIFETIME_DISPLAY: rrra 1 'b
    // PCG_LIFETIME_DISPLAY: rrra 0 'rrra
    // PCG_LIFETIME_DISPLAY: _11 0 'trrra
}
