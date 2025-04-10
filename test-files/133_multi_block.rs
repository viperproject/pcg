fn f<'a, 'b, 'c>(
    // 'c : 'b : 'a
    x: &'a mut &'b mut &'c mut i32,
    y: &'b mut &'c mut i32,
    z: &'c mut i32,
) {
    // std::mem::swap(**x, *y);
    *y = z;
    *x = y;
}

fn main() {
    let mut a = 1;
    let mut b = 2;
    let mut c = 3;
    let mut ra = &mut a; // &'c mut i32
    let mut rb = &mut b; // &'c mut i32
    let mut rc = &mut c; // &'c mut i32 PCG_LIFETIME_DISPLAY: rc 0 'rc
    let mut rra = &mut ra; // &'b mut &'c mut i32
    let mut rrb = &mut rb; // &'b mut &'c mut i32 PCG_LIFETIME_DISPLAY: rrb 1 'c
    let mut rrra = &mut rra; // &'a mut &'b mut &'c mut i32
    // PCG_LIFETIME_DISPLAY: rrra 1 'b
    // PCG_LIFETIME_DISPLAY: rrra 0 'rrra
    // PCG_LIFETIME_DISPLAY: _11 0 'trrra

    // let trrra = &mut *rrra; // &'a2 mut &'b2 mut &'c2 mut i32
    // let trrb = &mut *rrb;   // &'b3 mut &'c3 mut i32 rrb is inaccessible as long as b3 has not ended
    // let trc = &mut *rc;     // &'c4 mut i32
    f(rrra, rrb, rc);

    // According to the constraint, 'c : 'b : 'a
    // After this call we have <rc↓'c> → <rrb↓'b> → <rrra↓'a>

    // let rrra_lifetimec_after: &mut i32 = &mut ***rrra; // Corresponds to <rrra↓'c>
    // let rrb_lifetimec_after: &mut i32 = &mut **rrb;    // Corresponds to <rrb↓'c>
    // 'a must die here because rrb_lifetimec_after could potentially alias
    // with rrra_lifetimec_after

    // let x = *rrra_lifetimec_after;
    // let y = *rrb_lifetimec_after;

    // // If the order were changed, the program would not compile
    ***rrra = 1; // 'a dies here
    **rrb = 1; // 'b dies here
    *rc = 4; // 'c dies here
             // *rrb = &mut 4;  // Not allowed after *rc because rc|'c -> rrb|'b
    println!("{}", a);
}
