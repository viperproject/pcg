fn f(mut x: i32, mut y: i32, mut z: i32) {
    let r = if x > y {
        // PCG: bb1[2] post_main: borrow: r = &mut  x under conditions bb0 -> bb1
        &mut x
    } else {
        // PCG: bb2[3] post_main: borrow: _8 = &mut  y under conditions bb0 -> bb2
        &mut y
    };

    let s = if z > 5 {
        &mut *r
    } else {
        // PCG: bb5[1] pre_operands: r: W
        &mut z
    };

    *s = 5;
}
// PCG_LIFETIME_DISPLAY: r 0 'r

fn main(){

}

