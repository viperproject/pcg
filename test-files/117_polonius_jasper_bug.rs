fn path_sensitive(b: bool) {
    let mut x = 1;
    let mut y; let mut z;
    //y: &'y mut i64, z: &'z mut i64
    if (b) {
      y = &mut x; z = &mut *y;
    } else {
      z = &mut x; y = &mut *z;
    }
    // PCG: bb3[0] post_operands: borrow: _7 after bb1[1] = &mut  x under conditions bb0 -> bb1
    // PCG: bb3[0] pre_main: _7 after bb1[1]↓'?10 -> y↓'?8 under conditions bb0 -> bb1
    *y = 1;
    x = 2;
}

fn main(){

}
