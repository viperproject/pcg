fn path_sensitive(b: bool) {
    let mut x = 1;
    let mut y; let mut z;
    //y: &'y mut i64, z: &'z mut i64
    if (b) {
      y = &mut x; z = &mut *y;
    } else {
      z = &mut x; y = &mut *z;
    }
    // PCG: bb3[0] post_main: borrow: y = &mut  x under conditions bb1 -> bb3,
    *y = 1;
    x = 2;
}

fn main(){

}
