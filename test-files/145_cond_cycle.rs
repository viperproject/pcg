fn path_sensitive(b: bool) {
    let mut x = 1;
    let mut y; let mut z;
    //y: &'y mut i64, z: &'z mut i64
    if (b) {
      y = &mut x; z = &mut *y;
    } else {
      z = &mut x; y = &mut *z;
    }
    y = &mut x;
    z = &mut *y;
    x = 2;
}

fn main(){

}
