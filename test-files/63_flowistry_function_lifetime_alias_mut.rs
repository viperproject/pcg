fn foo<'a>(x: &'a mut i32, y: &'a i32) {
    let z = x;
    *z = 1;
    *y;
    // We're expanding just to read, so *y should be R instead of E
    // PCG: bb0[5] post_main: *y: R
}

  fn main() {}
