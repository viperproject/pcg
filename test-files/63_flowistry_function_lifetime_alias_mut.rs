fn foo<'a>(x: &'a mut i32, y: &'a i32) {
    let z = x;
    *z = 1;
    *y;
}

  fn main() {}
