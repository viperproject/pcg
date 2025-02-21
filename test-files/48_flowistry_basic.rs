fn main() {
    fn foo<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32 { x }

    let a = 1;
    let b = 2;
    let c = &a;
    let d = &b;
    let e = foo(c, d);
  }
