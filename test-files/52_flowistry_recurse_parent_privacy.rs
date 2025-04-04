/* recurse */
mod bar {
    pub fn whee(f: &mut super::foo::Foo) {
      super::foo::ok(f);
    }
  }

  mod foo {
    pub struct Foo(i32);
    pub fn new() -> Foo { Foo(0) }
    pub fn ok(f: &mut Foo) { f.0 = 1; }
    pub fn test() {
      let mut f = Foo(0);
      super::bar::whee(&mut f);
      f;
    }
  }

  fn main() {}
