fn main() {
    struct Foo<'a>(&'a mut i32);
    let mut x = 1;
    let f = Foo(&mut x);
    *f.0 += 1;
    x;
}
