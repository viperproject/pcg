struct X<'a> { a: &'a mut i32 }
fn foo_ref_struct<'a>(x: X<'a>) {
    *x.a = 42;
}
fn main(){}
