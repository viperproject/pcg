struct X<'a> { a: &'a mut i32 }
fn foo_ref_struct<'a>(x: X<'a>) {
    *x.a = 42; // PCG: bb0[0] pre_main: Weaken *x.a from E to W
}
fn main(){}
