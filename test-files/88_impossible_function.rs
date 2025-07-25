struct T {}
fn f<'b, 'a: 'b>(t: &'b mut T) -> &'a mut T { panic!(); }
fn main() {
    let mut t = T {};
    let u = &mut t;
    let v = f(u);
    /* can use u and v in any order here */
    let test_v = v;
    let test_u = u;
    let test_t = t;
}
