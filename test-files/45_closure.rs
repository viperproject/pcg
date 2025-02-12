pub fn helper<'a, 'b, T>(_: &'a &'b (), v: &'b T) -> &'a T {
    v
}

pub fn make_static<'a, T: 'static>(input: &'a T) {
    let f: for<'b> fn(&'static &'static (), &'b T) -> &'static T = helper;
    // f(&&(), input)
}

fn main(){

}
