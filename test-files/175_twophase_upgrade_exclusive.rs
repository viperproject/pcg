struct Data(i32);
struct Composite {
    f1: Data,
    f2: Data,
    f3: Data
}

impl Data {
    fn foo(&self) -> i32 {
        self.0
    }
}

impl Composite {
    fn foo(&self) -> i32 {
        self.f1.0
    }
}

fn mess_with_data(data: &mut Data, baz: i32) {
    unimplemented!()
}

fn f(mut c: Composite) {
    let baz = &mut c.f1;
    let b = c.f2.foo();
    // `c.f2` should be E by now
    // ~PCG: bb1[1] pre_main: c.f2: R
    mess_with_data(baz, b);
    // `c` should be packed, E by now
    // ~PCG: bb2[2] pre_main: c.f2: R
    let t = c;
}

fn main(){

}
