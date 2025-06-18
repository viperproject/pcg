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

fn f(mut c: &mut Composite) {
    let b = c.f2.foo();
    let cc = &c.f1;
    // At this point *c.f2 is exclusive, so *c shouldn't have any capabilities
    // ~PCG: bb1[8] pre_operands: *c: R
    mess_with_data(&mut c.f2, b);
    let dd = cc;
    let z = c;
}

fn main(){

}
