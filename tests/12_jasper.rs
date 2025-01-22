fn use_of_moved_value<T>(x: T) {
    let y = x;
    // x;
}

fn cannot_be_used_because_it_is_borrowed() {
    let mut x = 1;
    let y = &mut x;
    // x = 2;
    // x;
    *y = 1;
}

fn cannot_borrow_as_mutable_more_than_once() {
    let mut x = 1;
    let x_ref_0 = &mut x;
    // let x_ref_1 = &mut x;
    *x_ref_0 = 1;
}

fn cannot_borrow_as_immutable_because_mutabl() {
    let mut x = 1;
    let x_ref_0 = &mut x;
    // let x_ref_1 = &x;
    *x_ref_0 = 1;
}

fn cannot_borrow_as_mutable_because_immutable() {
    let mut x = 1;
    let x_ref_0 = &x;
    // let x_ref_1 = &mut x;
    *x_ref_0;
}

fn immutable_borrows() {
    let x = 1;
    let y = &x;
    let z = &x;
    y + z;
}

fn use_of_partially_moved_value<T>(t: &mut T) {
    struct S<T>{f: T}
    let s = S { f: t };
    let f_move = s.f;
    // s;
    // let _ = &mut s;
}

// fn lifetimes<'a, 'b : 'a, T>(x: &'a mut T, y: &'b mut T) {
//     x;
//     y;
// }

// error message: cannot assign bc borrowed
fn abstraction_edge(x: &mut i64) {
    fn abstraction<'a>(t: &'a mut i64) -> &'a mut i64 { t }
    let y = abstraction(x);
    // x;
    // let mut _ = &mut x;
    // let _ = &x;
    let _ = &y;
}

fn cycle() {
    enum E<'a> {
        Empty(),
        Bar(),
        NonEmpty(&'a E<'a>)
    }
    let mut node_1 = E::Empty();
    let node_2 = E::NonEmpty(&node_1);
    let foo = Box::new(1);
    // node_1 = E::NonEmpty(&node_2);
    node_2;
}

fn main() {}
