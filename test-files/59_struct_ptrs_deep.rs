struct A(i32);
struct B<'a>(&'a A);
struct C<'a, 'b>(&'b B<'a>);
struct D<'a, 'b, 'c>(&'c C<'a, 'b>);

fn foo() {
    let x = D(&C(&B(&A(0))));
    let y = x.0 .0 .0 .0 + 1;
}

fn main() {
    foo();
}
