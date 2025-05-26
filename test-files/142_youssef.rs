fn foo<'a, 'b, T: 'a, S: 'b>(x: &'a mut T, y: &'b mut S) -> (&'a mut T, &'b mut S) {
    (x, y)
}

fn main() {
    let mut x = 16;
    let mut y = 32;

    let (_foo1, foo2) = foo(&mut x, &mut y);
    foo(&mut x, foo2);
}
