// Foo::Y code should be irrelevant

fn main() {
    enum Foo {
        X(i32),
        Y(i32),
    }
    let mut x = Foo::X(1);
    if let Foo::X(z) = &mut x {
        *z += 1;
    }
    if let Foo::Y(z) = &mut x {
        *z += 1;
    }
    if let Foo::X(z) = x {
        z;
    }
}
