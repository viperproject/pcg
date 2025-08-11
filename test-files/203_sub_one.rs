fn sub_one(x: &mut i32) {
    if *x > 0 {
        *x -= 1
    }
}

fn client() -> i32 {
    let mut x = &mut 10;
    // *x = 9;
    sub_one(x);
    *x
}

fn main() {}
