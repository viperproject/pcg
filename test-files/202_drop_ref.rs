enum S {
    Left(String),
    Right(String),
}

fn f(mut s: S) {
    let mut x = String::new();
    let mut rx = &mut x;
    let mut y = String::new();
    match s {
        S::Left(mut left) => {
            rx = &mut left;
        }
        S::Right(mut right) => {
            y = right;
        }
    }
    // rx will not survive the branch, it's partially moved
}

fn main() {
    let s = S::Left("Hello".to_string());
}
