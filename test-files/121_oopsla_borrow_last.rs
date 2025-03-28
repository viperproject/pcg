struct Tree {
    value: i32,
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

fn f<'a>(left: &'a mut Tree, right: &'a mut Tree) {
    let lhs = &mut *left;
    let rhs = &mut *right;
    let mut ptr = match lhs.left {
        Some(ref mut left) => &mut **left,
        None => return,
    };
    let mut fallback = match rhs.left {
        Some(ref mut left) => &mut **left,
        None => return,
    };

    while lhs.right.is_some() {
        ptr = rhs;
        match ptr.right {
            Some(ref mut right) => fallback = &mut **right,
            None => return,
        }
    }
    fallback.value = 1;
    ptr.value = 2;
    lhs.value = 3;
    rhs.value = 4;
}

fn main() {
}


