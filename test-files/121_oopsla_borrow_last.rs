struct List {
    head: u32,
    tail: Option<Box<List>>,
}

fn f(left_orig: &mut List, right_orig: &mut List) {
    let mut left: &mut List = &mut *left_orig;
    let mut right: &mut List = &mut *right_orig;
    let mut c = None;
    while true {
        left = left.tail.as_mut().unwrap();
        right = right.tail.as_mut().unwrap();
        if true {
            c = Some(&mut left.tail);
        } else {
            c = Some(&mut right.tail);
        }
    }
    *c.unwrap() = None;
    left_orig.tail = None;
}

fn main() {
}


