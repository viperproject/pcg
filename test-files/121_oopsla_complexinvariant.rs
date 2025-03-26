struct List {
    head: u32,
    tail: Option<Box<List>>,
}

impl List {
    fn len(&self) -> usize {
        self.tail.as_ref().map_or(0, |tail| tail.len() + 1)
    }
}

fn f(left_orig: &mut List, right_orig: &mut List) {
    let mut left: &mut List = &mut *left_orig;
    let mut right: &mut List = &mut *right_orig;
    let mut c = None;
    let mut cont = left.len() > 0 && right.len() > 0;
    while cont {
        left = left.tail.as_mut().unwrap();
        right = right.tail.as_mut().unwrap();
        cont = left.len() > 0 && right.len() > 0;
        if left.head < right.head {
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


