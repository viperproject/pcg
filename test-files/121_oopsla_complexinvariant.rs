struct List {
    head: u32,
    tail: Option<Box<List>>,
}

impl List {
    fn len(&self) -> usize {
        self.tail.as_ref().map_or(0, |tail| tail.len() + 1)
    }
}

fn f(left_in: &mut List, right_in: &mut List) {
    let mut left: &mut List = &mut *left_in;
    let mut right: &mut List = &mut *right_in;
    let mut c = None; let mut cont = true;
    while cont {
      left = left.tail.as_mut().unwrap();
      cont = left.len() > 0;
      if left.head > 0 { c = Some(&mut left.tail); }
      else             { c = Some(&mut right.tail); }
    }
    *c.unwrap() = None; left_in.tail = None;
}

fn main() {
}


