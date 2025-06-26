struct List {
    head: u32,
    tail: Option<Box<List>>,
}

impl List {
    fn len(&self) -> usize {
        1
    }
}

fn f(lhs_in: &mut List, rhs_in: &mut List) {
    let mut lhs = &mut *lhs_in; let mut rhs = &mut *rhs_in;
    let mut c = None; let mut cont = true;
    while cont {
      lhs = lhs.tail.as_mut().unwrap();
      cont = lhs.len() > 0;
      if lhs.head > 0 { c = Some(&mut lhs.tail); }
      else             { c = Some(&mut rhs.tail); }
    }
    *c.unwrap() = None; lhs_in.tail = None;
}

fn main(){

}
