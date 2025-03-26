struct List { head: String, tail: Option<Box<List>> }
fn borrow_last<'b, 'a: 'b>(list: &'a mut List) -> &'b mut String {
  let mut current: &'a mut List = &mut *list;
  let mut acc: &'b mut String = &mut current.head;
  while let Some(ref mut tail) = current.tail {
    current = tail; acc = &mut current.head;
  }
  acc
}

fn main(){

}
