struct List { head: String, tail: Option<Box<List>> }
fn borrow_last<'b, 'a: 'b>(list: &'a mut List) -> &'b mut String {
  let mut current: &'a mut List = &mut *list;
  let mut acc: &'b mut String = &mut current.head;
  // We only have permission to current.tail at the loop head
  // PCG: bb1[0] pre_main: (*current).tail: E
  while let Some(ref mut tail) = current.tail {
    current = tail; acc = &mut current.head;
  }
  acc
}

fn main(){

}
