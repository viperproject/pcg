struct BorrowStrList<'a> { head: &'a mut str, tail: Option<Box<BorrowStrList<'a>>> }
fn f<'a>(list: BorrowStrList<'a>) -> &'a mut str {
  return list.head;
}

fn main(){

}
