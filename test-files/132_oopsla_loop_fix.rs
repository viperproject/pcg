struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

impl<T> List<T> {
    fn push(&mut self, value: T) {
    }
}


fn main() {
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut rv1 = &mut v1;
    let mut rv2 = &mut v2;
    let mut rv3 = &mut v3;
    let mut list1 = List { head: rv1, tail: None};
    let mut list2 = List { head: rv2, tail: None};
    let mut list3 = List { head: rv3, tail: None};
    while true {
        let h1 = list1.head;
        let h2 = list2.head;
        list1 = *list1.tail.unwrap();
        list2 = *list2.tail.unwrap();
        list2.push(h1);
        list3.push(h2);
    }


}
