struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

impl<T> List<T> {
    fn push(&mut self, value: T) {}
}

fn main() {
    let mut v1 = 1;
    let mut rv1 = &mut v1;
    let mut list = List {
        head: rv1,
        tail: None,
    };
    let hd = list.head;
    let tl = list.tail;
}
