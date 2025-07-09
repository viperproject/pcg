struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

fn f<'a>(mut list: List<&'a mut i32>) {
    let mut r1 = &mut 0;
    while let Some(mut tail) = list.tail {
        list = *tail;
        r1 = list.head;
    }
    *r1 = 1;
}

fn main() {}
