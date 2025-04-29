struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

impl<T> List<T> {
    fn push(&mut self, value: T) {}
}

fn main() {
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut rv1 = &mut v1;
    let mut rv2 = &mut v2;
    let mut rv3 = &mut v3;
    let mut list = List {
        head: rv1,
        tail: None,
    };
    list.push(rv2);
    // list|'a should not be a placeholder here
    // PCG: bb2[0] post_main: call List::<T>::push at bb1[8]: [_11 after bb1[5]↓'?20 after bb1[7], _12 after bb1[7]↓'?21] -> [list↓'?16] under conditions bb1 -> bb2,
    let y = 1;
    list.push(rv3);
}
