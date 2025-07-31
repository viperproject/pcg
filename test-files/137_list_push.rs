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
    let mut list: List<&mut i32> = List {
        head: rv1,
        tail: None,
    };
    list.push(rv2);
    // list|'a should not be a placeholder here
    // PCG: bb2[0] post_main: call List::<T>::push at bb1[9]: [_11 before bb1[9]:PostOperands↓'?21 before bb1[9]:PostMain] -> [_11 before bb1[9]:PostOperands↓'?21 after bb1]
// PCG: bb2[0] post_main: call List::<T>::push at bb1[9]: [_12 before bb1[9]:PostOperands↓'?22 before bb1[9]:PostMain] -> [_11 before bb1[9]:PostOperands↓'?21 after bb1]
    // PCG: bb2[0] post_main: _11 before bb1[9]:PostOperands↓'?21 after bb1 -> list↓'?17
    let y = 1;
    list.push(rv3);
}
