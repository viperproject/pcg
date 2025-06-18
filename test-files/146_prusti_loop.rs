// compile-flags: -Punsafe_core_proof=true
fn main(){}

struct WrapperIterator<'a, T>{
    iter_mut: std::slice::IterMut<'a, T>,
}
impl<'a, T> WrapperIterator<'a, T> {
    fn new(x: &'a mut Vec<T>) -> Self {
        WrapperIterator {
            iter_mut: x.iter_mut(),
        }
    }
}
impl<'a, T> Iterator for WrapperIterator<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut.next()
    }
}
fn test2() {
    let mut ve = Vec::new();
    let mut v: WrapperIterator<i32> = WrapperIterator::new(&mut ve);
    let mut n = 4;
    let mut s = &mut n;
    assert!(*s == 4);
    for x in &mut v {
        s = x;
    }
    *s = 4;
    assert!(*s == 4);
}
