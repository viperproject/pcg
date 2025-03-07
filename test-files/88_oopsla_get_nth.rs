struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

impl<T> List<T> {
    fn get_nth(&mut self, n: usize) -> Option<&mut T> {
        if n == 0 {
            Some(&mut self.head)
        } else {
            self.tail.as_mut().and_then(|tail| tail.get_nth(n - 1))
        }
    }
}

fn set_nth(list: &mut List<u32>, n: usize, value: u32) {
    let result = list.get_nth(n);
    // ~PCG: bb0[3] pre_operands: list: E
    if let Some(node) = result {
        *node = value;
    }
}

fn main() {
}
