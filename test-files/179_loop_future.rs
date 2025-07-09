struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

impl<T> List<T> {
    fn new() -> Self {
        todo!()
    }
    fn push(&mut self, x: T) {
    }
    fn pop(&mut self) -> T {
        todo!()
    }
}

// fn f<'a>(mut ol1: List<&'a mut i32>, mut ol2: List<&'a mut i32>) {
//     let mut l1 = &mut ol1;
//     let mut l2 = &mut ol2;
//     while true {
//         let h = l1.pop();
//         l2.push(h);
//     }
// }

fn main() {
    let mut x = 0;
    let mut l1: List<&mut i32> = List::new(); // PCG_LIFETIME_DISPLAY: l1 0 'a
    let mut l2: List<&mut i32> = List::new(); // PCG_LIFETIME_DISPLAY: l2 0 'a
    let mut rl: &mut List<&mut i32> = &mut l1;
    while true {
        rl = &mut l2;
    }
    rl.push(&mut x);
    // let y = *rl1.pop();
}
