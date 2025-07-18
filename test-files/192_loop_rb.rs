struct List<T> {
    head: T,
    tail: Node<T>,
}

impl<T> List<T> {
    fn len(&self) -> usize {
        let mut current = self;
        let mut len = 0;
        while let Some(ref next) = &current.tail {
            len += 1;
            current = next;
        }
        len
    }
}

pub type Node<T> = Option<Box<List<T>>>;

fn loop_rb(a_in: &mut List<i32>, b_in: &mut List<i32>) {
    let mut a = &mut *a_in;
    let b = &mut *b_in;
    let mut x = None;
    let mut cont = true;
    // The borrow of `b` survives the loop.
    // PCG: bb1[0] post_main: borrow: b <loop bb1> = &mut  *b_in
    while cont {
        a = a.tail.as_mut().unwrap();
        cont = a.len() > 0;
        if a.head > 0 {
            x = Some(&mut a.tail);
        } else {
            x = Some(&mut b.tail);
        }
    }
    *x.unwrap() = None;
    a_in.tail = None;
}
fn main(){}
