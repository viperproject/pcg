struct List {
    head: u32,
    tail: Option<Box<List>>,
}

impl List {
    fn get_nth_loop(&mut self, n: usize) -> &mut u32 {
        let mut i = 0;
        let mut current = self;
        while i < n {
            // PCG: bb2[0] pre_operands: Loop(bb1) under conditions bb1 -> bb2,
            current = match current.tail {
                Some(ref mut tail) => tail,
                None => unreachable!(),
            };
            i += 1;
        }
        &mut current.head
    }
}

fn main() {}
