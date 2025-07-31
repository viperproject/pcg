struct List {
    head: u32,
    tail: Option<Box<List>>,
}

impl List {
    fn get_nth_loop(&mut self, n: usize) -> &mut u32 {
        let mut x = 0;
        let y = &mut x;
        let z = &mut *y;
        let mut i = 0;
        let mut current = self;
        while i < n {
            // PCG: bb1[0] post_main: borrow: y <before bb0[8]:PreOperands> = &mut  x
            // PCG: bb1[0] post_main: borrow: z = &mut  *y
            // PCG: bb1[0] post_main: Loop(bb1): [Remote(_1)↓'?13] -> [current↓'?17]
            current = match current.tail {
                Some(ref mut tail) => tail,
                None => unreachable!(),
            };
            i += 1;
        }
        let a = *z;
        &mut current.head
    }
}

fn main() {}
