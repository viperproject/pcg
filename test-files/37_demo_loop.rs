struct List {
    head: u32,
    tail: Option<Box<List>>,
}

impl List {
    fn get_nth_loop(&mut self, n: usize) -> &mut u32 {
        let mut i = 0;
        let mut current = self;
        while i < n {
// PCG: Terminator(bb1): Add Edge: Loop(bb1): [Remote(_1)] -> [current↓'?13]
// ~PCG: bb1[0] pre_operands: (*_12) at After(bb7[2]) -> current↓'?13
// PCG: bb1[0] pre_operands: Loop(bb1): [Remote(_1)] -> [current↓'?13]
// PCG: bb1[0] pre_operands: Loop(bb1): [Remote(_1)↓'?11] -> [current↓'?13]
// PCG: bb2[0] pre_operands: Loop(bb1): [Remote(_1)] -> [current↓'?13]
// PCG: bb2[0] pre_operands: Loop(bb1): [Remote(_1)↓'?11] -> [current↓'?13]
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
