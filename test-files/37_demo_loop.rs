struct List {
    head: u32,
    tail: Option<Box<List>>,
}

impl List {
    fn get_nth_loop(&mut self, n: usize) -> &mut u32 {
        let mut i = 0;
        let mut current = self;
        while i < n {
// PCG: Terminator(bb1): Extra Start: Add Abstraction Edge: Loop(bb1): [Remote(_1)] -> [current↓'?13]; path conditions: bb1
// ~PCG: bb1[0] pre_operands: (*_12) at After(bb7[2]) -> current↓'?13 under conditions bb7 -> bb8,bb8 -> bb1,
// PCG: bb1[0] pre_operands: Loop(bb1): [Remote(_1)] -> [current↓'?13] under conditions bb1
// PCG: bb1[0] pre_operands: Loop(bb1): [Remote(_1)↓'?11] -> [current↓'?13] under conditions bb1
// PCG: bb2[0] pre_operands: Loop(bb1): [Remote(_1)] -> [current↓'?13] under conditions bb1 -> bb2,
// PCG: bb2[0] pre_operands: Loop(bb1): [Remote(_1)↓'?11] -> [current↓'?13] under conditions bb1 -> bb2,
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
