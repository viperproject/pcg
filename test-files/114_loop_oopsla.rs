struct List {
    head: u32,
    tail: Option<Box<List>>,
}

fn penultimate_mut<'a>(list: &'a mut List) -> Option<&'a mut u32> {
    let mut current: &'a mut List = list;
    let mut prev: Option<&'a mut u32> = None;
// PCG: bb2[0] pre_operands: Loop(bb1): [list↓'?11 after bb0[1]] -> [prev↓'?13] under conditions bb1 -> bb2,

    while let Some(ref mut tail) = current.tail {
        prev = Some(&mut current.head);
        current = tail;
    }
    prev
}

fn main() {
}
