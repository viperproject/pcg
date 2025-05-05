struct List {
    head: u32,
    tail: Option<Box<List>>,
}

fn penultimate_mut<'a>(list: &'a mut List) -> Option<&'a mut u32> {
    let mut current = list;
    let mut prev: Option<&'a mut u32> = None;
    // PCG: bb1[0] post_main: Loop(bb1): [Remote(_1)] -> [current↓'?11, prev↓'?12] under conditions bb1

    while let Some(ref mut tail) = current.tail {
        prev = Some(&mut current.head);
        current = tail;
    }
    prev
}

fn main() {
}
