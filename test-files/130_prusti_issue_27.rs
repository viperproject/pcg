#![feature(box_patterns)]

struct List {
    next: Option<Box<List>>,
}

fn len(head: &List) -> usize {
    // For the FakeRead, the expansion should happen in PreOperands
    // PCG: bb1[0] pre_main: Add Edge: {head} -> {*head} under conditions bb0 -> bb1; for read: true
    // PCG: bb1[0] pre_main: Add Edge: {*head} -> {(*head).next} under conditions bb0 -> bb1; for read: true
    match head.next {
        None => 1,
        Some(box ref tail) => 1,
    }
}

fn main() {}
