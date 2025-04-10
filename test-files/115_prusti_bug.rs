struct List {
    head: i32,
    tail: Option<Box<List>>,
}

fn foo<'a: 'a>(l: &'a mut List) {
    // PCG: bb0[3] pre_operands: Remove Edge {*l} -> {(*l).head, (*l).tail} under conditions bb0
    let mut l = &mut l.tail;
}

fn main() {
}
