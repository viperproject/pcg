struct List {
    head: i32,
    tail: Option<Box<List>>,
}

fn foo<'a: 'a>(list: &'a mut List) {
    // PCG: bb0[3] pre_operands: Remove Edge {*list} -> {(*list).head, (*list).tail} under conditions bb0
    let mut l = &mut list.tail;
}

fn main() {
}
