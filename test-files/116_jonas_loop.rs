struct List {
    head: i32,
    tail: Option<Box<List>>,
}

fn foo<'a: 'a>(list: &'a mut List) {
    let mut c = &mut list.tail;
    // PCG: bb1[0] pre_operands: Loop(bb1): [(*list).tail] -> [c↓'?8]
    // PCG: bb1[0] post_operands: (*list).head: E
    while let Some(c_tail) = c {
        c = &mut c_tail.tail;
    }
}

fn main(){}
