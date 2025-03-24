struct List {
    head: i32,
    tail: Option<Box<List>>,
}

fn walk<'a: 'a>(l: &'a mut List) {
    let mut c = l;
    while let Some(tail) = &mut c.tail {
        // PCG: bb4[6] pre_main: Repacks Middle: Weaken(_2, E, W)
        c = &mut **tail;
    }
}

fn main(){}
