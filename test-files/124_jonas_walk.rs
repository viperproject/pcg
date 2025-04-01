struct List {
    head: i32,
    tail: Option<Box<List>>,
}

fn walk<'a: 'a>(l: &'a mut List) {
    let mut c = l;
    while let Some(tail) = &mut c.tail {
        // PCG: bb4[6] pre_main: Weaken(_2, E, W)
        c = &mut **tail;
        // ~PCG: bb4[7] pre_main: Weaken(_7, E, W)
    }
}

fn main(){}
