struct List {
    head: i32,
    tail: Option<Box<List>>,
}

fn foo<'a: 'a>(list: &'a mut List) {
    let mut c = &mut list.tail;
    while let Some(c_tail) = c {
        c = &mut c_tail.tail;
    }
}

fn main(){}
