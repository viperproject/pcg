struct List {
    head: i32,
    tail: Option<Box<List>>,
}

fn foo<'a: 'a>(l: &'a mut List) {
    let mut c = &mut l.tail;
    while let Some(tail) = c {
        c = &mut tail.tail;
    }
}

fn main(){}
