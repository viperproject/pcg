enum StringList<'a> {
    Cons(&'a mut String, Box<StringList<'a>>),
    Nil,
}

impl <'a> StringList<'a> {
    fn get_nth(self, n: usize) -> Option<&'a mut String> {
        match self {
            StringList::Cons(head, tail) => {
                if n == 0 {
                    Some(head)
                } else {
                    tail.get_nth(n - 1)
                }
            }
            StringList::Nil => None,
        }
    }
}

fn set_nth<'a>(list: StringList<'a>, n: usize, value: String) {
    if let Some(node) = list.get_nth(n) {
        *node = value;
    }
}

fn main() {
}
