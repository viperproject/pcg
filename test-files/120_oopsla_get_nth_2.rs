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
    fn set_nth(self, n: usize, value: String) {
        if let Some(node) = self.get_nth(n) {
            *node = value;
// PCG: bb4[0] post_main: (_4@Some).0 before bb3[1]:PostOperands↓'?6 -> node↓'?8 before bb4[0]:PreMain under conditions bb1 -> bb2
// PCG: bb4[0] post_main: Remote(_1)↓'?5 -> self before bb0[2]:PostOperands↓'?5 under conditions bb1 -> bb2
// PCG: bb4[0] post_main: call StringList::<'a>::get_nth at bb0[5]: [_5 before bb0[5]:PostOperands↓'?7 before bb0[5]:PostMain] -> [_4 before bb3[1]:PostOperands↓'?6 before bb3[1]:PreOperands] under conditions bb1 -> bb2
// PCG: bb4[0] post_main: self before bb0[2]:PostOperands↓'?5 -> _5 before bb0[5]:PostOperands↓'?7 before bb0[5]:PostMain under conditions bb1 -> bb2
// PCG: bb4[0] post_main: {(_4@Some) before bb3[1]:PostOperands↓'?6 before bb3[1]:PreOperands} -> {(_4@Some).0 before bb3[1]:PostOperands↓'?6} under conditions bb1 -> bb2
// PCG: bb4[0] post_main: {_4 before bb3[1]:PostOperands↓'?6 before bb3[1]:PreOperands} -> {(_4@Some) before bb3[1]:PostOperands↓'?6 before bb3[1]:PreOperands} under conditions bb1 -> bb2
        }
    }
}


fn main() {
}
