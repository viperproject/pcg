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
// PCG: bb4[0] post_main: (_4@Some).0 after bb0[5]↓'?6 -> node↓'?8 mid bb4[0] under conditions bb1 -> bb2
// PCG: bb4[0] post_main: Remote(_1)↓'?5 -> self after bb0[0]↓'?5 under conditions bb1 -> bb2
// PCG: bb4[0] post_main: call StringList::<'a>::get_nth at bb0[5]: [_5 after bb0[2]↓'?7 after bb0[4]] -> [_4 after bb0[5]↓'?6 after bb3[0]] under conditions bb1 -> bb2
// PCG: bb4[0] post_main: self after bb0[0]↓'?5 -> _5 after bb0[2]↓'?7 after bb0[4] under conditions bb1 -> bb2
// PCG: bb4[0] post_main: {(_4@Some) after bb0[5]↓'?6 after bb3[0]} -> {(_4@Some).0 after bb0[5]↓'?6} under conditions bb1 -> bb2
// PCG: bb4[0] post_main: {_4 after bb0[5]↓'?6 after bb3[0]} -> {(_4@Some) after bb0[5]↓'?6 after bb3[0]} under conditions bb1 -> bb2
        }
    }
}


fn main() {
}
