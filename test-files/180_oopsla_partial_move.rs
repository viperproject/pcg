struct StringList { hd: String, tl: Option<Box<StringList>> }
fn take_head(list: StringList) -> String {
    list.hd
// PCG: bb0[0] post_main: RETURN: E
// PCG: bb0[0] post_main: list.hd: W
// PCG: bb0[0] post_main: list.tl: E
}

fn main() {
}
