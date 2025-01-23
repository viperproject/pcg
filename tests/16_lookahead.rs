use std::cell::RefCell;

type Span = usize;
type Cursor<'a> = &'a str;

pub struct Lookahead1<'a> {
    scope: Span,
    cursor: Cursor<'a>,
    comparisons: RefCell<Vec<&'static str>>,
}

pub(crate) fn new(scope: Span, cursor: Cursor) -> Lookahead1 {
    Lookahead1 {
        scope,
        cursor,
        comparisons: RefCell::new(Vec::new()),
    }
}
fn main(){

}
