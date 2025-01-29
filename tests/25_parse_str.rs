use std::cell::Cell;
use std::marker::PhantomData;
use std::rc::Rc;


type Entry = ();

pub struct Cursor<'a> {
    // The current entry which the `Cursor` is pointing at.
    ptr: *const Entry,
    // This is the only `Entry::End` object which this cursor is allowed to
    // point at. All other `End` objects are skipped over in `Cursor::create`.
    scope: *const Entry,
    // Cursor is covariant in 'a. This field ensures that our pointers are still
    // valid.
    marker: PhantomData<&'a Entry>,
}

type Unexpected = ();
pub type Result<T> = std::result::Result<T, ()>;
type Span = ();

pub struct ParseBuffer<'a> {
    scope: Span,
    // Instead of Cell<Cursor<'a>> so that ParseBuffer<'a> is covariant in 'a.
    // The rest of the code in this module needs to be careful that only a
    // cursor derived from this `cell` is ever assigned to this `cell`.
    //
    // Cell<Cursor<'a>> cannot be covariant in 'a because then we could take a
    // ParseBuffer<'a>, upcast to ParseBuffer<'short> for some lifetime shorter
    // than 'a, and then assign a Cursor<'short> into the Cell.
    //
    // By extension, it would not be safe to expose an API that accepts a
    // Cursor<'a> and trusts that it lives as long as the cursor currently in
    // the cell.
    cell: Cell<Cursor<'static>>,
    marker: PhantomData<Cursor<'a>>,
    unexpected: Cell<Option<Rc<Cell<Unexpected>>>>,
}

pub type ParseStream<'a> = &'a ParseBuffer<'a>;
pub trait Parse: Sized {
    fn parse(input: ParseStream) -> Result<Self>;
}
pub fn parse_str<T: Parse>(s: &str) -> Result<T> {
    Parser::parse_str(T::parse, s)
}

pub trait Parser: Sized {
    type Output;
    fn parse_str(self, s: &str) -> Result<Self::Output>;
}

impl<F, T> Parser for F
where
    F: FnOnce(ParseStream) -> Result<T>,
{
    type Output = T;
    fn parse_str(self, s: &str) -> Result<Self::Output> {
        unimplemented!()
    }
}

fn main(){

}
