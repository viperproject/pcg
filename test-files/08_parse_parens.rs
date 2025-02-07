use std::{cell::Cell, marker::PhantomData, rc::Rc};

type Span = ();
type Result<T> = std::result::Result<T, ()>;
type DelimSpan = ();
type Cursor<'a> = PhantomData<&'a ()>;

pub(crate) enum Unexpected {
    None,
    Some(Span, Delimiter),
    Chain(Rc<Cell<Unexpected>>),
}

struct Paren {
}

pub enum Delimiter {
    /// `( ... )`
    Parenthesis,
    /// `{ ... }`
    Brace,
    /// `[ ... ]`
    Bracket,
    /// `∅ ... ∅`
    ///
    /// An invisible delimiter, that may, for example, appear around tokens
    /// coming from a "macro variable" `$var`. It is important to preserve
    /// operator priorities in cases like `$var * 3` where `$var` is `1 + 2`.
    /// Invisible delimiters may not survive roundtrip of a token stream through
    /// a string.
    ///
    /// <div class="warning">
    ///
    /// Note: rustc currently can ignore the grouping of tokens delimited by `None` in the output
    /// of a proc_macro. Only `None`-delimited groups created by a macro_rules macro in the input
    /// of a proc_macro macro are preserved, and only in very specific circumstances.
    /// Any `None`-delimited groups (re)created by a proc_macro will therefore not preserve
    /// operator priorities as indicated above. The other `Delimiter` variants should be used
    /// instead in this context. This is a rustc bug. For details, see
    /// [rust-lang/rust#67062](https://github.com/rust-lang/rust/issues/67062).
    ///
    /// </div>
    None,
}

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

pub struct Parens<'a> {
    pub token: (),
    pub content: PhantomData<&'a ()>
}

fn parse_delimited<'a>(
    input: &ParseBuffer<'a>,
    delimiter: Delimiter,
) -> Result<(DelimSpan, ParseBuffer<'a>)> {
    unimplemented!()
}

pub fn parse_parens<'a>(input: &ParseBuffer<'a>) -> Result<Parens<'a>> {
    parse_delimited(input, Delimiter::Parenthesis).map(|(span, content)| Parens {
        token: (),
        content: PhantomData,
    })
}

fn main() {
}
