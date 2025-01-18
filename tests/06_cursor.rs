pub(crate) struct Reject;
type PResult<'a, O> = Result<(Cursor<'a>, O), Reject>;
#[derive(Copy, Clone)]
pub(crate) struct Cursor<'a> {
    pub(crate) rest: &'a str,
    pub(crate) off: u32,
}
fn ident_not_raw<'a>(input: Cursor<'a>) -> PResult<&'a str> {
    todo!()
}

fn literal_suffix<'a>(input: Cursor<'a>) -> Cursor<'a> {
    match ident_not_raw(input) {
        Ok((input, _)) => input,
        Err(Reject) => input,
    }
}

fn main() {}
