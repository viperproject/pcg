pub type ParseResult<S> = Result<S, S>;

#[derive(Debug, Clone, Copy)]
pub struct Position<'i> {
    input: &'i str,
    pos: usize,
}

impl<'i> Position<'i> {
    pub fn skip_until(mut self, strings: &[&str]) -> bool {
        true
    }
}

pub struct ParserState<'i> {
    position: Position<'i>,
}

impl<'i> ParserState<'i> {
    pub fn skip_until(mut self: Box<Self>, strings: &[&str]) -> ParseResult<Box<Self>> {
        self.position.skip_until(strings);
        Ok(self)
    }
}

fn main() {
}
