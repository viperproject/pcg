#[derive(Clone, Copy)]
pub struct Position<'i> {
    input: &'i str,
    pos: usize,
}

#[derive(Clone, Copy)]
pub struct Span<'i> {
    input: &'i str,
    start: usize,
    end: usize,
}

pub trait RuleType: Copy {}

pub struct Stack<T: Clone> {
    /// All elements in the stack.
    cache: Vec<T>,
    /// All elements that are in previous snapshots but may not be in the next state.
    /// They will be pushed back to `cache` if the snapshot is restored,
    /// otherwise be dropped if the snapshot is cleared.
    ///
    /// Those elements from a sequence of snapshots are stacked in one [`Vec`], and
    /// `popped.len() == lengths.iter().map(|(len, remained)| len - remained).sum()`
    popped: Vec<T>,
    /// Every element corresponds to a snapshot, and each element has two fields:
    /// - Length of `cache` when corresponding snapshot is taken (AKA `len`).
    /// - Count of elements that come from corresponding snapshot
    ///   and are still in next snapshot or current state (AKA `remained`).
    ///
    /// And `len` is never less than `remained`.
    ///
    /// On restoring, the `cache` can be divided into two parts:
    /// - `0..remained` are untouched since the snapshot is taken.
    ///
    ///   There's nothing to do with those elements. Just let them stay where they are.
    ///
    /// - `remained..cache.len()` are pushed after the snapshot is taken.
    lengths: Vec<(usize, usize)>,
}

pub type ParseResult<S> = std::result::Result<S, S>;

pub struct ParserState<'i, R: RuleType> {
    position: Position<'i>,
    stack: Stack<Span<'i>>,
    _marker: std::marker::PhantomData<R>,
}

impl<'i, R: RuleType> ParserState<'i, R> {
    pub fn stack_match_pop(mut self: Box<Self>) -> ParseResult<Box<Self>> {
        let mut position = self.position;
        let mut result = true;
        while let Some(span) = self.stack.pop() {
            result = position.match_string(span.as_str());
            if !result {
                break;
            }
        }

        if result {
            self.position = position;
            Ok(self)
        } else {
            Err(self)
        }
    }
}

impl<T: Clone> Stack<T> {
    pub fn pop(&mut self) -> Option<T> {
        unimplemented!()
    }
}

impl<'i> Position<'i> {
    pub(crate) fn match_string(&mut self, string: &str) -> bool {
        unimplemented!()
    }
}

impl<'i> Span<'i> {
    pub fn as_str(&self) -> &str {
        unimplemented!()
    }
}

fn main() {
}
