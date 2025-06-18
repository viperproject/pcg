use std::fmt::{Debug, Formatter};

pub type FmtResult = std::result::Result<(), std::fmt::Error>;

pub struct Error;

pub enum Either<L, R> {
    /// A value of type `L`.
    Left(L),
    /// A value of type `R`.
    Right(R),
}

pub struct ExactlyOneError<I>
where
    I: Iterator,
{
    first_two: Option<Either<[I::Item; 2], I::Item>>,
    inner: I,
}

impl<I> Debug for ExactlyOneError<I>
where
    I: Iterator + Debug,
    I::Item: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let mut dbg = f.debug_struct("ExactlyOneError");
        match &self.first_two {
            Some(Either::Left([first, second])) => {
                dbg.field("first", first).field("second", second);
            }
            Some(Either::Right(second)) => {
                dbg.field("second", second);
            }
            None => {}
        }
        dbg.field("inner", &self.inner).finish()
    }
}


fn main() {}
