use std::ops::Range;

pub struct RangedSlice<'a, T>(&'a [T]);

impl<'a, T> RangedSlice<'a, T> {
    pub fn range(&self) -> Range<&'a T> {
        &self.0[0]..&self.0[self.0.len() - 1]
    }
}

fn main(){}

