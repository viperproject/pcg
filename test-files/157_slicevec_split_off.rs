pub struct SliceVec<'s, T> {
    data: &'s mut [T],
    len: usize,
  }


  impl<'s, T> Default for SliceVec<'s, T> {
    fn default() -> Self {
        Self {
            data: &mut [],
            len: 0,
        }
    }
  }

  impl<'s, T> SliceVec<'s, T> {

  pub fn split_off<'a>(&'a mut self, at: usize) -> SliceVec<'s, T> {
    let mut new = Self::default();
    let backing: &'s mut [T] = core::mem::take(&mut self.data);
    let (me, other) = backing.split_at_mut(at);
    new.len = self.len - at;
    new.data = other;
    self.len = me.len();
      self.data = me;
      new
  }

}

fn main(){}
