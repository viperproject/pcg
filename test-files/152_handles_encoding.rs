pub struct ByteDestination<'a> {
    slice: &'a mut [u8],
    pos: usize,
}

impl<'a> ByteDestination<'a> {
    fn write_three(&mut self, first: u8, second: u8, third: u8) {}
    fn written(&self) -> usize {
        self.pos
    }
}

pub struct ByteThreeHandle<'a, 'b>
{
    dest: &'a mut ByteDestination<'b>,
}

impl<'a, 'b> ByteThreeHandle<'a, 'b>
{
    pub fn write_three_return_written(self, first: u8, second: u8, third: u8) -> usize {
        self.dest.write_three(first, second, third);
        self.dest.written()
    }
}

fn main(){}
