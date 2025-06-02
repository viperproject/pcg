struct ByteSource<'a> {
    slice: &'a [u8],
    pos: usize,
}

impl<'a> ByteSource<'a> {
    fn read(&mut self) -> u8 {
        unimplemented!()
    }
}

struct ByteReadHandle<'a, 'b>
where
    'b: 'a,
{
    source: &'a mut ByteSource<'b>,
}

struct ByteUnreadHandle<'a, 'b>
where
    'b: 'a,
{
    source: &'a mut ByteSource<'b>,
}

impl<'a, 'b> ByteUnreadHandle<'a, 'b>
where
    'b: 'a,
{
    #[inline(always)]
    fn new(src: &'a mut ByteSource<'b>) -> ByteUnreadHandle<'a, 'b> {
        ByteUnreadHandle { source: src }
    }
}

impl<'a, 'b> ByteReadHandle<'a, 'b>
where
    'b: 'a,
{
    pub fn read(self) -> (u8, ByteUnreadHandle<'a, 'b>) {
        let byte = self.source.read();
        let handle = ByteUnreadHandle::new(self.source);
        (byte, handle)
    }
}

fn main(){}
