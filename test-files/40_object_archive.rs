/// The list of members in the archive.
#[derive(Debug, Clone, Copy)]
enum Members<'data> {
    Common { offset: u64, end_offset: u64 },
    AixBig { index: &'data [u32] },
}

pub struct ArchiveMember<'data> {
    name: &'data [u8],
    // May be zero for thin members.
    offset: u64,
    size: u64,
}

pub trait ReadRef<'a>: Clone + Copy {}
/// An iterator over the members of an archive.
#[derive(Debug)]
pub struct ArchiveMemberIterator<'data, R: ReadRef<'data> = &'data [u8]> {
    data: R,
    members: Members<'data>,
    names: &'data [u8],
    thin: bool,
}

mod read {
    pub type Result<T> = std::result::Result<T, ()>;
}

mod archive {
    pub struct AixMemberOffset(u64);
}

impl<'data> ArchiveMember<'data> {
    /// Parse the member header, name, and file data in an archive with the common format.
    ///
    /// This reads the extended name (if any) and adjusts the file size.
    fn parse<R: ReadRef<'data>>(
        data: R,
        offset: &mut u64,
        names: &'data [u8],
        thin: bool,
    ) -> read::Result<Self> {
        unimplemented!()
    }

    fn parse_aixbig_index<R: ReadRef<'data>>(
        data: R,
        index: &u32,
    ) -> read::Result<Self> {
        unimplemented!()
    }
}

impl<'data, R: ReadRef<'data>> Iterator for ArchiveMemberIterator<'data, R> {
    type Item = read::Result<ArchiveMember<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.members {
            Members::AixBig { ref mut index } => match **index {
                [] => None,
                [ref first, ref rest @ ..] => {
                    // *index = rest;
                    let member = ArchiveMember::parse_aixbig_index(self.data, first);
                    // if member.is_err() {
                    //     *index = &[];
                    // }
                    // Some(member)
                    None
                }
            },
            _ => unreachable!()
        }
    }
}

fn main() {}
