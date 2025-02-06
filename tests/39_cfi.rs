trait Reader {
    /// The type used for offsets and lengths.
    type Offset;
    fn is_empty(&self) -> bool;
    fn empty(&mut self);
}

trait UnwindSection<R> {
}

pub struct CommonInformationEntry<R, Offset = <R as Reader>::Offset>
where
    R: Reader<Offset = Offset>,
{
    offset: Offset,
    length: u32,
    version: u8,
    augmentation: &'static str,
    code_alignment_factor: u32,
    initial_instructions: R,
}

struct BaseAddresses;
pub enum CieOrFde<'bases, Section, R>
where
    R: Reader,
    Section: UnwindSection<R>,
{
    /// This CFI entry is a `CommonInformationEntry`.
    Cie(CommonInformationEntry<R>),
    /// This CFI entry is a `FrameDescriptionEntry`, however fully parsing it
    /// requires parsing its CIE first, so it is left in a partially parsed
    /// state.
    Fde(PartialFrameDescriptionEntry<'bases, Section, R>),
}

pub struct PartialFrameDescriptionEntry<'bases, Section, R>
where
    R: Reader,
    Section: UnwindSection<R>,
{
    offset: R::Offset,
    length: R::Offset,
    // format: Format,
    // cie_offset: Section::Offset,
    rest: R,
    section: Section,
    bases: &'bases BaseAddresses,
}

type Result<T> = std::result::Result<T, ()>;

pub struct CfiEntriesIter<'bases, Section, R>
where
    R: Reader,
{
    section: Section,
    bases: &'bases BaseAddresses,
    input: R,
}

impl<'bases, Section, R> CfiEntriesIter<'bases, Section, R>
where
    R: Reader,
    Section: UnwindSection<R>,
{
    /// Advance the iterator to the next entry.
    pub fn next(&mut self) -> Result<Option<CieOrFde<'bases, Section, R>>> {
        match parse_cfi_entry(self.bases, &self.section, &mut self.input) {
            Err(e) => {
                self.input.empty();
                Err(e)
            }
            _ => Ok(None)
        }
    }
}

fn parse_cfi_entry<'bases, Section, R>(
    bases: &'bases BaseAddresses,
    section: &Section,
    input: &mut R,
) -> Result<Option<CieOrFde<'bases, Section, R>>>
where
    R: Reader,
    Section: UnwindSection<R>,
{
    unimplemented!()
}

fn main(){}
