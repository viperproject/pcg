use std::marker::PhantomData;

enum State {
    StreamStart,
    ImplicitDocumentStart,
    DocumentStart,
    DocumentContent,
    DocumentEnd,
    BlockNode,
    // BlockNodeOrIndentlessSequence,
    // FlowNode,
    BlockSequenceFirstEntry,
    BlockSequenceEntry,
    IndentlessSequenceEntry,
    BlockMappingFirstKey,
    BlockMappingKey,
    BlockMappingValue,
    FlowSequenceFirstEntry,
    FlowSequenceEntry,
    FlowSequenceEntryMappingKey,
    FlowSequenceEntryMappingValue,
    FlowSequenceEntryMappingEnd,
    FlowMappingFirstKey,
    FlowMappingKey,
    FlowMappingValue,
    FlowMappingEmptyValue,
    End,
}

pub enum Event {
    /// Reserved for internal use
    Nothing,
    StreamStart,
    StreamEnd,
    DocumentStart,
    DocumentEnd,
    /// Refer to an anchor ID
    Alias(usize),
    /// Value, style, anchor_id, tag
    // Scalar(String, TScalarStyle, usize, Option<TokenType>),
    /// Anchor ID
    SequenceStart(usize),
    SequenceEnd,
    /// Anchor ID
    MappingStart(usize),
    MappingEnd,
}

pub enum TEncoding {
    Utf8,
}

pub enum TokenType {
    NoToken,
    StreamStart(TEncoding),
    StreamEnd,
    /// major, minor
    VersionDirective(u32, u32),
    /// handle, prefix
    TagDirective(String, String),
    DocumentStart,
    DocumentEnd,
    BlockSequenceStart,
    BlockMappingStart,
    BlockEnd,
    FlowSequenceStart,
    FlowSequenceEnd,
    FlowMappingStart,
    FlowMappingEnd,
    BlockEntry,
    FlowEntry,
    Key,
    Value,
    Alias(String),
    Anchor(String),
    /// handle, suffix
    Tag(String, String),
    // Scalar(TScalarStyle, String),
}

pub type ParseResult = Result<(Event, Marker), ScanError>;

pub struct Parser<T> {
    // scanner: Scanner<T>,
    _marker: PhantomData<T>,
    states: Vec<State>,
    state: State,
    marks: Vec<Marker>,
    token: Option<Token>,
    current: Option<(Event, Marker)>,
    // anchors: HashMap<String, usize>,
    anchor_id: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Marker {
    index: usize,
    line: usize,
    col: usize,
}

pub struct ScanError {
    mark: Marker,
    info: String,
}

pub struct Token(pub Marker, pub TokenType);

impl<T> Parser<T> {
    fn skip(&mut self) {
        // self.token = None;
        //self.peek_token();
    }
    fn stream_start(&mut self) -> ParseResult {
        match *self.peek_token()? {
            Token(mark, TokenType::StreamStart(_)) => {
                // TODO: Result<?'10> is stil live from the controlflow
                self.state = State::ImplicitDocumentStart;
                Ok((Event::StreamStart, mark))
            }
            Token(mark, _) => Err(ScanError::new(mark, "did not find expected <stream-start>")),
        }
    }

    fn peek_token(&mut self) -> Result<&Token, ScanError> {
        unimplemented!()
    }
}

impl ScanError {
    pub fn new(loc: Marker, info: &str) -> ScanError {
        unimplemented!()
    }
}

fn main() {}
