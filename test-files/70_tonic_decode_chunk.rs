#[derive(Debug, Clone)]
struct Status;

#[derive(Debug, Clone)]
enum State {
    ReadHeader,
    Error(Option<Status>),
}

#[derive(Debug, Clone, Copy, Default)]
pub struct BufferSettings {
    buffer_size: usize,
    yield_threshold: usize,
}
pub trait Decoder {
    /// The type that is decoded.
    type Item;

    /// The type of unrecoverable frame decoding errors.
    type Error: From<std::io::Error>;

    /// Decode a message from the buffer.
    ///
    /// The buffer will contain exactly the bytes of a full message. There
    /// is no need to get the length from the bytes, gRPC framing is handled
    /// for you.
    fn decode(&mut self, src: &mut DecodeBuf<'_>) -> Result<Option<Self::Item>, Self::Error>;

    /// Controls how tonic creates and expands decode buffers.
    fn buffer_settings(&self) -> BufferSettings {
        BufferSettings::default()
    }
}

impl From<std::io::Error> for Status {
    fn from(value: std::io::Error) -> Self {
        unimplemented!()
    }
}

struct StreamingInner {
    state: State,
    max_message_size: Option<usize>,
}

impl StreamingInner {
    fn decode_chunk(
        &mut self,
        buffer_settings: BufferSettings,
    ) -> Result<Option<DecodeBuf<'_>>, Status> {
        unimplemented!()
    }
}

pub struct DecodeBuf<'a> {
    // buf: &'a mut BytesMut,
    buf: &'a [u8],
    len: usize,
}

struct Streaming<T> {
    decoder: Box<dyn Decoder<Item = T, Error = Status> + Send + 'static>,
    inner: StreamingInner,
}

impl<T> Streaming<T> {
    // type Item = Result<T, Status>;
    fn decode_chunk(&mut self) -> Result<Option<T>, Status> {

        match self.inner.decode_chunk(self.decoder.buffer_settings())? {
            Some(mut decode_buf) => match self.decoder.decode(&mut decode_buf)? {
                Some(msg) => {
                    self.inner.state = State::ReadHeader;
                    Ok(Some(msg))
                }
                None => Ok(None),
            },
            None => Ok(None),
        }
    }
}

fn main() {
}
