type ByteStr = String;

/// Represents the path component of a URI
#[derive(Clone)]
pub struct PathAndQuery {
    pub data: ByteStr,
    pub query: u16,
}

const NONE: u16 = u16::MAX;

impl PathAndQuery {
    pub fn path(&self) -> &str {
        let ret = if self.query == NONE {
            &self.data[..]
        } else {
            &self.data[..self.query as usize]
        };

        if ret.is_empty() {
            return "/";
        }

        ret
    }
}

fn main() {
}
