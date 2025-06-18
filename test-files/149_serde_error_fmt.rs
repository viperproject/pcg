use std::fmt::{self, Debug};

type ErrorImpl = Box<str>;

pub struct Error {
    err: ErrorImpl,
}

impl Debug for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let mut debug = formatter.debug_tuple("Error");
        debug.field(&self.err);
        debug.finish()
    }
}

fn main() {
}
