pub enum Pair<T, P> {
    Punctuated(T, P),
    End(T),
}

impl<T, P> Pair<T, P> {
    /// Extracts the syntax tree node from this punctuated pair, discarding the
    /// following punctuation.
    pub fn into_value(self) -> T {
        match self {
            Pair::Punctuated(t, _) | Pair::End(t) => t,
        }
    }
}

fn main() {}
