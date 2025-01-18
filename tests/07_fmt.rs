struct Ident {
    id: usize,
}

impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Ident({:?})", self.id)
    }
}

fn main() {
}
