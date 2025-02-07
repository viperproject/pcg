type Span = ();

struct TokenStream {
}

impl TokenStream {
    fn append(&mut self, punct: Punct) {
        unimplemented!()
    }
}

enum Spacing {
    Alone,
    Joint,
}

pub struct Punct {
    ch: char,
    spacing: Spacing,
    span: Span,
}

impl Punct {
    fn new(ch: char, spacing: Spacing) -> Self {
        Self { ch, spacing, span: () }
    }

    fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}


pub fn punct(s: &str, spans: &[Span], tokens: &mut TokenStream) {
    assert_eq!(s.len(), spans.len());

    let mut chars = s.chars();
    let mut spans = spans.iter();
    let ch = chars.next_back().unwrap();
    let span = spans.next_back().unwrap();
    for (ch, span) in chars.zip(spans) {
        let mut op = Punct::new(ch, Spacing::Joint);
        op.set_span(*span);
        tokens.append(op);
    }

    let mut op = Punct::new(ch, Spacing::Alone);
    op.set_span(*span);
    tokens.append(op);
}

fn main() {}
