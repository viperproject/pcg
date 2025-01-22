use std::marker::PhantomData;

type Ast = ();
type Frame<'a> = PhantomData<&'a ()>;
type ClassInduct<'a> = PhantomData<&'a ()>;
type ClassFrame<'a> = PhantomData<&'a ()>;

struct HeapVisitor<'a> {
    /// A stack of `Ast` nodes. This is roughly analogous to the call stack
    /// used in a typical recursive visitor.
    stack: Vec<(&'a Ast, Frame<'a>)>,
    /// Similar to the `Ast` stack above, but is used only for character
    /// classes. In particular, character classes embed their own mini
    /// recursive syntax.
    stack_class: Vec<(ClassInduct<'a>, ClassFrame<'a>)>,
}

impl<'a> HeapVisitor<'a> {
    fn new() -> Self {
        Self {
            stack: Vec::new(),
            stack_class: Vec::new(),
        }
    }
}

fn main() {
}
