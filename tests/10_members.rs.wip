use std::mem::ManuallyDrop;

type FieldsNamed = ();
type FieldsUnnamed = ();

pub enum Fields {
    /// Named fields of a struct or struct variant such as `Point { x: f64,
    /// y: f64 }`.
    Named(FieldsNamed),

    /// Unnamed fields of a tuple struct or tuple variant such as `Some(T)`.
    Unnamed(FieldsUnnamed),

    /// Unit struct or unit variant such as `None`.
    Unit,
}

mod punctuated {
    use std::mem::ManuallyDrop;

    trait IterTrait<'a, T: 'a>:
        Iterator<Item = &'a T> + DoubleEndedIterator + ExactSizeIterator
    {
        fn clone_box(&self) -> Box<NoDrop<dyn IterTrait<'a, T> + 'a>>;
    }

    pub(crate) struct NoDrop<T: ?Sized>(ManuallyDrop<T>);
    pub struct Iter<'a, T: 'a> {
        inner: Box<NoDrop<dyn IterTrait<'a, T> + 'a>>,
    }

    pub(crate) fn empty_punctuated_iter<'a, T>() -> Iter<'a, T> {
        Iter {
            inner: todo!()
        }
    }
}

type Field = ();

impl Fields {
    pub fn members(&self) -> Members {
        Members {
            fields: self.iter(),
            index: 0,
        }
    }

    pub fn iter(&self) -> punctuated::Iter<Field> {
        todo!()
    }
}

pub struct Members<'a> {
    fields: punctuated::Iter<'a, Field>,
    index: u32,
}

fn main() {
}
