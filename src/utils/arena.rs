use std::{borrow::Cow, rc::Rc};

use bumpalo::Bump;

pub type ArenaRef<T, A> = Rc<T, A>;
