use std::{borrow::Cow, rc::Rc};

use bumpalo::Bump;

pub type ArenaRef<'arena, T> = Rc<T, &'arena Bump>;
