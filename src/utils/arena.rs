use std::rc::Rc;

use crate::pcg::PcgArena;

pub type PcgArenaRef<'a, T> = Rc<T, PcgArena<'a>>;
