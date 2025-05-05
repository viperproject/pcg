use std::rc::Rc;


pub type ArenaRef<T, A> = Rc<T, A>;
