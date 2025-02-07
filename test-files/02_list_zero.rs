enum List {
	Nil,
	Cons(u32, Box<List>),
}


fn all_zero(mut l : &mut List) {
	while let List::Cons(el, tl) = l {
		*el = 0;

		l = tl
	}
}

fn main() {}