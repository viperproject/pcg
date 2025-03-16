struct T {}
fn main () {}
fn test<'b, 'a : 'b>(x : &'a mut (&'b mut T), y : &'a mut (&'b mut T)) {
	*x = *y;
}
