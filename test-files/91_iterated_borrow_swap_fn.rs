struct T {}
fn test<'b, 'a : 'b>(x : &'a mut (&'b mut T), y : &'a mut (&'b mut T), c : &'a mut &'b mut T) -> (&'a mut &'b mut T, &'a mut &'b mut T) {
	*c = *x;
	*x = *y;
	*y = *c;
	return (x, y);
}
fn main () {
	let mut t1 = T {};
	let mut t2 = T {};
	let mut t3 = T {};
	let mut x1 = &mut t1;
	let mut x2 = &mut t2;
	let mut x3 = &mut t3;
	let mut y1 : &mut &mut T = &mut x1;
	let mut y2 : &mut &mut T = &mut x2;
	let mut y3 : &mut &mut T = &mut x3;

	let (y1, y2) =  test(y1, y2, y3);
	// Fails: let test_t3 = t3;

	let test_y1 = y1;
	let test_y2 = y2;

	let test_t3 = t3;

	let test_t1 = t1;
	let test_t2 = t2;

	// OK let test_t3 = t3;
}
