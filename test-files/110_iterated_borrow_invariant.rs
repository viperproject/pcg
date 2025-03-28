struct T {}
fn main () {}
fn test() {
    let mut t = T {};
    let mut x : &mut T = &mut t;
    let mut y : &mut (&mut T) = &mut x;

    let mut t1 = T {};
    let mut x1 : &mut T = &mut t1;
    let mut y1 : &mut (&mut T) = &mut x1;

	let mut c = y;
	y = y1;
	y1 = c;

	let test_y = y;
	let test_y1 = y1;

	let test_x1 = x1;
	let test_x = x;

 	let test_t1 = t1;
 	let test_t = t;

	// let test_y = y;
	// let test_x1 = x1;
 	// let test_t1 = t1;

	// let test_y1 = y1;
	// let test_x = x;
 	// let test_t = t;
}
