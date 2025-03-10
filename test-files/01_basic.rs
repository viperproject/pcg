

fn main() {
	let mut x = 1;
	// PCG: bb0[2] post_main: x: E
	x += 1;

	let y = &mut x;

	*y = 0;

	assert!(x == 0);
}
