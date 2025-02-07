fn unnest<'a, 'b, T>(x: &'a mut &'b mut T) -> &'a mut T {
	*x
}

fn rebor<'b, 'a : 'b, T>(x: &'a mut T) -> &'b mut T {
	x
}

fn main() {}