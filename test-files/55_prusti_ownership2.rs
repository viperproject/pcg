struct Point {
    x: Box<u32>,
    y: Box<u32>,
}

fn add(a: Box<u32>, b: u32) -> Box<u32> { Box::new(*a + b) }

fn shift_x(p: Point, s: u32) -> Point {
    let mut pp = p;
    let x = pp.x;     // p.x is moved out.
    pp.x = add(x, s); // x is moved into add,
                      // result moved into p.x
    pp
}

fn main(){}
