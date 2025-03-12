struct Point { x: u32, y: u32 }

fn f1<'a>(p: &'a mut Point) -> &'a mut u32 {
    // We're only reading `(*p).x` here, so it should be R
    // By only *exclusively* expand e.g *p when a field will be used
    // exclusive (e.g. mutably reborrowed)
    // PCG: bb0[4] post_operands: (*p).x: R
    if p.x == 0 {
        &mut p.x
    } else {
        &mut p.x
    }
}

fn main() {}
