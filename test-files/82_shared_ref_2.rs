fn f(x: Result<Option<usize>, ()>) {
    if let Ok(s @ Some(y)) = x {
        // ~PCG: bb3[1] pre_operands: Expand(_1, (_1@Ok), E)
        let r = &s;
        let d = *r;
    }
}

fn main() {}
