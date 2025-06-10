fn f<'a, 'b>(x: &'a mut Vec<&'b mut i32>, y: &'a mut Vec<&'b mut i32>) {
    let y_ref = y.pop().unwrap();
    // The future of `*y|13` shouldn't be blocked by an RP with a labelled place
    // ~PCG: bb0[4] post_main: *y↓'?13 FUTURE -> _5 after bb0[3]↓'?17
    x.push(y_ref);
}

fn main() {
}
