fn f<'a, 'b>(x: &'a mut Vec<&'b mut i32>, y: &'a mut Vec<&'b mut i32>) {
    while let Some(y_ref) = y.pop() {
        x.push(y_ref);
    }
}

fn main() {
    let mut one = 1;
    let mut two = 2;
    let r1 = &mut one;
    let r2 = &mut two;
    let mut x = vec![r1];
    let mut y = vec![r2];
    f(&mut x, &mut y);
    let z = *x[0];
}
