fn main() {
    let mut a = 0;
    let b = (1, &mut a);
    *b.1 += 1;
    let c = b;
    c;
 }
