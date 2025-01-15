fn main() {
}

fn f(x: &[u8]) {
    for c in x.chunks(2) {
        println!("{:?}", c);
    }
}
