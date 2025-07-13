fn main() {
}

fn f(x_orig: &mut [u8]) {
    let x = x_orig;
    for c in x.chunks(2) {
        println!("{:?}", c);
    }
}
