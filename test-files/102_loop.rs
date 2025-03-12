fn main() {
    let vec = vec![1, 2, 3];
    let mut x = 0;
    for i in vec.into_iter() {
        x += i;
    }
}
