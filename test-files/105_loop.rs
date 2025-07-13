fn main() {
    let mut vec = vec![1, 2, 3];
    let mut x = &mut 0;
    for i in vec.iter_mut() {
        x = &mut *i;
    }
    // PCG: bb8[0] post_main: Loop(bb8): [(*_14)] -> [iter↓'?18]
    // PCG: bb8[0] post_main: Loop(bb8): [(*_14)] -> [x↓'?12]
    // PCG: bb8[0] post_main: Loop(bb8): [_9] -> [x↓'?12]
    let y = *x;
}
