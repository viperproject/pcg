fn main() {
    let mut x = 1;
    let y = [&mut x];
    // PCG: bb0[6] post_main: _3 at After(bb0[5])↓'?5 -> y↓'?4 under conditions bb0
    *y[0] = 0;
    x;
  }
