fn main() {
    let mut x = 1;
    let y = [&mut x];
    // PCG: bb0[6] post_main: _3 before bb0[6]:PostOperands↓'?5 -> y↓'?4
    *y[0] = 0;
    x;
  }
