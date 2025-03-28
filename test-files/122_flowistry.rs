fn main() {
  let a = 0;
  let mut b = 1;
  let c = ((0, &a), &mut b);
  let d = 0;
  let e = &d;
  let f = &e;
}
