struct MutWrapper<'a> { val: &'a mut String }
fn g<'a, 'b>(bp1: &'a mut MutWrapper<'b>, bp2: &'a mut MutWrapper<'b>, s: &'a mut String) { }
fn f(mut x: String, mut y: String, mut z: String) {
  let mut a = MutWrapper { val: &mut x };
  let mut b = MutWrapper { val: &mut y };
  g(&mut a, &mut b, &mut z);
  *a.val = z;
}

fn main(){}
