struct T{}
fn f<'a, 'b, 'c, 'd, 'e, 'f>(x: &'a mut T, y: &'b mut T, z: &'c mut T) -> (&'d mut T, &'e mut T)
    where 'a: 'd, 'b: 'd, 'b: 'e, 'c: 'e
{ todo!() }
fn main() {
    let mut t1 = T {};
    let mut t2 = T {};
    let mut t3 = T {};
    let mut x = &mut t1;
    let mut y = &mut t2;
    let mut z = &mut t3;
    let (r1, r2)  = f(x, y, z);
    let test_r1 = r1;
    // After r1 dies, x is no longer part of the abstraction but the function abstraction is still live
    // PCG: bb1[14] post_main: x: E
    // PCG: bb1[14] post_main: FunctionCall(DefId(0:4 ~ 103_function_w_reborrow[da5a]::f), ['?8, '?9, '?10, '?11, '?12]) under conditions bb0 -> bb1,
    let test_r2 = r2;
    let test_x = x;
    let test_y = y;
    let test_z = z;
    let test_t1 = t1;
    let test_t2 = t2;
    let test_t3 = t3;
}
