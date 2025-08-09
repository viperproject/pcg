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
    let test_r2 = r2;
    let test_x = x;
    let test_y = y;
    let test_z = z;
    let test_t1 = t1;
    let test_t2 = t2;
    let test_t3 = t3;
}
