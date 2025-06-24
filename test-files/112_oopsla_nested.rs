struct U32Pair<'a>{f: &'a mut u32, g: &'a mut u32}
fn swap<'a, 'b>(x: &'a mut U32Pair<'b>, y: &'a mut U32Pair<'b>){ std::mem::swap(x.f,y.f) }

fn client<'a>(r1: &'a mut u32, r2: &'a mut u32, r3: &'a mut u32, r4: &'a mut u32) -> &'a mut u32{
    let mut x = U32Pair {f: r1, g: r2};
    let mut y = U32Pair {f: r3, g: r4};
    let mut rx = &mut x;
    let mut ry = &mut y;
    swap(rx, ry);
    x.f
}

fn main(){
}
