struct U32Pair<'a> { fst: &'a mut u32, snd: &'a mut u32 }
fn f<'a>(pair: U32Pair<'a>) { }

fn main() {
    let mut x = 42; let mut y = 1337;
    let mut rx = &mut x; let mut ry = &mut y;
    let pair = U32Pair { fst: rx, snd: ry };
    let z = &mut (*pair.fst);
}
