struct T;
struct S<'a>{f: &'a mut Option<T>, g: &'a mut Option<T>}

fn f<'a, 'b>(x: &'a mut S<'b>, y: &'a mut S<'b>){
    std::mem::swap(x.f,y.f)
}

fn client<'a>(
    xf: &'a mut Option<T>,
    xg: &'a mut Option<T>,
    yf: &'a mut Option<T>,
    yg: &'a mut Option<T>
) -> S<'a> {
    let mut s = S{f: xf, g: xg};
    let mut x = &mut s;
    let xx = &mut *x;
    let y = &mut S{f: yf, g: yg};
    f(xx,y);
    let z = &mut x;
    s
// s could potentially borrow from any input at this point, due to the call to `f`
//?PCG: bb1[6] post_operands: _6 at After(bb0[2])↓'?21 -> s↓'?20 under conditions bb0 -> bb1,
//?PCG: bb1[6] post_operands: _7 at After(bb0[4])↓'?22 -> s↓'?20 under conditions bb0 -> bb1,
//?PCG: bb1[6] post_operands: _12 at After(bb0[18])↓'?30 -> s↓'?20 under conditions bb0 -> bb1,
//?PCG: bb1[6] post_operands: _13 at After(bb0[20])↓'?31 -> s↓'?20 under conditions bb0 -> bb1,
}

fn main(){
}
