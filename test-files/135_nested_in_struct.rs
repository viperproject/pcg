struct S<'a, 'b> {x: &'a mut &'b mut i32 }

fn wow<'a, 'b, 'c: 'b>(
    s: S<'a, 'b>,
    y: &'c mut i32,
) {
    *s.x = y;
}

fn main(){
    let mut x = 1;
    let s = S {
        x: &mut &mut x,
    };
    // PCG_LIFETIME_DISPLAY: s 0 'sa
    // PCG_LIFETIME_DISPLAY: s 1 'sb

    let y = &mut 2;

    wow(s, y);

}

