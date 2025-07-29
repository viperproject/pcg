struct Pos2D<T> {
    x: T,
    y: T,
}

fn replace_x_ref<'a, 'b>(rf: &'a mut Pos2D<&'b mut i32>, new_x: &'b mut i32) {
    (*rf).x = new_x;
}

fn cl<'a>(r1: &'a mut i32, r2: &'a mut i32, r3: &'a mut i32, r4: &'a mut i32) {
    let mut f = Pos2D { x: r1, y: r2 }; // g: Pos2D<&'c0 mut i32>
    let rf = &mut f; // rf: &'c2 mut Pos2D<&'c1 mut i32>
    (*rf).y = r3;
    replace_x_ref(rf, r4);
    *f.x = 0;
}

fn main(){}
