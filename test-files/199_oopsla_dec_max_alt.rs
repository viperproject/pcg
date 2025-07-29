// args: -C overflow-checks=off
struct Pos2D<T> {
    x: T,
    y: T
}

fn dec_max_alt<'a>(pos: &'a mut Pos2D<i32>) {
    let rx = &mut pos.x;
    let ry = &mut pos.y;
    let res = max(rx, ry);
    *res -= 1;
}

fn max<'a>(rx: &'a mut i32, ry: &'a mut i32) -> &'a mut i32 {
    if *rx > *ry {
        &mut *rx
    } else {
        &mut *ry
    }
}

fn main(){}
