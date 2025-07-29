// args: -C overflow-checks=off
struct Pos2D<T> {
    x: T,
    y: T
}

fn dec_max_alt<'a>(pos: &'a mut Pos2D<i32>) {
    let rx = &mut pos.x;
    let ry = &mut pos.y;
    let res = max(rx, ry);
    // After *res is read in the operands stage, it should be packed in pre_main back to res before being
    // expanded to write
    // PCG: bb1[3] pre_main: Restore res to E
    // PCG: bb1[3] pre_main: Add Edge: {res} -> {*res}
    // PCG: bb1[3] pre_main: Weaken *res from E to W
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
