// ---
// Sec. 2
// ---

// Fig 1
pub struct Pos2D<T> {
    x: T,
    y: T,
}

fn replace_x_owned<T>(mut pos: Pos2D<T>, new_x: T) -> Pos2D<T> {
    let old_x = pos.x;
    pos.x = new_x;
    pos
}

// Fig 2
fn replace_x<T>(pos: &mut Pos2D<T>, new_x: T) {
    let x_ref = &mut pos.x;
    *x_ref = new_x;
}

fn caller(mut original: Pos2D<i32>) {
    let pos = &mut original;
    replace_x(pos, 0);
}

// Fig 3
fn dec_max(mut pos: Pos2D<i32>, mut z: i32) {
    let max2 = if pos.x > pos.y {
        &mut pos.x
    } else {
        &mut pos.y
    };
    let max3 = if z > *max2 {
        // PCG: bb4[1] pre_operands: Remove Edge borrow: max2 = &mut  (*_7) after bb2[3] under conditions bb0 -> bb2, bb3 -> bb4
        // PCG: bb4[2] pre_main: Expand(RepackExpand { from: _1, guide: None, capability: W })
        // PCG: bb4[2] pre_main: Weaken pos.x from E to W
        pos.x = 0; // max2 borrow must end here!
        &mut z
    } else {
        &mut *max2
    };
    *max3 -= 1;
}

// Fig 4
fn max<'a>(rx: &'a mut i32, ry: &'a mut i32) -> &'a mut i32 {
    if *rx > *ry {
        &mut *rx
    } else {
        &mut *ry
    }
}

fn dec_max_alt<'a>(pos: &'a mut Pos2D<i32>) {
    let rx = &mut pos.x;
    let ry = &mut pos.y;
    let res = max(rx, ry);
    *res -= 1;
}

// Fig 5
struct List<T> {
    head: T,
    tail: Node<T>,
}

impl<T> List<T> {
    fn len(&self) -> usize {
        let mut current = self;
        let mut len = 0;
        while let Some(ref next) = &current.tail {
            len += 1;
            current = next;
        }
        len
    }
}

pub type Node<T> = Option<Box<List<T>>>;

fn penultimate_mut<'a>(list: &'a mut List<i32>) -> Option<&'a mut i32> {
    let mut current = &mut *list;
    let mut prev = None;
    while let Some(next) = &mut current.tail {
        prev = Some(&mut current.head);
        current = &mut *next;
    }
    prev
}

// Fig 6
fn swap<'a, 'b>(a: &'a mut Pos2D<&'b mut i32>, b: &'a mut Pos2D<&'b mut i32>) {
    std::mem::swap(&mut a.x, &mut b.x)
}

fn f<'a>(r1: &'a mut i32, r2: &'a mut i32, r3: &'a mut i32, r4: &'a mut i32) -> &'a mut i32 {
    let mut a = Pos2D { x: r1, y: r2 }; // a: Pos2D<&'r0 mut i32>
    let mut b = Pos2D { x: r3, y: r4 }; // b: Pos2D<&'s0 mut i32>
    let mut ra = &mut a; // ra: &'r1 Pos2D<&'r2 mut i32>
    let mut rb = &mut b; // rb: &'s1 Pos2D<&'s2 mut i32>
    swap(ra, rb); a.x
}

// ---
// Sec. 3
// ---

// Fig 8
fn get_x<T>(pos: Pos2D<T>) -> T {
    return pos.x
}

// Fig 10 (duplicated from Sec. 2, skip listing)
// fn dec_max(mut pos: Pos2D<i32>, mut z: i32) {
//     let max2 = if pos.x > pos.y {
//         &mut pos.x
//     } else {
//         &mut pos.y
//     };
//     let max3 = if z > *max2 {
//         pos.x = 0; // TODO: do we keep this line here?
//         &mut z
//     } else {
//         &mut *max2
//     };
//     *max3 -= 1;
// }

// Fig 11
fn main() {
    let mut vx = 0;
    let mut vy = 0;
    let x = &mut vx;
    let y = &mut vy;
    let pos = Pos2D { x, y };
}

// Fig 12 (duplicated from Sec. 2, skip listing)
// fn max<'a>(rx: &'a mut i32, ry: &'a mut i32) -> &'a mut i32 {
//     if *rx > *ry {
//         &mut *rx
//     } else {
//         &mut *ry
//     }
// }

// fn dec_max_alt<'a>(pos: &'a mut Pos2D<i32>) {
//     let rx = &mut pos.x;
//     let ry = &mut pos.y;
//     let res = max(rx, ry);
//     *res -= 1;
// }


// Fig 13
fn get_nth<'a>(list: Node<&'a mut i32>, n: usize) -> Option<&'a mut i32> { unimplemented!() }
fn set_nth<'a>(list: Node<&'a mut i32>, n: usize, value: i32) {
    if let Some(node) = get_nth(list, n) {
        *node = value;
    }
}

// Fig 14
fn loop_rb(a_in: &mut List<i32>, b_in: &mut List<i32>) {
    let mut a = &mut *a_in;
    let b = &mut *b_in;
    let mut x = None;
    let mut cont = true;
    while cont {
        a = a.tail.as_mut().unwrap();
        cont = a.len() > 0;
        if a.head > 0 {
            x = Some(&mut a.tail);
        } else {
            x = Some(&mut b.tail);
        }
    }
    *x.unwrap() = None;
    a_in.tail = None;
}

// Fig 15 (duplicated from Sec. 2, skip listing)
// fn penultimate_mut<'a>(list: &'a mut List<i32>) -> Option<&'a mut i32> {
//     let mut current = &mut *list;
//     let mut prev = None;
//     while let Some(next) = &mut current.tail {
//         prev = Some(&mut current.head);
//         current = &mut *next;
//     }
//     prev
// }

// Fig 17 (duplicated from Sec. 2, skip listing)
// fn swap<'a, 'b>(a: &'a mut Pos2D<&'b mut i32>, b: &'a mut Pos2D<&'b mut i32>) {
//     std::mem::swap(&mut a.x, &mut b.x)
// }

fn f2<'a>(r1: &'a mut i32, r2: &'a mut i32, r3: &'a mut i32, r4: &'a mut i32) -> &'a mut i32 {
    let mut a = Pos2D { x: r1, y: r2 }; // a: Pos2D<&'r0 mut i32>
    let mut b = Pos2D { x: r3, y: r4 }; // b: Pos2D<&'s0 mut i32>
    let mut ra = &mut a; // ra: &'r1 Pos2D<&'r2 mut i32>
    let mut rb = &mut b; // rb: &'s1 Pos2D<&'s2 mut i32>
    swap(ra, rb); a.x
}
