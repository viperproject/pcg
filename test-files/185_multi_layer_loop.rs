fn main() {
    let mut x = 0;
    let mut y = 1;
    let mut z = 2;
    let mut rx = &mut x;
    let mut ry = &mut y;
    let mut rz = &mut z;
// PCG: bb1[0] pre_main: Loop(bb1): [*rx] -> [ry↓'?10 before bb1[0]:PreOperands]
// PCG: bb1[0] pre_main: Loop(bb1): [*rx] -> [rz↓'?11]
// PCG: bb1[0] pre_main: Loop(bb1): [*ry] -> [rz↓'?11]
// PCG: bb1[0] pre_main: Loop(bb1): [y] -> [ry↓'?10 before bb1[0]:PreOperands]
// PCG: bb1[0] pre_main: Loop(bb1): [y] -> [rz↓'?11]
// PCG: bb1[0] pre_main: Loop(bb1): [z] -> [rz↓'?11]
    while true {
        ry = &mut (*rx);
        rz = &mut (*ry);
    }
    *rz = 1;
    *ry = 2;
    *rx = 3;
}
