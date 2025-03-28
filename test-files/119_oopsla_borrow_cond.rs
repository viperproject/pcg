fn f(mut x: i32, mut y: i32, mut z: i32) {
    let r = if x > y {
        &mut x
    } else {
        &mut y
    };

    let s = if z > 5 {
        &mut *r
    } else {
        &mut z
    };

    *s = 5;
}

fn main(){

}

