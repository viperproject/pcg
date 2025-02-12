fn f(c: bool){
    let mut x = 1;
    let mut y = 2;
    let mut r = if c {
        &mut x
    } else {
        &mut y
    };
    *r = 7;
    x += 1;
}

fn main(){
}
