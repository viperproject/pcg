fn choose<'a, T>(c: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if c { x } else { y }
}

fn client(c: bool){
    let mut x = 1;
    let mut y = 2;
    let r = choose(c, &mut x, &mut y);
    *r = 3;
}

fn main(){
    client(true);
}
