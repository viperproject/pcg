fn foo() {
    let mut x = 1;
    let y = &mut &mut &mut x;
    let a = ***y;
}

fn main(){

}
