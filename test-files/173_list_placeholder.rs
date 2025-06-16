struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

fn f<'a>(mut list: List<&'a mut i32>, s: &'a mut i32) -> List<&'a mut i32> {
    let h1 = list.head;
    list.head = s;
    // Because list.head is moved out, the lifetime projection shouldn't exist
    // ~PCG: bb0[1] post_main: list.head↓'?7 -> list↓'?7 FUTURE
    list
}

fn main(){}
