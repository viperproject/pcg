struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

impl<T> List<T> {
    fn push(&mut self, value: T) {}
}

fn f<'a>(mut list1: List<&'a mut i32>, mut list2: List<&'a mut i32>, mut list3: List<&'a mut i32>) {
    // PCG_LIFETIME_DISPLAY: list1 0 'a
    // PCG: bb1[0] pre_operands: Loop(bb1): [Remote(_1)] -> [list1↓'a]
    // PCG: bb1[0] pre_operands: Loop(bb1): [Remote(_1)↓'a] -> [list1↓'a]
    // PCG: bb1[0] pre_operands: Loop(bb1): [Remote(_1)↓'a] -> [list2↓'?16]
    // PCG: bb1[0] pre_operands: Loop(bb1): [Remote(_1)↓'a] -> [list3↓'?17]
    while true {
        let h1 = list1.head;
        let h2 = list2.head;
        list1 = *list1.tail.unwrap();
        list2 = *list2.tail.unwrap();
        list2.push(h1);
        list3.push(h2);
    }
}

fn main() {}
