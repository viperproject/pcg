struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

fn f<'a>(mut list: List<&'a mut i32>, s: &'a mut i32) -> List<&'a mut i32> {
    let h1 = list.head;
    list.head = s;
    // `list` is owned, we shouldn't have future projections
    // ~PCG: bb0[1] pre_operands: list.head↓'?7 -> list↓'?7 FUTURE
    // ~PCG: bb0[1] post_main: list.head↓'?7 -> list↓'?7 FUTURE

    // After list is re-packed, its memory comes from _4 after bb0[4]↓'?10
    // (reborrow of s for list.head) and the old version of list for list.tail

// PCG: bb0[6] pre_operands: _4 after bb0[4]↓'?10 -> list.head before collapse bb0[6]↓'?7
// PCG: bb0[6] pre_operands: borrow: _4 after bb0[4] = &mut  *s
// PCG: bb0[6] pre_operands: list.head before collapse bb0[6]↓'?7 -> list↓'?7
// PCG: bb0[6] pre_operands: list.tail before collapse bb0[6]↓'?7 -> list↓'?7
// PCG: bb0[6] pre_operands: {list after bb0[0]↓'?7 after bb0[0]} -> {list.head after bb0[0]↓'?7, list.tail before collapse bb0[6]↓'?7}

    // PCG: bb0[7] post_main: list after bb0[5]↓'?7 -> RETURN↓'?6
    list
}

fn main(){}
