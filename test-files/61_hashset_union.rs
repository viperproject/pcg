use std::collections::HashSet;
fn union(set: &mut HashSet<i32>, other: &HashSet<i32>) -> bool {
  let orig_len = set.len();
  // PCG: bb8[1] post_main: Add Edge: (_12@Some).0↓'?18 -> el↓'?23 under conditions bb5 -> { bb7, bb8 }

  for el in other {
    set.insert(*el);
  }
  let final_len = set.len();
  return orig_len != final_len;
}

fn main() {
}
