pub trait HasPcsElems<T> {
    fn pcs_elems(&mut self) -> Vec<&mut T>;

    fn mut_pcs_elems(&mut self, mut f: impl FnMut(&mut T) -> bool) -> bool {
        let mut changed = false;
        for p in self.pcs_elems() {
            if f(p) {
                changed = true;
            }
        }
        changed
    }
}
