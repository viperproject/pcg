struct Repr<'a>(&'a [u8]);

impl<'a> Repr<'a> {

    /// Calls the given function on every pattern ID in this state.
    fn iter_match_pattern_ids(&self) {
        let mut pids = self.0;
        while true {
            pids = &pids[0..];
            g();
        }
    }
}

fn g(){}

fn main() {}
