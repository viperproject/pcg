use crate::{
    borrow_pcg::latest::Latest,
    utils::{CompilerCtxt, Place},
};

pub struct LoopUsage<'tcx, 'other> {
    self_latest: Latest<'tcx>,
    other_latest: &'other Latest<'tcx>,
}

impl<'tcx, 'other> LoopUsage<'tcx, 'other> {
    pub(crate) fn new(self_latest: Latest<'tcx>, other_latest: &'other Latest<'tcx>) -> Self {
        Self {
            self_latest,
            other_latest,
        }
    }

    pub fn used_in_loop(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.self_latest.get(place, ctxt) != self.other_latest.get(place, ctxt)
    }
}
