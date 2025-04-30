use derive_more::From;

use crate::action::PcgActions;

#[derive(Debug, Clone, From)]
pub(crate) struct ExecutedActions<'tcx> {
    actions: PcgActions<'tcx>,
}

impl<'tcx> ExecutedActions<'tcx> {
    pub(crate) fn actions(self) -> PcgActions<'tcx> {
        self.actions
    }
}
