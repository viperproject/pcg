use derive_more::From;

use crate::action::PcgActions;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::utils::CompilerCtxt;

#[derive(Debug, Clone, From)]
pub(crate) struct ExecutedActions<'tcx> {
    actions: PcgActions<'tcx>,
}

impl<'tcx> ExecutedActions<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            actions: PcgActions::default(),
        }
    }

    pub(crate) fn record(&mut self, action: BorrowPCGAction<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx>) {
        self.actions.push(action.into());
    }

    pub(crate) fn actions(self) -> PcgActions<'tcx> {
        self.actions
    }
}
