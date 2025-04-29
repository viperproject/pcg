use crate::action::PcgActions;
use crate::borrow_pcg::action::actions::BorrowPCGActions;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::utils::CompilerCtxt;

#[derive(Debug, Clone)]
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

    pub(crate) fn extend(&mut self, actions: ExecutedActions<'tcx>) {
        self.actions.extend(actions.actions);
    }

    pub(crate) fn actions(self) -> PcgActions<'tcx> {
        self.actions
    }
}
