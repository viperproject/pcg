use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrows_visitor::BorrowPCGActions;

#[derive(Debug)]
pub(crate) struct ExecutedActions<'tcx> {
    actions: BorrowPCGActions<'tcx>,
    changed: bool,
}

impl<'tcx> ExecutedActions<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            actions: BorrowPCGActions::new(),
            changed: false,
        }
    }

    pub(crate) fn record(&mut self, action: BorrowPCGAction<'tcx>, changed: bool) {
        self.actions.push(action);
        self.changed |= changed;
    }

    pub(crate) fn extend(&mut self, actions: ExecutedActions<'tcx>) {
        self.actions.extend(actions.actions);
        self.changed |= actions.changed;
    }

    pub(crate) fn actions(self) -> BorrowPCGActions<'tcx> {
        self.actions
    }
}