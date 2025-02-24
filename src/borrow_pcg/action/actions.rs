use crate::borrow_pcg::action::BorrowPCGAction;
use crate::validity_checks_enabled;

#[derive(Clone, Debug)]
pub(crate) struct BorrowPCGActions<'tcx>(Vec<BorrowPCGAction<'tcx>>);

impl<'tcx> Default for BorrowPCGActions<'tcx> {
    fn default() -> Self {
        Self(vec![])
    }
}

impl<'tcx> BorrowPCGActions<'tcx> {
    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub(crate) fn iter(&self) -> impl Iterator<Item = &BorrowPCGAction<'tcx>> {
        self.0.iter()
    }

    pub(crate) fn to_vec(self) -> Vec<BorrowPCGAction<'tcx>> {
        self.0
    }

    pub(crate) fn new() -> Self {
        Self(vec![])
    }

    pub(crate) fn first(&self) -> Option<&BorrowPCGAction<'tcx>> {
        self.0.first()
    }

    pub(crate) fn last(&self) -> Option<&BorrowPCGAction<'tcx>> {
        self.0.last()
    }

    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    pub(crate) fn extend(&mut self, actions: BorrowPCGActions<'tcx>) {
        if validity_checks_enabled() {
            match (self.last(), actions.first()) {
            (Some(a), Some(b)) => assert_ne!(
                a, b,
                "The last action ({:#?}) is the same as the first action in the list to extend with.",
                a,
            ),
            _ => (),
        }
        }
        self.0.extend(actions.0);
    }

    pub(crate) fn push(&mut self, action: BorrowPCGAction<'tcx>) {
        if validity_checks_enabled() {
            if let Some(last) = self.last() {
                assert!(last != &action, "Action {:?} to be pushed is the same as the last pushed action, this probably a bug.", action);
            }
        }
        self.0.push(action);
    }
}