use crate::rustc_interface::middle::mir;
use crate::{borrow_pcg::state::BorrowsState, pcg::place_capabilities::PlaceCapabilities};

pub(crate) struct JoinOwnedData<'pcg, 'tcx, T> {
    pub(crate) owned: T,
    pub(crate) borrows: &'pcg mut BorrowsState<'tcx>,
    pub(crate) capabilities: &'pcg mut PlaceCapabilities<'tcx>,
    pub(crate) block: mir::BasicBlock,
}

impl<'pcg, 'tcx, T> JoinOwnedData<'pcg, 'tcx, T> {
    pub(crate) fn map_owned<'slf: 'res, 'res, U: 'res>(
        &'slf mut self,
        f: impl Fn(&'slf mut T) -> U,
    ) -> JoinOwnedData<'res, 'tcx, U>
    where
        'pcg: 'res,
    {
        JoinOwnedData {
            owned: f(&mut self.owned),
            borrows: self.borrows,
            capabilities: self.capabilities,
            block: self.block,
        }
    }
}

impl<'pcg, 'tcx, T> JoinOwnedData<'pcg, 'tcx, &'pcg mut T> {
    pub(crate) fn reborrow<'slf>(&'slf mut self) -> JoinOwnedData<'slf, 'tcx, &'slf mut T> {
        JoinOwnedData {
            owned: self.owned,
            borrows: self.borrows,
            capabilities: self.capabilities,
            block: self.block,
        }
    }
}
