use crate::{
    action::PcgAction,
    borrow_pcg::state::{BorrowStateMutRef, BorrowsStateLike},
    free_pcs::{LocalExpansions, RepackOp, join::data::JoinOwnedData},
    pcg::{
        PcgError,
        obtain::{ActionApplier, HasSnapshotLocation, PlaceCollapser},
        place_capabilities::PlaceCapabilities,
    },
    rustc_interface::middle::mir,
    utils::{CompilerCtxt, Place, SnapshotLocation, data_structures::HashSet},
};

pub(crate) struct JoinObtainer<'pcg: 'exp, 'exp, 'slf, 'mir, 'tcx> {
    pub(crate) ctxt: CompilerCtxt<'mir, 'tcx>,
    pub(crate) data: &'slf mut JoinOwnedData<'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>>,
    pub(crate) actions: Vec<RepackOp<'tcx>>,
}

impl HasSnapshotLocation for JoinObtainer<'_, '_, '_, '_, '_> {
    fn prev_snapshot_location(&self) -> SnapshotLocation {
        SnapshotLocation::BeforeJoin(self.data.block)
    }
}

impl<'pcg, 'mir, 'tcx> ActionApplier<'tcx> for JoinObtainer<'_, '_, '_, 'mir, 'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, PcgError> {
        match action {
            PcgAction::Borrow(action) => {
                self.data
                    .borrows
                    .apply_action(action.clone(), self.data.capabilities, self.ctxt)
            }
            PcgAction::Owned(action) => match action.kind {
                RepackOp::StorageDead(_) => todo!(),
                RepackOp::IgnoreStorageDead(_) => todo!(),
                RepackOp::Weaken(..) => todo!(),
                RepackOp::Expand(_) => todo!(),
                RepackOp::Collapse(collapse) => {
                    self.data.owned.perform_collapse_action(
                        collapse,
                        self.data.capabilities,
                        self.ctxt,
                    )?;
                    self.actions.push(action.kind);
                    Ok(true)
                }
                RepackOp::DerefShallowInit(..) => todo!(),
                RepackOp::RegainLoanedCapability(place, capability_kind) => {
                    self.data.capabilities.regain_loaned_capability(
                        place,
                        capability_kind,
                        self.data.borrows.as_mut_ref(),
                        self.ctxt,
                    )?;
                    self.actions.push(action.kind);
                    Ok(true)
                }
            },
        }
    }
}

impl<'pcg, 'mir, 'tcx> PlaceCollapser<'mir, 'tcx> for JoinObtainer<'_, '_, '_, 'mir, 'tcx> {
    fn get_local_expansions(&self, _local: mir::Local) -> &LocalExpansions<'tcx> {
        &self.data.owned
    }

    fn borrows_state(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        self.data.borrows.into()
    }

    fn capabilities(&mut self) -> &mut PlaceCapabilities<'tcx> {
        self.data.capabilities
    }

    fn leaf_places(&self, ctxt: CompilerCtxt<'mir, 'tcx>) -> HashSet<Place<'tcx>> {
        let mut leaf_places = self.data.owned.leaf_places(ctxt);
        leaf_places.retain(|p| !self.data.borrows.graph().owned_places(ctxt).contains(p));
        leaf_places
    }
}
