use std::rc::Rc;

use crate::borrow_pcg::action::actions::BorrowPCGActions;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPCGEdge;
use crate::borrow_pcg::edge::borrow::RemoteBorrow;
use crate::borrow_pcg::edge::outlives::{OutlivesEdge, OutlivesEdgeKind};
use crate::borrow_pcg::path_condition::{PathCondition, PathConditions};
use crate::borrow_pcg::state::BorrowsState;
use crate::combined_pcs::EvalStmtPhase::*;
use crate::utils::domain_data::DomainData;
use crate::utils::eval_stmt_data::EvalStmtData;
use crate::utils::{Place, PlaceRepacker};

pub type AbstractionInputTarget<'tcx> = CGNode<'tcx>;

impl<'tcx> TryFrom<AbstractionInputTarget<'tcx>> for RegionProjection<'tcx> {
    type Error = ();

    fn try_from(value: AbstractionInputTarget<'tcx>) -> Result<Self, Self::Error> {
        match value {
            CGNode::RegionProjection(rp) => Ok(rp.into()),
            _ => Err(()),
        }
    }
}

pub type AbstractionOutputTarget<'tcx> = RegionProjection<'tcx, MaybeOldPlace<'tcx>>;

use super::coupling_graph_constructor::BorrowCheckerInterface;
use super::visitor::extract_regions;
use super::{coupling_graph_constructor::CGNode, region_projection::RegionProjection};
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::remote::RemotePlace;

use crate::rustc_interface::middle::{
    mir::{BasicBlock, Local, Location},
    ty::{self},
};

const DEBUG_JOIN_ITERATION_LIMIT: usize = 10000;

impl<'mir, 'tcx, BC: BorrowCheckerInterface<'mir, 'tcx>> BorrowsDomain<'mir, 'tcx, BC> {
    pub(crate) fn join(&mut self, other: &Self) -> bool {
        self.data.enter_join();
        self.debug_join_iteration += 1;

        if self.debug_join_iteration > DEBUG_JOIN_ITERATION_LIMIT {
            panic!(
                "Block {:?} has not terminated after {} join iterations, this is probably a bug",
                self.block(),
                self.debug_join_iteration
            );
        }
        // For performance reasons we don't check validity here.
        // if validity_checks_enabled() {
        //     pcg_validity_assert!(other.is_valid(), "Other graph is invalid");
        // }
        let mut other_after = other.post_main_state().clone();

        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let pc = PathCondition::new(other.block(), self.block());
        other_after.add_path_condition(pc);

        let self_block = self.block();

        Rc::<BorrowsState<'tcx>>::make_mut(&mut self.data.entry_state).join(
            &other_after,
            self_block,
            other.block(),
            &self.bc,
            self.repacker,
        )
    }
}

#[derive(Clone)]
/// The domain of the Borrow PCG dataflow analysis. Note that this contains many
/// fields which serve as context (e.g. reference to a borrow-checker impl to
/// properly compute joins) but are not updated in the analysis itself.
pub struct BorrowsDomain<'mir, 'tcx, BC> {
    pub(crate) data: DomainData<BorrowsState<'tcx>>,
    pub(crate) block: Option<BasicBlock>,
    pub(crate) repacker: PlaceRepacker<'mir, 'tcx>,
    pub(crate) actions: EvalStmtData<BorrowPCGActions<'tcx>>,
    pub(crate) bc: BC,
    /// The number of times the join operation has been called, this is just
    /// used for debugging to identify if the dataflow analysis is not
    /// terminating.
    pub(crate) debug_join_iteration: usize,
}

impl<BC> PartialEq for BorrowsDomain<'_, '_, BC> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data && self.block == other.block
    }
}

impl<BC> Eq for BorrowsDomain<'_, '_, BC> {}

impl<BC> std::fmt::Debug for BorrowsDomain<'_, '_, BC> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BorrowsDomain")
            .field("states", &self.data.states)
            .field("block", &self.block)
            .finish()
    }
}

impl<'mir, 'tcx, BC> BorrowsDomain<'mir, 'tcx, BC> {
    pub(crate) fn post_main_state(&self) -> &BorrowsState<'tcx> {
        self.data.states[PostMain].as_ref()
    }

    pub(crate) fn post_state_mut(&mut self) -> &mut BorrowsState<'tcx> {
        self.data.states.get_mut(PostMain)
    }

    pub(crate) fn set_block(&mut self, block: BasicBlock) {
        self.block = Some(block);
    }

    pub(crate) fn block(&self) -> BasicBlock {
        self.block.unwrap()
    }

    pub(crate) fn new(
        repacker: PlaceRepacker<'mir, 'tcx>,
        bc: BC,
        block: Option<BasicBlock>,
    ) -> Self {
        Self {
            data: DomainData::default(),
            actions: EvalStmtData::default(),
            block,
            repacker,
            debug_join_iteration: 0,
            bc,
        }
    }

    fn introduce_initial_borrows(&mut self, local: Local) {
        let local_decl = &self.repacker.body().local_decls[local];
        let arg_place: Place<'tcx> = local.into();
        if let ty::TyKind::Ref(_, _, _) = local_decl.ty.kind() {
            let entry_state = Rc::<BorrowsState<'tcx>>::make_mut(&mut self.data.entry_state);
            let _ = entry_state.apply_action(
                BorrowPCGAction::add_edge(RemoteBorrow::new(local).into(), true),
                self.repacker,
            );
        }
        for region in extract_regions(local_decl.ty, self.repacker) {
            let region_projection =
                RegionProjection::new(region, arg_place.into(), self.repacker).unwrap();
            let entry_state = Rc::<BorrowsState<'tcx>>::make_mut(&mut self.data.entry_state);
            assert!(entry_state
                .apply_action(
                    BorrowPCGAction::add_edge(
                        BorrowPCGEdge::new(
                            OutlivesEdge::new(
                                RegionProjection::new(
                                    region,
                                    RemotePlace::new(local).into(),
                                    self.repacker,
                                )
                                .unwrap_or_else(|e| {
                                    panic!(
                                        "Failed to create region for remote place (for {local:?}).
                                    Local ty: {:?}. Error: {:?}",
                                        local_decl.ty, e
                                    );
                                }),
                                region_projection,
                                OutlivesEdgeKind::Todo,
                                self.repacker,
                            )
                            .into(),
                            PathConditions::AtBlock((Location::START).block),
                        ),
                        true,
                    ),
                    self.repacker,
                )
                .unwrap());
        }
    }

    pub(crate) fn initialize_as_start_block(&mut self) {
        for arg in self.repacker.body().args_iter() {
            self.introduce_initial_borrows(arg);
        }
    }
}
