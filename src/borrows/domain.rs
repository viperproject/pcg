use std::rc::Rc;

use crate::borrows::borrow_pcg_action::BorrowPCGAction;
use crate::borrows::borrows_state::BorrowsState;
use crate::borrows::borrows_visitor::{BorrowCheckerImpl, BorrowPCGActions};
use crate::borrows::path_condition::{PathCondition, PathConditions};
use crate::borrows::region_projection_member::{
    RegionProjectionMember, RegionProjectionMemberKind,
};
use crate::combined_pcs::EvalStmtPhase::*;
use crate::combined_pcs::{PCGError, PCGErrorKind, PCGNodeLike};
use crate::free_pcs::CapabilityKind;
use crate::utils::domain_data::DomainData;
use crate::utils::eval_stmt_data::EvalStmtData;
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::{Place, PlaceRepacker};
use crate::{utils, BorrowsBridge};
use smallvec::smallvec;

pub type AbstractionInputTarget<'tcx> = CGNode<'tcx>;
pub type AbstractionOutputTarget<'tcx> = RegionProjection<'tcx, MaybeOldPlace<'tcx>>;

use super::{coupling_graph_constructor::CGNode, region_projection::RegionProjection};
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::remote::RemotePlace;

use crate::rustc_interface::{
    middle::{
        mir::{BasicBlock, Local, Location},
        ty::{self},
    },
    mir_dataflow::JoinSemiLattice,
};

const DEBUG_JOIN_ITERATION_LIMIT: usize = 10000;

impl<'mir, 'tcx> JoinSemiLattice for BorrowsDomain<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        self.data.enter_join();
        self.debug_join_iteration += 1;

        if self.debug_join_iteration > DEBUG_JOIN_ITERATION_LIMIT {
            panic!(
                "Block {:?} has not terminated after {} join iterations, this is probably a bug",
                self.block(),
                self.debug_join_iteration
            );
        }
        if other.has_error() && !self.has_error() {
            self.error = other.error.clone();
            return true;
        } else if self.has_error() {
            return false;
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
pub struct BorrowsDomain<'mir, 'tcx> {
    pub(crate) data: DomainData<BorrowsState<'tcx>>,
    pub(crate) block: Option<BasicBlock>,
    pub(crate) repacker: PlaceRepacker<'mir, 'tcx>,
    pub(crate) actions: EvalStmtData<BorrowPCGActions<'tcx>>,
    pub(crate) bc: BorrowCheckerImpl<'mir, 'tcx>,
    /// The number of times the join operation has been called, this is just
    /// used for debugging to identify if the dataflow analysis is not
    /// terminating.
    pub(crate) debug_join_iteration: usize,
    error: Option<PCGError>,
}

impl<'mir, 'tcx> PartialEq for BorrowsDomain<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data && self.block == other.block
    }
}

impl<'mir, 'tcx> Eq for BorrowsDomain<'mir, 'tcx> {}

impl<'mir, 'tcx> std::fmt::Debug for BorrowsDomain<'mir, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BorrowsDomain")
            .field("states", &self.data.states)
            .field("block", &self.block)
            .finish()
    }
}

impl<'mir, 'tcx> BorrowsDomain<'mir, 'tcx> {
    pub(crate) fn get_bridge(&self) -> (BorrowsBridge<'tcx>, BorrowsBridge<'tcx>) {
        (
            self.actions.pre_operands.clone().into(),
            self.actions.pre_main.clone().into(),
        )
    }
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

    pub(crate) fn report_error(&mut self, error: PCGError) {
        eprintln!("PCG Error: {:?}", error);
        self.error = Some(error);
    }

    #[allow(unused)]
    pub(crate) fn has_internal_error(&self) -> bool {
        self.error
            .as_ref()
            .map_or(false, |e| matches!(e.kind, PCGErrorKind::Internal(_)))
    }

    pub(crate) fn has_error(&self) -> bool {
        self.error.is_some()
    }

    pub(crate) fn new(
        repacker: PlaceRepacker<'mir, 'tcx>,
        bc: BorrowCheckerImpl<'mir, 'tcx>,
        block: Option<BasicBlock>,
    ) -> Self {
        Self {
            data: DomainData::default(),
            actions: EvalStmtData::default(),
            block,
            repacker,
            debug_join_iteration: 0,
            error: None,
            bc,
        }
    }

    fn introduce_initial_borrows(&mut self, local: Local) {
        let local_decl = &self.repacker.body().local_decls[local];
        let arg_place: Place<'tcx> = local.into();
        if let ty::TyKind::Ref(region, _, mutability) = local_decl.ty.kind() {
            let entry_state = Rc::<BorrowsState<'tcx>>::make_mut(&mut self.data.entry_state);
            assert!(entry_state.set_capability(
                MaybeRemotePlace::place_assigned_to_local(local).into(),
                if mutability.is_mut() {
                    CapabilityKind::Exclusive
                } else {
                    CapabilityKind::Read
                },
                self.repacker,
            ));
            let _ = entry_state.apply_action(
                BorrowPCGAction::add_region_projection_member(
                    RegionProjectionMember::new(
                        smallvec![MaybeRemotePlace::place_assigned_to_local(local).into()],
                        smallvec![RegionProjection::new(
                            (*region).into(),
                            arg_place,
                            self.repacker
                        )
                        .into(),],
                        RegionProjectionMemberKind::FunctionInput,
                    ),
                    PathConditions::AtBlock((Location::START).block),
                    "Introduce initial borrow",
                ),
                self.repacker,
            );
        }
        let local_place: utils::Place<'tcx> = arg_place.into();
        for region_projection in local_place.region_projections(self.repacker) {
            let entry_state = Rc::<BorrowsState<'tcx>>::make_mut(&mut self.data.entry_state);
            assert!(entry_state.apply_action(
                BorrowPCGAction::add_region_projection_member(
                    RegionProjectionMember::new(
                        smallvec![RegionProjection::new(
                            region_projection.region(self.repacker),
                            RemotePlace::new(local),
                            self.repacker,
                        )
                        .to_pcg_node(),],
                        smallvec![region_projection.into()],
                        RegionProjectionMemberKind::Todo,
                    ),
                    PathConditions::AtBlock((Location::START).block),
                    "Initialize Local",
                ),
                self.repacker,
            ));
        }
    }

    pub(crate) fn initialize_as_start_block(&mut self) {
        for arg in self.repacker.body().args_iter() {
            let arg_place: utils::Place<'tcx> = arg.into();
            for rp in arg_place.region_projections(self.repacker) {
                let entry_state = Rc::<BorrowsState<'tcx>>::make_mut(&mut self.data.entry_state);
                assert!(entry_state.set_capability(
                    rp.into(),
                    CapabilityKind::Exclusive,
                    self.repacker
                ));
            }
            self.introduce_initial_borrows(arg);
        }
    }
}
