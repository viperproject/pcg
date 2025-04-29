use super::BorrowsVisitor;
use crate::{
    borrow_pcg::{
        action::{BorrowPCGAction, MakePlaceOldReason},
        borrow_pcg_edge::{BorrowPCGEdge, BorrowPCGEdgeLike},
        edge::{
            kind::BorrowPCGEdgeKind,
            outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        },
        path_condition::PathConditions,
        region_projection::{MaybeRemoteRegionProjectionBase, RegionProjection},
        state::obtain::ObtainReason,
    },
    free_pcs::CapabilityKind,
    pcg::{EvalStmtPhase, PCGUnsupportedError, PcgError},
    pcg_validity_assert,
    rustc_interface::middle::{
        mir::{AggregateKind, BorrowKind, Location, Operand, Rvalue, Statement, StatementKind},
        ty::{self},
    },
    utils::{self, display::DisplayWithCompilerCtxt, maybe_old::MaybeOldPlace},
};

impl<'tcx> BorrowsVisitor<'tcx, '_, '_> {


}
