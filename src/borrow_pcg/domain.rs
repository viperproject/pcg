use std::rc::Rc;

use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPCGEdge;
use crate::borrow_pcg::edge::borrow::RemoteBorrow;
use crate::borrow_pcg::edge::outlives::{OutlivesEdge, OutlivesEdgeKind};
use crate::borrow_pcg::path_condition::{PathCondition, PathConditions};
use crate::borrow_pcg::state::BorrowsState;
use crate::pcg::EvalStmtPhase::*;
use crate::utils::domain_data::DomainData;
use crate::utils::incoming_states::IncomingStates;
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
