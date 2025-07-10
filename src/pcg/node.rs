use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::domain::LoopAbstractionInput;
use crate::borrow_pcg::has_pcs_elem::{LabelRegionProjection, LabelRegionProjectionPredicate};
use crate::borrow_pcg::region_projection::RegionProjectionLabel;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::remote::RemotePlace;
use crate::utils::{Place, SnapshotLocation};
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        region_projection::{
            MaybeRemoteRegionProjectionBase, RegionProjection, RegionProjectionBaseLike,
        },
    },
    rustc_interface::{hir::Mutability, middle::mir},
    utils::{display::DisplayWithCompilerCtxt, validity::HasValidityCheck, CompilerCtxt},
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PCGNode<'tcx, T = MaybeRemotePlace<'tcx>, U = MaybeRemoteRegionProjectionBase<'tcx>> {
    Place(T),
    RegionProjection(RegionProjection<'tcx, U>),
}

impl<'tcx> PCGNode<'tcx> {
    pub(crate) fn related_local(&self) -> Option<mir::Local> {
        self.related_current_place().map(|p| p.local)
    }

    pub(crate) fn related_current_place(&self) -> Option<Place<'tcx>> {
        match self {
            PCGNode::Place(p) => p.as_current_place(),
            PCGNode::RegionProjection(rp) => rp.base().as_current_place(),
        }
    }

    // TODO: Make this more precise
    #[allow(unused)]
    pub(crate) fn is_mutable(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        match self {
            PCGNode::Place(p) => p.is_mutable(ctxt),
            PCGNode::RegionProjection(rp) => rp
                .base()
                .as_local_place()
                .is_some_and(|p| p.ty(ctxt).ty.ref_mutability() != Some(Mutability::Not)),
        }
    }
}

impl<'tcx, T, U> PCGNode<'tcx, T, U> {
    pub(crate) fn is_place(&self) -> bool {
        matches!(self, PCGNode::Place(_))
    }

    pub(crate) fn try_into_region_projection(self) -> Result<RegionProjection<'tcx, U>, Self> {
        match self {
            PCGNode::RegionProjection(rp) => Ok(rp),
            _ => Err(self),
        }
    }
}

impl<'tcx> From<LoopAbstractionInput<'tcx>> for PCGNode<'tcx> {
    fn from(target: LoopAbstractionInput<'tcx>) -> Self {
        target.0
    }
}

impl<'tcx, T, U: Eq + From<MaybeOldPlace<'tcx>>> LabelRegionProjection<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn label_region_projection(
        &mut self,
        predicate: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if let PCGNode::RegionProjection(this_projection) = self {
            this_projection.label_region_projection(predicate, label, repacker)
        } else {
            false
        }
    }
}

impl<T, U> From<T> for PCGNode<'_, T, U> {
    fn from(value: T) -> Self {
        PCGNode::Place(value)
    }
}

impl<'tcx, U> From<RegionProjection<'tcx, U>> for PCGNode<'tcx, MaybeRemotePlace<'tcx>, U> {
    fn from(value: RegionProjection<'tcx, U>) -> Self {
        PCGNode::RegionProjection(value)
    }
}

impl<'tcx> From<RegionProjection<'tcx, Place<'tcx>>> for PCGNode<'tcx> {
    fn from(value: RegionProjection<'tcx, Place<'tcx>>) -> Self {
        PCGNode::RegionProjection(value.into())
    }
}

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for PCGNode<'tcx> {
    fn from(value: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        PCGNode::RegionProjection(value.into())
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> PCGNodeLike<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        match self {
            PCGNode::Place(p) => p.to_pcg_node(repacker),
            PCGNode::RegionProjection(rp) => rp.to_pcg_node(repacker),
        }
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> HasValidityCheck<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        match self {
            PCGNode::Place(p) => p.check_validity(ctxt),
            PCGNode::RegionProjection(rp) => rp.check_validity(ctxt),
        }
    }
}

impl<
        'tcx,
        'a,
        T: PCGNodeLike<'tcx> + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
        U: RegionProjectionBaseLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>> for PCGNode<'tcx, T, U>
{
    fn to_short_string(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        match self {
            PCGNode::Place(p) => p.to_short_string(repacker),
            PCGNode::RegionProjection(rp) => rp.to_short_string(repacker),
        }
    }
}

impl<
        'tcx,
        BC: Copy,
        T: PCGNodeLike<'tcx> + ToJsonWithCompilerCtxt<'tcx, BC>,
        U: RegionProjectionBaseLike<'tcx> + ToJsonWithCompilerCtxt<'tcx, BC>,
    > ToJsonWithCompilerCtxt<'tcx, BC> for PCGNode<'tcx, T, U>
{
    fn to_json(&self, _repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        todo!()
    }
}

pub trait MaybeHasLocation {
    fn location(&self) -> Option<SnapshotLocation>;
}

impl<'tcx, T: MaybeHasLocation, U: RegionProjectionBaseLike<'tcx> + MaybeHasLocation>
    MaybeHasLocation for PCGNode<'tcx, T, U>
{
    fn location(&self) -> Option<SnapshotLocation> {
        match self {
            PCGNode::Place(place) => place.location(),
            PCGNode::RegionProjection(region_projection) => region_projection.base().location(),
        }
    }
}

pub trait PCGNodeLike<'tcx>:
    Clone + Copy + std::fmt::Debug + Eq + PartialEq + std::hash::Hash + HasValidityCheck<'tcx>
{
    fn to_pcg_node<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx>;

    fn try_to_local_node<C: Copy>(
        self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<LocalNode<'tcx>> {
        match self.to_pcg_node(ctxt) {
            PCGNode::Place(p) => match p {
                MaybeRemotePlace::Local(maybe_old_place) => {
                    Some(maybe_old_place.to_local_node(ctxt))
                }
                MaybeRemotePlace::Remote(_) => None,
            },
            PCGNode::RegionProjection(rp) => match rp.base() {
                MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                    match maybe_remote_place {
                        MaybeRemotePlace::Local(maybe_old_place) => {
                            Some(rp.with_base(maybe_old_place).to_local_node(ctxt))
                        }
                        MaybeRemotePlace::Remote(_) => None,
                    }
                }
                MaybeRemoteRegionProjectionBase::Const(_) => None,
            },
        }
    }
}

pub(crate) trait LocalNodeLike<'tcx> {
    fn to_local_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx>;
}

impl<'tcx> LocalNodeLike<'tcx> for mir::Place<'tcx> {
    fn to_local_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl From<RemotePlace> for PCGNode<'_> {
    fn from(remote_place: RemotePlace) -> Self {
        PCGNode::Place(remote_place.into())
    }
}
