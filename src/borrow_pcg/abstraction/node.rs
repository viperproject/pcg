use derive_more::{Deref, DerefMut};

use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{borrow_pcg_edge::LocalNode, region_projection::MaybeRemoteRegionProjectionBase},
    pcg::PcgNode,
    utils::{CompilerCtxt, display::DisplayWithCompilerCtxt, maybe_remote::MaybeRemotePlace},
};

#[derive(Debug, DerefMut, Deref, Hash, Eq, PartialEq, Ord, PartialOrd, Copy, Clone)]
pub(crate) struct AbstractionGraphNode<'tcx>(
    pub(crate) PcgNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>>,
);

impl<'tcx> From<LocalNode<'tcx>> for AbstractionGraphNode<'tcx> {
    fn from(node: LocalNode<'tcx>) -> Self {
        match node {
            LocalNode::Place(p) => Self(PcgNode::Place(p.into())),
            LocalNode::LifetimeProjection(rp) => {
                let rp = rp.with_base(rp.base().into());
                Self(PcgNode::LifetimeProjection(rp))
            }
        }
    }
}

impl<'tcx> TryFrom<PcgNode<'tcx>> for AbstractionGraphNode<'tcx> {
    type Error = ();

    fn try_from(value: PcgNode<'tcx>) -> Result<Self, Self::Error> {
        match value {
            PcgNode::Place(p) => Ok(Self(PcgNode::Place(p))),
            PcgNode::LifetimeProjection(rp) => {
                if let MaybeRemoteRegionProjectionBase::Place(p) = rp.base() {
                    Ok(Self(PcgNode::LifetimeProjection(rp.with_base(p))))
                } else {
                    Err(())
                }
            }
        }
    }
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for AbstractionGraphNode<'tcx>
{
    fn to_short_string(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        self.0.to_short_string(repacker)
    }
}
