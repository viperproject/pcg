use derive_more::{Deref, DerefMut};

use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        has_pcs_elem::HasPcgElems,
        region_projection::
            MaybeRemoteRegionProjectionBase
        ,
    },
    pcg::PCGNode,
    utils::{
        display::DisplayWithCompilerCtxt, maybe_remote::MaybeRemotePlace, CompilerCtxt,
    },
};

#[derive(Debug, DerefMut, Deref, Hash, Eq, PartialEq, Ord, PartialOrd, Copy, Clone)]
pub(crate) struct AbstractionGraphNode<'tcx>(
    pub(crate) PCGNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>>,
);

impl<'tcx> From<LocalNode<'tcx>> for AbstractionGraphNode<'tcx> {
    fn from(node: LocalNode<'tcx>) -> Self {
        match node {
            LocalNode::Place(p) => Self(PCGNode::Place(p.into())),
            LocalNode::LifetimeProjection(rp) => {
                let rp = rp.with_base(rp.base().into());
                Self(PCGNode::LifetimeProjection(rp))
            }
        }
    }
}

impl<'tcx> TryFrom<PCGNode<'tcx>> for AbstractionGraphNode<'tcx> {
    type Error = ();

    fn try_from(value: PCGNode<'tcx>) -> Result<Self, Self::Error> {
        match value {
            PCGNode::Place(p) => Ok(Self(PCGNode::Place(p))),
            PCGNode::LifetimeProjection(rp) => {
                if let MaybeRemoteRegionProjectionBase::Place(p) = rp.base() {
                    Ok(Self(PCGNode::LifetimeProjection(rp.with_base(p))))
                } else {
                    Err(())
                }
            }
        }
    }
}

impl<'tcx, T> HasPcgElems<T> for AbstractionGraphNode<'tcx>
where
    PCGNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>>: HasPcgElems<T>,
{
    fn pcg_elems(&mut self) -> Vec<&mut T> {
        self.0.pcg_elems()
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
