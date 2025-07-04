use derive_more::{Deref, DerefMut};

use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        abstraction_graph_constructor::AbstractionGraph,
        borrow_pcg_edge::LocalNode,
        has_pcs_elem::HasPcgElems,
        region_projection::{
            MaybeRemoteRegionProjectionBase, RegionProjection, RegionProjectionLabel,
        },
    },
    pcg::{PCGNode, PCGNodeLike},
    rustc_interface::middle::mir,
    utils::{
        display::DisplayWithCompilerCtxt, maybe_remote::MaybeRemotePlace, CompilerCtxt, Place,
        SnapshotLocation,
    },
};

#[derive(Debug, DerefMut, Deref, Hash, Eq, PartialEq, Ord, PartialOrd, Copy, Clone)]
pub(crate) struct AbstractionGraphNode<'tcx>(
    pub(crate) PCGNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>>,
);

impl<'tcx> AbstractionGraphNode<'tcx> {
    #[allow(unused)]
    pub(crate) fn related_current_place(&self) -> Option<Place<'tcx>> {
        match self.0 {
            PCGNode::Place(p) => p.as_current_place(),
            PCGNode::RegionProjection(rp) => rp.base().as_current_place(),
        }
    }

    pub(crate) fn remove_rp_label_if_present(&mut self) {
        if let PCGNode::RegionProjection(rp) = &mut self.0 {
            self.0 = PCGNode::RegionProjection(rp.unlabelled());
        }
    }

    pub(crate) fn to_pcg_node(self, ctxt: CompilerCtxt<'_, 'tcx>) -> PCGNode<'tcx> {
        self.0.to_pcg_node(ctxt)
    }

    pub(crate) fn is_old(&self) -> bool {
        match self.0 {
            PCGNode::Place(p) => p.is_old(),
            PCGNode::RegionProjection(rp) => rp.base().is_old(),
        }
    }

    pub(crate) fn place(maybe_remote_place: MaybeRemotePlace<'tcx>) -> Self {
        AbstractionGraphNode(PCGNode::Place(maybe_remote_place))
    }

}

impl<'tcx> From<LocalNode<'tcx>> for AbstractionGraphNode<'tcx> {
    fn from(node: LocalNode<'tcx>) -> Self {
        match node {
            LocalNode::Place(p) => Self(PCGNode::Place(p.into())),
            LocalNode::RegionProjection(rp) => {
                let rp = rp.with_base(rp.base().into());
                Self(PCGNode::RegionProjection(rp))
            }
        }
    }
}

impl<'tcx> TryFrom<PCGNode<'tcx>> for AbstractionGraphNode<'tcx> {
    type Error = ();

    fn try_from(value: PCGNode<'tcx>) -> Result<Self, Self::Error> {
        match value {
            PCGNode::Place(p) => Ok(Self(PCGNode::Place(p))),
            PCGNode::RegionProjection(rp) => {
                if let MaybeRemoteRegionProjectionBase::Place(p) = rp.base() {
                    Ok(Self(PCGNode::RegionProjection(rp.with_base(p))))
                } else {
                    Err(())
                }
            }
            _ => Err(()),
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
