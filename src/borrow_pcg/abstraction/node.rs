use derive_more::{Deref, DerefMut};

use crate::{
    borrow_pcg::{
        has_pcs_elem::HasPcgElems,
        region_projection::{RegionProjection, RegionProjectionLabel},
    },
    pcg::{PCGNode, PCGNodeLike},
    rustc_interface::middle::mir,
    utils::{
        display::DisplayWithCompilerCtxt, maybe_remote::MaybeRemotePlace, CompilerCtxt, Place, SnapshotLocation
    },
};

#[derive(Debug, DerefMut, Deref, Hash, Eq, PartialEq, Ord, PartialOrd, Copy, Clone)]
pub(crate) struct AbstractionGraphNode<'tcx>(
    PCGNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>>,
);

impl<'tcx> AbstractionGraphNode<'tcx> {
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

    pub(crate) fn to_pcg_node(
        &self,
    ) -> PCGNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>> {
        self.0
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

    pub(crate) fn from_pcg_node(
        node: PCGNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>>,
        block: mir::BasicBlock,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        match node {
            PCGNode::Place(p) => Self::place(p),
            PCGNode::RegionProjection(rp) => Self::from_region_projection(rp, block, ctxt),
        }
    }

    pub(crate) fn from_region_projection(
        rp: RegionProjection<'tcx, MaybeRemotePlace<'tcx>>,
        block: mir::BasicBlock,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        let rp = match rp.try_to_local_node(ctxt) {
            Some(_) => rp.with_label(
                Some(RegionProjectionLabel::Location(SnapshotLocation::Start(
                    block,
                ))),
                ctxt,
            ),
            None => rp,
        };
        Self(PCGNode::RegionProjection(rp))
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

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for AbstractionGraphNode<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        self.0.to_short_string(repacker)
    }
}
