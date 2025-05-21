use crate::{
    borrow_pcg::{
        borrow_pcg_edge::BlockedNode,
        has_pcs_elem::{default_make_place_old, LabelRegionProjection, MakePlaceOld},
        latest::Latest,
        region_projection::{MaybeRemoteRegionProjectionBase, RegionProjectionLabel},
    },
    edgedata_enum,
    rustc_interface::{
        data_structures::fx::FxHashSet,
        hir::def_id::DefId,
        middle::{
            mir::{BasicBlock, Location},
            ty::GenericArgsRef,
        },
    },
    utils::{redirect::MaybeRedirected, Place},
};

use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, LocalNode, ToBorrowsEdge};
use crate::borrow_pcg::domain::{AbstractionInputTarget, AbstractionOutputTarget};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::has_pcs_elem::HasPcgElems;
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::pcg::{LocalNodeLike, PCGNode};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::CompilerCtxt;
use itertools::Itertools;
use smallvec::SmallVec;

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct LoopAbstraction<'tcx> {
    pub(crate) edge: AbstractionBlockEdge<'tcx>,
    pub(crate) block: BasicBlock,
}

impl<'tcx> LoopAbstraction<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
    ) {
        self.edge.redirect(from, to);
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for LoopAbstraction<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge
            .label_region_projection(projection, label, repacker)
    }
}
impl<'tcx> MakePlaceOld<'tcx> for LoopAbstraction<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        default_make_place_old(self, place, latest, repacker)
    }
}

impl<'tcx> EdgeData<'tcx> for LoopAbstraction<'tcx> {
    fn blocked_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        self.edge.blocked_nodes(repacker)
    }

    fn blocked_by_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.edge.blocked_by_nodes(repacker)
    }
}
impl<'tcx> HasValidityCheck<'tcx> for LoopAbstraction<'tcx> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        self.edge.check_validity(repacker)
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for LoopAbstraction<'tcx> {
    fn to_short_string(&self, _repacker: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "Loop({:?}): {}",
            self.block,
            self.edge.to_short_string(_repacker)
        )
    }
}

impl<'tcx, T> HasPcgElems<T> for LoopAbstraction<'tcx>
where
    AbstractionBlockEdge<'tcx>: HasPcgElems<T>,
{
    fn pcg_elems(&mut self) -> Vec<&mut T> {
        self.edge.pcg_elems()
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for LoopAbstraction<'tcx> {
    fn to_borrow_pcg_edge(self, path_conditions: PathConditions) -> BorrowPcgEdge<'tcx> {
        BorrowPcgEdge::new(
            BorrowPcgEdgeKind::Abstraction(AbstractionType::Loop(self)),
            path_conditions,
        )
    }
}

impl<'tcx> LoopAbstraction<'tcx> {
    pub(crate) fn new(edge: AbstractionBlockEdge<'tcx>, block: BasicBlock) -> Self {
        Self { edge, block }
    }

    pub(crate) fn location(&self) -> Location {
        Location {
            block: self.block,
            statement_index: 0,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub struct FunctionData<'tcx> {
    def_id: DefId,
    substs: GenericArgsRef<'tcx>,
}

impl<'tcx> FunctionData<'tcx> {
    pub fn new(def_id: DefId, substs: GenericArgsRef<'tcx>) -> Self {
        Self { def_id, substs }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionCallAbstraction<'tcx> {
    location: Location,
    /// This may be `None` if the call is to a function pointer
    function_data: Option<FunctionData<'tcx>>,
    edge: AbstractionBlockEdge<'tcx>,
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
    ) {
        self.edge.redirect(from, to);
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for FunctionCallAbstraction<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge
            .label_region_projection(projection, label, repacker)
    }
}

impl<'tcx> MakePlaceOld<'tcx> for FunctionCallAbstraction<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        default_make_place_old(self, place, latest, repacker)
    }
}

impl<'tcx> EdgeData<'tcx> for FunctionCallAbstraction<'tcx> {
    fn blocks_node<C: Copy>(
        &self,
        node: BlockedNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        self.edge.blocks_node(node, repacker)
    }

    fn blocked_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        self.edge.blocked_nodes(repacker)
    }

    fn blocked_by_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.edge.blocked_by_nodes(repacker)
    }
}

impl<'tcx> HasValidityCheck<'tcx> for FunctionCallAbstraction<'tcx> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        self.edge.check_validity(repacker)
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for FunctionCallAbstraction<'tcx> {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "call{} at {:?}: {}",
            if let Some(function_data) = &self.function_data {
                format!(" {}", ctxt.tcx().def_path_str(function_data.def_id))
            } else {
                "".to_string()
            },
            self.location,
            self.edge.to_short_string(ctxt)
        )
    }
}

impl<'tcx, T> HasPcgElems<T> for FunctionCallAbstraction<'tcx>
where
    AbstractionBlockEdge<'tcx>: HasPcgElems<T>,
{
    fn pcg_elems(&mut self) -> Vec<&mut T> {
        self.edge.pcg_elems()
    }
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    pub fn def_id(&self) -> Option<DefId> {
        self.function_data.as_ref().map(|f| f.def_id)
    }
    pub fn substs(&self) -> Option<GenericArgsRef<'tcx>> {
        self.function_data.as_ref().map(|f| f.substs)
    }

    pub fn location(&self) -> Location {
        self.location
    }

    pub fn edge(&self) -> &AbstractionBlockEdge<'tcx> {
        &self.edge
    }

    pub fn new(
        location: Location,
        function_data: Option<FunctionData<'tcx>>,
        edge: AbstractionBlockEdge<'tcx>,
    ) -> Self {
        Self {
            location,
            function_data,
            edge,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum AbstractionType<'tcx> {
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
}

edgedata_enum!(
    AbstractionType<'tcx>,
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
);

impl<'tcx> AbstractionType<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
    ) {
        match self {
            AbstractionType::FunctionCall(c) => c.redirect(from, to),
            AbstractionType::Loop(c) => c.redirect(from, to),
        }
    }
}

#[derive(Clone, Debug, Hash)]
pub struct AbstractionBlockEdge<'tcx> {
    pub(crate) inputs: SmallVec<[AbstractionInputTarget<'tcx>; 8]>,
    outputs: SmallVec<[MaybeRedirected<AbstractionOutputTarget<'tcx>>; 8]>,
}

impl<'tcx> AbstractionBlockEdge<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
    ) {
        for output in self.outputs.iter_mut() {
            output.redirect(from, to);
        }
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for AbstractionBlockEdge<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for input in self.inputs.iter_mut() {
            changed |= input.label_region_projection(projection, label, repacker);
        }
        for output in self.outputs.iter_mut() {
            changed |= output.label_region_projection(projection, label, repacker);
        }
        changed
    }
}

impl<'tcx> EdgeData<'tcx> for AbstractionBlockEdge<'tcx> {
    fn blocks_node<C: Copy>(
        &self,
        node: BlockedNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        match node {
            PCGNode::Place(p) => self.inputs.contains(&p.into()),
            PCGNode::RegionProjection(region_projection) => match region_projection.base {
                MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => self.inputs.contains(
                    &region_projection
                        .with_base(maybe_remote_place, repacker)
                        .into(),
                ),
                MaybeRemoteRegionProjectionBase::Const(_) => false,
            },
        }
    }
    fn blocked_nodes<C: Copy>(
        &self,
        _repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        self.inputs().into_iter().map(|i| i.into()).collect()
    }

    fn blocked_by_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.outputs()
            .into_iter()
            .map(|o| o.to_local_node(repacker))
            .collect()
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for AbstractionBlockEdge<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "[{}] -> [{}]",
            self.inputs
                .iter()
                .map(|i| i.to_short_string(repacker))
                .join(", "),
            self.outputs
                .iter()
                .map(|o| o.to_short_string(repacker))
                .join(", ")
        )
    }
}

impl<'tcx> HasValidityCheck<'tcx> for AbstractionBlockEdge<'tcx> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        for input in self.inputs.iter() {
            input.check_validity(repacker)?;
        }
        for output in self.outputs.iter() {
            output.check_validity(repacker)?;
        }
        Ok(())
    }
}

// impl<'tcx> HasPcgElems<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for AbstractionBlockEdge<'tcx> {
//     fn pcg_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
//         self.outputs.iter_mut().collect()
//     }
// }

impl PartialEq for AbstractionBlockEdge<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.inputs() == other.inputs() && self.outputs() == other.outputs()
    }
}

impl Eq for AbstractionBlockEdge<'_> {}

impl<'tcx> AbstractionBlockEdge<'tcx> {
    pub(crate) fn new(
        inputs: Vec<AbstractionInputTarget<'tcx>>,
        outputs: Vec<AbstractionOutputTarget<'tcx>>,
    ) -> Self {
        assert!(!inputs.is_empty());
        assert!(!outputs.is_empty());
        Self {
            inputs: inputs.into_iter().collect(),
            outputs: outputs.into_iter().map(|o| o.into()).collect(),
        }
    }

    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        self.outputs.iter().map(|o| o.effective()).collect()
    }

    pub fn inputs(&self) -> Vec<AbstractionInputTarget<'tcx>> {
        self.inputs.to_vec()
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for AbstractionInputTarget<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            AbstractionInputTarget::Place(p) => p.pcg_elems(),
            AbstractionInputTarget::RegionProjection(rp) => rp.base.pcg_elems(),
        }
    }
}
impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for AbstractionBlockEdge<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut result = vec![];
        for input in self.inputs.iter_mut() {
            result.extend(input.pcg_elems());
        }
        for output in self.outputs.iter_mut() {
            result.extend(output.pcg_elems());
        }
        result
    }
}

impl<'tcx> AbstractionType<'tcx> {
    pub(crate) fn is_function_call(&self) -> bool {
        matches!(self, AbstractionType::FunctionCall(_))
    }

    pub fn location(&self) -> Location {
        match self {
            AbstractionType::FunctionCall(c) => c.location,
            AbstractionType::Loop(c) => c.location(),
        }
    }

    pub fn inputs(&self) -> Vec<AbstractionInputTarget<'tcx>> {
        self.edge().inputs()
    }

    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        self.edge().outputs()
    }

    pub fn edge(&self) -> &AbstractionBlockEdge<'tcx> {
        match self {
            AbstractionType::FunctionCall(c) => &c.edge,
            AbstractionType::Loop(c) => &c.edge,
        }
    }

    pub fn has_input(&self, node: AbstractionInputTarget<'tcx>) -> bool {
        self.inputs().contains(&node)
    }
}
