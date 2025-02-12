use crate::rustc_interface::{
    data_structures::fx::FxHashSet,
    hir::def_id::DefId
    ,
    middle::mir::{BasicBlock, Location},
    middle::ty::GenericArgsRef,
};

use crate::borrows::borrow_pcg_edge::{BorrowPCGEdge, BorrowPCGEdgeKind, LocalNode, ToBorrowsEdge};
use crate::borrows::domain::{AbstractionInputTarget, AbstractionOutputTarget, MaybeOldPlace};
use crate::borrows::edge_data::EdgeData;
use crate::borrows::has_pcs_elem::HasPcsElems;
use crate::borrows::path_condition::PathConditions;
use crate::borrows::region_projection::RegionProjection;
use crate::combined_pcs::{LocalNodeLike, PCGNode};
use crate::utils::display::DisplayWithRepacker;
use crate::utils::validity::HasValidityCheck;
use crate::utils::PlaceRepacker;
use itertools::Itertools;
use std::collections::BTreeSet;

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct LoopAbstraction<'tcx> {
    pub(crate) edge: AbstractionBlockEdge<'tcx>,
    pub(crate) block: BasicBlock,
}

impl<'tcx> HasValidityCheck<'tcx> for LoopAbstraction<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.edge.check_validity(repacker)
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for LoopAbstraction<'tcx> {
    fn to_short_string(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "Loop({:?}): {}",
            self.block,
            self.edge.to_short_string(_repacker)
        )
    }
}

impl<'tcx, T> HasPcsElems<T> for LoopAbstraction<'tcx>
where
    AbstractionBlockEdge<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        self.edge.pcs_elems()
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for LoopAbstraction<'tcx> {
    fn to_borrow_pcg_edge(self, path_conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge::new(
            BorrowPCGEdgeKind::Abstraction(AbstractionType::Loop(self)),
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

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionCallAbstraction<'tcx> {
    location: Location,
    def_id: DefId,
    substs: GenericArgsRef<'tcx>,
    edges: Vec<AbstractionBlockEdge<'tcx>>,
}

impl<'tcx> HasValidityCheck<'tcx> for FunctionCallAbstraction<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        for edge in self.edges.iter() {
            edge.check_validity(repacker)?;
        }
        Ok(())
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for FunctionCallAbstraction<'tcx> {
    fn to_short_string(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!("FunctionCall({:?}, {:?})", self.def_id, self.substs)
    }
}

impl<'tcx, T> HasPcsElems<T> for FunctionCallAbstraction<'tcx>
where
    AbstractionBlockEdge<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        self.edges
            .iter_mut()
            .flat_map(|edge| edge.pcs_elems())
            .collect()
    }
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    pub fn def_id(&self) -> DefId {
        self.def_id
    }
    pub fn substs(&self) -> GenericArgsRef<'tcx> {
        self.substs
    }

    pub fn location(&self) -> Location {
        self.location
    }

    pub fn edges(&self) -> &Vec<AbstractionBlockEdge<'tcx>> {
        &self.edges
    }

    pub fn new(
        location: Location,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        edges: Vec<AbstractionBlockEdge<'tcx>>,
    ) -> Self {
        assert!(!edges.is_empty());
        Self {
            location,
            def_id,
            substs,
            edges,
        }
    }
}

impl<'tcx> EdgeData<'tcx> for AbstractionType<'tcx> {
    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.inputs().into_iter().map(|i| i.into()).collect()
    }

    fn blocked_by_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        self.outputs()
            .into_iter()
            .map(|o| o.to_local_node())
            .collect()
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum AbstractionType<'tcx> {
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
}

impl<'tcx> DisplayWithRepacker<'tcx> for AbstractionType<'tcx> {
    fn to_short_string(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match self {
            AbstractionType::FunctionCall(c) => c.to_short_string(_repacker),
            AbstractionType::Loop(c) => c.to_short_string(_repacker),
        }
    }
}

impl<'tcx> HasValidityCheck<'tcx> for AbstractionType<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        match self {
            AbstractionType::FunctionCall(c) => c.check_validity(repacker),
            AbstractionType::Loop(c) => c.check_validity(repacker),
        }
    }
}

impl<'tcx, T> HasPcsElems<T> for AbstractionType<'tcx>
where
    LoopAbstraction<'tcx>: HasPcsElems<T>,
    FunctionCallAbstraction<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        match self {
            AbstractionType::FunctionCall(c) => c.pcs_elems(),
            AbstractionType::Loop(c) => c.pcs_elems(),
        }
    }
}

#[derive(Clone, Debug, Hash)]
pub struct AbstractionBlockEdge<'tcx> {
    inputs: Vec<AbstractionInputTarget<'tcx>>,
    outputs: Vec<AbstractionOutputTarget<'tcx>>,
}

impl<'tcx> DisplayWithRepacker<'tcx> for AbstractionBlockEdge<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
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
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        for input in self.inputs.iter() {
            input.check_validity(repacker)?;
        }
        for output in self.outputs.iter() {
            output.check_validity(repacker)?;
        }
        Ok(())
    }
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for AbstractionBlockEdge<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        self.outputs.iter_mut().collect()
    }
}

impl<'tcx> PartialEq for AbstractionBlockEdge<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.inputs() == other.inputs() && self.outputs() == other.outputs()
    }
}

impl<'tcx> Eq for AbstractionBlockEdge<'tcx> {}

impl<'tcx> AbstractionBlockEdge<'tcx> {
    pub(crate) fn new(
        inputs: BTreeSet<AbstractionInputTarget<'tcx>>,
        outputs: BTreeSet<AbstractionOutputTarget<'tcx>>,
    ) -> Self {
        Self {
            inputs: inputs.into_iter().collect(),
            outputs: outputs.into_iter().collect(),
        }
    }

    pub fn outputs(&self) -> BTreeSet<AbstractionOutputTarget<'tcx>> {
        self.outputs.clone().into_iter().collect()
    }

    pub fn inputs(&self) -> BTreeSet<AbstractionInputTarget<'tcx>> {
        self.inputs.clone().into_iter().collect()
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for AbstractionBlockEdge<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut result = vec![];
        for input in self.inputs.iter_mut() {
            result.extend(input.pcs_elems());
        }
        for output in self.outputs.iter_mut() {
            result.extend(output.pcs_elems());
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
        self.edges()
            .into_iter()
            .flat_map(|edge| edge.inputs())
            .collect()
    }
    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        self.edges()
            .into_iter()
            .flat_map(|edge| edge.outputs())
            .collect()
    }

    pub fn edges(&self) -> Vec<AbstractionBlockEdge<'tcx>> {
        match self {
            AbstractionType::FunctionCall(c) => c.edges.clone(),
            AbstractionType::Loop(c) => vec![c.edge.clone()],
        }
    }
}