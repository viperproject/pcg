//! Function and loop abstractions
pub(crate) mod function;
pub(crate) mod r#loop;
pub(crate) mod r#type;

use std::marker::PhantomData;

use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::BlockedNode,
        domain::{AbstractionInputTarget, FunctionCallAbstractionInput},
        edge::abstraction::{function::FunctionCallAbstraction, r#loop::LoopAbstraction},
        edge_data::{edgedata_enum, LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelPlace, LabelRegionProjection, LabelRegionProjectionPredicate,
            LabelRegionProjectionResult, PlaceLabeller,
        },
        region_projection::{MaybeRemoteRegionProjectionBase, RegionProjectionLabel},
    },
    pcg::PCGNodeLike,
    utils::{maybe_remote::MaybeRemotePlace},
};

use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::domain::LoopAbstractionInput;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::has_pcs_elem::HasPcgElems;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::pcg::PCGNode;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::CompilerCtxt;
use itertools::Itertools;

/// Either a function call or a loop abstraction
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

/// A hyperedge for a function or loop abstraction
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct AbstractionBlockEdge<'tcx, Input, Output> {
    _phantom: PhantomData<&'tcx ()>,
    inputs: Vec<Input>,
    pub(crate) outputs: Vec<Output>,
}

impl<'tcx, T: LabelPlace<'tcx>, U: LabelPlace<'tcx>> LabelEdgePlaces<'tcx>
    for AbstractionBlockEdge<'tcx, T, U>
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for input in &mut self.inputs {
            changed |= input.label_place(predicate, labeller, ctxt);
        }
        changed
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for output in &mut self.outputs {
            changed |= output.label_place(predicate, labeller, ctxt);
        }
        changed
    }
}

impl<
        'tcx: 'a,
        'a,
        Input: LabelRegionProjection<'tcx>
            + PCGNodeLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
        Output: LabelRegionProjection<'tcx>
            + PCGNodeLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > LabelRegionProjection<'tcx> for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn label_region_projection(
        &mut self,
        projection: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelRegionProjectionResult {
        let mut changed = LabelRegionProjectionResult::Unchanged;
        let mut i = 0;
        while i < self.inputs.len() {
            let input = &mut self.inputs[i];
            changed |= input.label_region_projection(projection, label, ctxt);
            let input = self.inputs[i];
            if self
                .outputs
                .iter()
                .any(|o| o.to_pcg_node(ctxt) == input.to_pcg_node(ctxt))
            {
                self.inputs
                    .retain(|i| i.to_pcg_node(ctxt) != input.to_pcg_node(ctxt));
                self.assert_validity(ctxt);
                return LabelRegionProjectionResult::Changed;
            }
            i += 1;
        }
        let mut j = 0;
        while j < self.outputs.len() {
            let output = &mut self.outputs[j];
            changed |= output.label_region_projection(projection, label, ctxt);
            let output = self.outputs[j];
            if self
                .inputs
                .iter()
                .any(|i| i.to_pcg_node(ctxt) == output.to_pcg_node(ctxt))
            {
                self.outputs
                    .retain(|o| o.to_pcg_node(ctxt) != output.to_pcg_node(ctxt));
                self.assert_validity(ctxt);
                return LabelRegionProjectionResult::Changed;
            }
            j += 1;
        }
        self.assert_validity(ctxt);
        changed
    }
}

trait AbstractionInputLike<'tcx>: Sized + Clone {
    fn inputs_block<C: Copy>(
        inputs: &[Self],
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool;

    fn to_abstraction_input(self) -> AbstractionInputTarget<'tcx>;
}

impl<'tcx> AbstractionInputLike<'tcx> for LoopAbstractionInput<'tcx> {
    fn inputs_block<C: Copy>(
        inputs: &[Self],
        node: BlockedNode<'tcx>,
        _ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        match node {
            PCGNode::Place(p) => inputs.contains(&p.into()),
            PCGNode::RegionProjection(region_projection) => match region_projection.base {
                MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                    inputs.contains(&(region_projection.with_base(maybe_remote_place).into()))
                }
                MaybeRemoteRegionProjectionBase::Const(_) => false,
            },
        }
    }

    fn to_abstraction_input(self) -> AbstractionInputTarget<'tcx> {
        AbstractionInputTarget(self.0)
    }
}

impl<'tcx> From<RegionProjection<'tcx, MaybeRemotePlace<'tcx>>> for LoopAbstractionInput<'tcx> {
    fn from(value: RegionProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Self {
        LoopAbstractionInput(PCGNode::RegionProjection(value.into()))
    }
}

impl<'tcx> AbstractionInputLike<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn inputs_block<C: Copy>(
        inputs: &[Self],
        node: BlockedNode<'tcx>,
        _ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        match node {
            PCGNode::Place(_) => false,
            PCGNode::RegionProjection(region_projection) => match region_projection.base {
                MaybeRemoteRegionProjectionBase::Place(MaybeRemotePlace::Local(rp)) => {
                    inputs.contains(&region_projection.with_base(rp).into())
                }
                _ => false,
            },
        }
    }

    fn to_abstraction_input(self) -> AbstractionInputTarget<'tcx> {
        AbstractionInputTarget(self.0.into())
    }
}

impl<'tcx, Input: AbstractionInputLike<'tcx>, Output: Copy + PCGNodeLike<'tcx>> EdgeData<'tcx>
    for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        Input::inputs_block(&self.inputs, node, ctxt)
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        _ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PCGNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(self.inputs().into_iter().map(|i| *i.to_abstraction_input()))
    }

    fn blocked_by_nodes<'slf, 'mir, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
        'mir: 'slf,
    {
        Box::new(
            self.outputs()
                .into_iter()
                .map(move |o| o.to_pcg_node(ctxt).try_to_local_node(ctxt).unwrap()),
        )
    }
}

impl<
        'tcx,
        'a,
        Input: DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
        Output: DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        format!(
            "[{}] -> [{}]",
            self.inputs
                .iter()
                .map(|i| i.to_short_string(ctxt))
                .join(", "),
            self.outputs
                .iter()
                .map(|o| o.to_short_string(ctxt))
                .join(", ")
        )
    }
}

impl<
        'tcx: 'a,
        'a,
        Input: HasValidityCheck<'tcx>
            + PCGNodeLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
        Output: HasValidityCheck<'tcx>
            + PCGNodeLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > HasValidityCheck<'tcx> for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        for input in self.inputs.iter() {
            input.check_validity(ctxt)?;
        }
        for output in self.outputs.iter() {
            output.check_validity(ctxt)?;
        }
        for input in self.inputs.iter() {
            for output in self.outputs.iter() {
                if input.to_pcg_node(ctxt) == output.to_pcg_node(ctxt) {
                    return Err(format!(
                        "Input {:?} and output {:?} are the same node",
                        input, output,
                    ));
                }
            }
        }
        Ok(())
    }
}

impl<
        'tcx: 'a,
        'a,
        Input: Clone
            + PCGNodeLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
        Output: Clone
            + PCGNodeLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > AbstractionBlockEdge<'tcx, Input, Output>
{
    pub(crate) fn new(
        inputs: Vec<Input>,
        outputs: Vec<Output>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        assert!(!inputs.is_empty());
        assert!(!outputs.is_empty());
        let result = Self {
            _phantom: PhantomData,
            inputs,
            outputs: outputs.into_iter().map(|o| o.into()).collect(),
        };
        result.assert_validity(ctxt);
        result
    }
}

impl<Input: Clone, Output: Copy> AbstractionBlockEdge<'_, Input, Output> {
    pub fn outputs(&self) -> Vec<Output> {
        self.outputs.clone()
    }

    pub fn inputs(&self) -> Vec<Input> {
        self.inputs.clone()
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for LoopAbstractionInput<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match &mut self.0 {
            PCGNode::Place(p) => p.pcg_elems(),
            PCGNode::RegionProjection(rp) => rp.base.pcg_elems(),
        }
    }
}
impl<'tcx, Input: HasPcgElems<MaybeOldPlace<'tcx>>, Output: HasPcgElems<MaybeOldPlace<'tcx>>>
    HasPcgElems<MaybeOldPlace<'tcx>> for AbstractionBlockEdge<'tcx, Input, Output>
{
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
