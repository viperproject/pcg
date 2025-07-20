use std::marker::PhantomData;

use crate::borrow_pcg::{
    domain::{AbstractionInputTarget, AbstractionOutputTarget, FunctionCallAbstractionOutput},
    edge::abstraction::{AbstractionBlockEdge, AbstractionInputLike, AbstractionType},
};
use crate::pcg::PCGNode;
use crate::rustc_interface::middle::mir::Location;

impl<'tcx> AbstractionType<'tcx> {
    pub(crate) fn is_function_call(&self) -> bool {
        matches!(self, AbstractionType::FunctionCall(_))
    }

    pub fn location(&self) -> Location {
        match self {
            AbstractionType::FunctionCall(c) => c.location(),
            AbstractionType::Loop(c) => c.location(),
        }
    }

    pub fn inputs(&self) -> Vec<AbstractionInputTarget<'tcx>> {
        self.edge().inputs()
    }

    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        self.edge().outputs()
    }

    pub fn edge(
        &self,
    ) -> AbstractionBlockEdge<'tcx, AbstractionInputTarget<'tcx>, AbstractionOutputTarget<'tcx>>
    {
        match self {
            AbstractionType::FunctionCall(c) => AbstractionBlockEdge {
                _phantom: PhantomData,
                inputs: c
                    .edge()
                    .inputs
                    .iter()
                    .map(|i| i.to_abstraction_input())
                    .collect(),
                outputs: c.edge().outputs.iter().copied().map(|o| o.into()).collect(),
            },
            AbstractionType::Loop(c) => AbstractionBlockEdge {
                _phantom: PhantomData,
                inputs: c
                    .edge
                    .inputs
                    .iter()
                    .map(|i| i.to_abstraction_input())
                    .collect(),
                outputs: c.edge.outputs.iter().copied().map(|o| (*o).into()).collect(),
            },
        }
    }
}

impl<'tcx> From<FunctionCallAbstractionOutput<'tcx>> for AbstractionOutputTarget<'tcx> {
    fn from(value: FunctionCallAbstractionOutput<'tcx>) -> Self {
        AbstractionOutputTarget(PCGNode::RegionProjection(*value))
    }
}
