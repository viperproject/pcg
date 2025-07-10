use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::{BlockedNode, LocalNode},
        domain::{AbstractionOutputTarget, FunctionCallAbstractionInput},
        edge::abstraction::AbstractionBlockEdge,
        edge_data::{EdgeData, LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{HasPcgElems, LabelRegionProjection, LabelRegionProjectionPredicate},
        latest::Latest,
        region_projection::RegionProjectionLabel,
    },
    pcg::PCGNode,
    rustc_interface::{
        hir::def_id::DefId,
        middle::{mir::Location, ty::GenericArgsRef},
    },
    utils::{
        display::DisplayWithCompilerCtxt, validity::HasValidityCheck,
        CompilerCtxt,
    },
};

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub struct FunctionData<'tcx> {
    def_id: DefId,
    substs: GenericArgsRef<'tcx>,
}

impl<'tcx> FunctionData<'tcx> {
    pub(crate) fn new(def_id: DefId, substs: GenericArgsRef<'tcx>) -> Self {
        Self { def_id, substs }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionCallAbstraction<'tcx> {
    location: Location,
    /// This may be `None` if the call is to a function pointer
    function_data: Option<FunctionData<'tcx>>,
    edge: AbstractionBlockEdge<'tcx, FunctionCallAbstractionInput<'tcx>>,
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        self.edge.redirect(from, to, ctxt);
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for FunctionCallAbstraction<'tcx> {
    fn label_region_projection(
        &mut self,
        predicate: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge
            .label_region_projection(predicate, label, repacker)
    }
}

impl<'tcx> LabelEdgePlaces<'tcx> for FunctionCallAbstraction<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge.label_blocked_places(predicate, latest, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge.label_blocked_by_places(predicate, latest, ctxt)
    }
}

impl<'tcx> EdgeData<'tcx> for FunctionCallAbstraction<'tcx> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.edge.blocks_node(node, repacker)
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PCGNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_nodes(ctxt)
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        repacker: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
    {
        self.edge.blocked_by_nodes(repacker)
    }
}

impl<'tcx> HasValidityCheck<'tcx> for FunctionCallAbstraction<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.edge.check_validity(ctxt)
    }
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for FunctionCallAbstraction<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
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
    AbstractionBlockEdge<'tcx, FunctionCallAbstractionInput<'tcx>>: HasPcgElems<T>,
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

    pub fn edge(&self) -> &AbstractionBlockEdge<'tcx, FunctionCallAbstractionInput<'tcx>> {
        &self.edge
    }

    pub fn new(
        location: Location,
        function_data: Option<FunctionData<'tcx>>,
        edge: AbstractionBlockEdge<'tcx, FunctionCallAbstractionInput<'tcx>>,
    ) -> Self {
        Self {
            location,
            function_data,
            edge,
        }
    }
}
