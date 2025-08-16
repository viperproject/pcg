use crate::borrow_checker::BorrowCheckerInterface;
use crate::pcg::place_capabilities::{
    PlaceCapabilitiesInterface, PlaceCapabilitiesReader, SymbolicPlaceCapabilities,
};
use crate::pcg::{
    BodyAnalysis, CapabilityConstraint, CapabilityKind, CapabilityRule, CapabilityRules,
    CapabilityVar, Choice, DataflowStmtPhase, IntroduceConstraints, PcgArena,
    PcgBlockDebugVisualizationGraphs, PcgRef, SymbolicCapability, SymbolicCapabilityCtxt,
};
use crate::rustc_interface::middle::{mir, ty};
use crate::utils::data_structures::HashMap;
use crate::utils::logging::LogPredicate;
use crate::utils::{
    CompilerCtxt, DataflowCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, Place, SETTINGS,
    SnapshotLocation, StmtGraphs, ToGraph,
};
use crate::visualization::write_pcg_dot_graph_to_file;

impl<'a, 'tcx: 'a> std::fmt::Debug for AnalysisCtxt<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AnalysisCtxt {{ block: {:?} }}", self.block)
    }
}

impl<'a, 'tcx: 'a> DataflowCtxt<'a, 'tcx> for AnalysisCtxt<'a, 'tcx> {
    fn try_into_analysis_ctxt(self) -> Option<AnalysisCtxt<'a, 'tcx>> {
        Some(self)
    }
}

mod private {
    use crate::{
        pcg::{BodyAnalysis, PcgArena, PcgBlockDebugVisualizationGraphs, SymbolicCapabilityCtxt},
        rustc_interface::middle::mir,
        utils::{CompilerCtxt, PcgSettings},
    };

    #[derive(Copy, Clone)]
    pub struct AnalysisCtxt<'a, 'tcx> {
        pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
        pub(crate) body_analysis: &'a BodyAnalysis<'a, 'tcx>,
        pub(crate) settings: &'a PcgSettings<'a>,
        #[allow(dead_code)]
        pub(crate) symbolic_capability_ctxt: SymbolicCapabilityCtxt<'a, 'tcx>,
        pub(crate) block: mir::BasicBlock,
        pub(crate) graphs: Option<PcgBlockDebugVisualizationGraphs<'a>>,
        pub(crate) arena: PcgArena<'a>,
    }
}

fn dot_filename_for(output_dir: &str, relative_filename: &str) -> String {
    format!("{}/{}", output_dir, relative_filename)
}

pub use private::*;

impl<'a, 'tcx: 'a> AnalysisCtxt<'a, 'tcx> {
    pub(crate) fn generate_pcg_debug_visualization_graph<'pcg>(
        self,
        location: mir::Location,
        to_graph: ToGraph,
        pcg: PcgRef<'pcg, 'tcx>,
    ) {
        if location.block.as_usize() == 0 {
            assert!(!matches!(
                to_graph,
                ToGraph::Phase(DataflowStmtPhase::Join(_))
            ));
        }
        if let Some(debug_data) = self.graphs {
            let relative_filename = StmtGraphs::relative_filename(location, to_graph);
            let filename = dot_filename_for(debug_data.dot_output_dir, &relative_filename);
            match to_graph {
                ToGraph::Action(phase, action_idx) => {
                    debug_data.dot_graphs.borrow_mut().insert_for_action(
                        location,
                        phase,
                        action_idx,
                        relative_filename,
                    );
                }
                ToGraph::Phase(phase) => debug_data.dot_graphs.borrow_mut().insert_for_phase(
                    location.statement_index,
                    phase,
                    relative_filename,
                ),
            }

            write_pcg_dot_graph_to_file(pcg, self, location, &filename).unwrap();
        }
    }

    #[allow(dead_code)]
    pub(crate) fn create_place_capability_inference_vars(
        self,
        places: impl Iterator<Item = Place<'tcx>>,
        location: SnapshotLocation,
        capabilities: &mut SymbolicPlaceCapabilities<'tcx>,
    ) -> HashMap<Place<'tcx>, CapabilityVar> {
        places
            .into_iter()
            .map(|place| {
                let var = self.symbolic_capability_ctxt.introduce_var(place, location);
                capabilities.insert(place, var, self);
                (place, var)
            })
            .collect()
    }

    #[allow(dead_code)]
    pub(crate) fn get_or_create_place_capability_inference_vars(
        self,
        places: impl Iterator<Item = Place<'tcx>>,
        location: SnapshotLocation,
        capabilities: &mut SymbolicPlaceCapabilities<'tcx>,
    ) -> HashMap<Place<'tcx>, SymbolicCapability> {
        places
            .into_iter()
            .map(|place| {
                (
                    place,
                    self.get_or_create_place_capability_inference_var(
                        place,
                        location,
                        capabilities,
                    ),
                )
            })
            .collect()
    }

    pub(crate) fn get_or_create_place_capability_inference_var(
        self,
        place: Place<'tcx>,
        location: SnapshotLocation,
        capabilities: &mut SymbolicPlaceCapabilities<'tcx>,
    ) -> SymbolicCapability {
        if let Some(cap) = capabilities.get(place, self) {
            cap
        } else {
            let var = self.symbolic_capability_ctxt.introduce_var(place, location);
            capabilities.insert(place, var, self);
            SymbolicCapability::Variable(var)
        }
    }

    #[allow(dead_code)]
    fn get_application_rules(
        self,
        constraints: &IntroduceConstraints<'tcx>,
        capabilities: &mut SymbolicPlaceCapabilities<'tcx>,
    ) -> CapabilityRules<'a, 'tcx> {
        match constraints {
            IntroduceConstraints::ExpandForSharedBorrow {
                base_place,
                expansion_places,
                ..
            } => {
                let base_cap = capabilities.get(*base_place, self).unwrap();
                let expand_read = CapabilityRule::new(
                    base_cap.gte(CapabilityKind::Read),
                    HashMap::from_iter(expansion_places.iter().map(|p| (*p, CapabilityKind::Read))),
                );
                let expand_exclusive = CapabilityRule::new(
                    CapabilityConstraint::eq(base_cap, CapabilityKind::Exclusive),
                    HashMap::from_iter(
                        expansion_places
                            .iter()
                            .map(|p| (*p, CapabilityKind::Exclusive)),
                    ),
                );
                CapabilityRules::one_of(vec![expand_read, expand_exclusive])
            }
        }
    }

    #[allow(dead_code)]
    fn apply_capability_rules(
        self,
        constraints: &IntroduceConstraints<'tcx>,
        rule: CapabilityRules<'a, 'tcx>,
        capabilities: &mut SymbolicPlaceCapabilities<'tcx>,
    ) {
        match rule {
            CapabilityRules::OneOf(rules) => {
                let choice = self
                    .symbolic_capability_ctxt
                    .add_choice(Choice::new(rules.len()));
                let affected_places = constraints.affected_places();
                let new_place_vars = self.create_place_capability_inference_vars(
                    affected_places,
                    constraints.before_location(),
                    capabilities,
                );
                for (decision, rule) in rules.into_iter_enumerated() {
                    let decision = CapabilityConstraint::Decision { choice, decision };
                    self.require(decision.implies(rule.pre, self.arena));
                    for (place, cap) in rule.post.into_iter() {
                        let var = new_place_vars[&place];
                        self.require(CapabilityConstraint::eq(var, cap));
                    }
                }
            }
        }
    }

    pub(crate) fn require(&self, constraint: CapabilityConstraint<'a>) {
        self.symbolic_capability_ctxt.require(constraint);
    }
}

impl<'a, 'tcx> HasCompilerCtxt<'a, 'tcx> for AnalysisCtxt<'a, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'a, 'tcx, ()> {
        self.ctxt.ctxt()
    }
}

impl<'a, 'tcx> HasBorrowCheckerCtxt<'a, 'tcx> for AnalysisCtxt<'a, 'tcx> {
    fn bc(&self) -> &'a dyn BorrowCheckerInterface<'tcx> {
        self.ctxt.bc()
    }

    fn bc_ctxt(&self) -> CompilerCtxt<'a, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>> {
        self.ctxt
    }
}

impl<'a, 'tcx> AnalysisCtxt<'a, 'tcx> {
    pub(crate) fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.ctxt.tcx()
    }
    pub(crate) fn body(&self) -> &'a mir::Body<'tcx> {
        self.ctxt.body()
    }
    pub(crate) fn new(
        ctxt: CompilerCtxt<'a, 'tcx>,
        block: mir::BasicBlock,
        body_analysis: &'a BodyAnalysis<'a, 'tcx>,
        symbolic_capability_ctxt: SymbolicCapabilityCtxt<'a, 'tcx>,
        arena: PcgArena<'a>,
        graphs: Option<PcgBlockDebugVisualizationGraphs<'a>>,
    ) -> Self {
        Self {
            ctxt,
            body_analysis,
            settings: &SETTINGS,
            block,
            graphs,
            symbolic_capability_ctxt,
            arena,
        }
    }
    pub(crate) fn matches(&self, predicate: LogPredicate) -> bool {
        match predicate {
            LogPredicate::DebugBlock => {
                if let Some(debug_block) = self.settings.debug_block {
                    debug_block == self.block
                } else {
                    false
                }
            }
        }
    }
}
