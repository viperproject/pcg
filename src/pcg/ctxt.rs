use crate::borrow_checker::BorrowCheckerInterface;
use crate::pcg::place_capabilities::{
    PlaceCapabilitiesInterface, PlaceCapabilitiesReader, SymbolicPlaceCapabilities,
};
use crate::pcg::{
    BodyAnalysis, CapabilityConstraint, CapabilityKind, CapabilityRule, CapabilityRules,
    CapabilityVar, Choice, ChoiceIdx, IntroduceConstraints, PcgArena, SymbolicCapability,
    SymbolicCapabilityCtxt,
};
use crate::rustc_interface::middle::{mir, ty};
use crate::utils::data_structures::HashMap;
use crate::utils::logging::LogPredicate;
use crate::utils::{
    CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, PcgSettings, Place, SETTINGS,
    SnapshotLocation,
};

impl<'a, 'tcx: 'a> std::fmt::Debug for AnalysisCtxt<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AnalysisCtxt {{ block: {:?} }}", self.block)
    }
}

#[derive(Copy, Clone)]
pub(crate) struct AnalysisCtxt<'a, 'tcx> {
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
    pub(crate) body_analysis: &'a BodyAnalysis<'a, 'tcx>,
    pub(crate) settings: &'a PcgSettings<'a>,
    pub(crate) symbolic_capability_ctxt: SymbolicCapabilityCtxt<'a, 'tcx>,
    pub(crate) block: mir::BasicBlock,
    pub(crate) arena: PcgArena<'a>,
}

impl<'a, 'tcx: 'a> AnalysisCtxt<'a, 'tcx> {
    pub(crate) fn alloc<T>(&self, val: T) -> &'a mut T {
        self.arena.alloc(val)
    }

    pub(crate) fn create_place_capability_inference_vars(
        self,
        places: impl Iterator<Item = Place<'tcx>>,
        location: SnapshotLocation,
        capabilities: &mut SymbolicPlaceCapabilities<'a, 'tcx>,
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

    pub(crate) fn get_or_create_place_capability_inference_vars(
        self,
        places: impl Iterator<Item = Place<'tcx>>,
        location: SnapshotLocation,
        capabilities: &mut SymbolicPlaceCapabilities<'a, 'tcx>,
    ) -> HashMap<Place<'tcx>, SymbolicCapability<'a>> {
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
        capabilities: &mut SymbolicPlaceCapabilities<'a, 'tcx>,
    ) -> SymbolicCapability<'a> {
        if let Some(cap) = capabilities.get(place, self) {
            cap
        } else {
            let var = self
                .symbolic_capability_ctxt
                .introduce_var(place, location)
                .into();
            capabilities.insert(place, var, self);
            SymbolicCapability::Variable(var)
        }
    }

    fn get_application_rules(
        self,
        constraints: &IntroduceConstraints<'tcx>,
        capabilities: &mut SymbolicPlaceCapabilities<'a, 'tcx>,
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

    fn apply_capability_rules(
        self,
        constraints: &IntroduceConstraints<'tcx>,
        rule: CapabilityRules<'a, 'tcx>,
        capabilities: &mut SymbolicPlaceCapabilities<'a, 'tcx>,
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
    ) -> Self {
        Self {
            ctxt,
            body_analysis,
            settings: &SETTINGS,
            block,
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
