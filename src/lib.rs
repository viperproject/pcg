// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns, hash_extract_if, extract_if)]
#![feature(if_let_guard, let_chains)]
#![feature(never_type)]
pub mod borrow_pcg;
pub mod combined_pcs;
pub mod coupling;
pub mod free_pcs;
pub mod r#loop;
pub mod rustc_interface;
pub mod utils;
pub mod visualization;

use std::rc::Rc;

use borrow_pcg::{
    borrow_checker::r#impl::BorrowCheckerImpl, coupling_graph_constructor::BorrowCheckerInterface,
    latest::Latest,
};
use combined_pcs::{PCGEngine, PcgSuccessor};
use free_pcs::{CapabilityKind, PcgLocation, RepackOp};
use rustc_interface::{
    borrowck::{
        self, BorrowSet, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext,
    },
    dataflow::{compute_fixpoint, PCGAnalysis},
    middle::{mir::Body, ty::TyCtxt},
};
use serde_json::json;
use utils::{
    display::{DebugLines, DisplayWithRepacker},
    env_feature_enabled,
    maybe_old::MaybeOldPlace,
    validity::HasValidityCheck,
    Place, PlaceRepacker,
};
use visualization::mir_graph::generate_json_from_mir;

use utils::json::ToJsonWithRepacker;

pub type FpcsOutput<'mir, 'tcx> = free_pcs::FreePcsAnalysis<'mir, 'tcx>;
/// Instructs that the current capability to the place (first [`CapabilityKind`]) should
/// be weakened to the second given capability. We guarantee that `_.1 > _.2`.
/// If `_.2` is `None`, the capability is removed.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Weaken<'tcx> {
    pub(crate) place: Place<'tcx>,
    pub(crate) from: CapabilityKind,
    pub(crate) to: Option<CapabilityKind>,
}

impl<'tcx> Weaken<'tcx> {
    pub(crate) fn debug_line(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        let to_str = match self.to {
            Some(to) => format!("{:?}", to),
            None => "None".to_string(),
        };
        format!(
            "Weaken {} from {:?} to {}",
            self.place.to_short_string(repacker),
            self.from,
            to_str
        )
    }

    pub(crate) fn new(
        place: Place<'tcx>,
        from: CapabilityKind,
        to: Option<CapabilityKind>,
    ) -> Self {
        if let Some(to) = to {
            pcg_validity_assert!(
                from > to,
                "FROM capability ({:?}) is not greater than TO capability ({:?})",
                from,
                to
            );
        }
        Self { place, from, to }
    }

    pub fn place(&self) -> Place<'tcx> {
        self.place
    }

    pub fn from_cap(&self) -> CapabilityKind {
        self.from
    }

    pub fn to_cap(&self) -> Option<CapabilityKind> {
        self.to
    }
}

/// Instructs that the current capability to the place should be restored to the given capability, e.g.
/// a lent exclusive capability should be restored to an exclusive capability.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct RestoreCapability<'tcx> {
    place: MaybeOldPlace<'tcx>,
    capability: CapabilityKind,
}

impl<'tcx> RestoreCapability<'tcx> {
    pub(crate) fn debug_line(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "Restore {} to {:?}",
            self.place.to_short_string(repacker),
            self.capability,
        )
    }

    pub(crate) fn new(place: MaybeOldPlace<'tcx>, capability: CapabilityKind) -> Self {
        Self { place, capability }
    }

    pub fn place(&self) -> MaybeOldPlace<'tcx> {
        self.place
    }

    pub fn capability(&self) -> CapabilityKind {
        self.capability
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for Weaken<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.place.to_json(repacker),
            "old": format!("{:?}", self.from),
            "new": format!("{:?}", self.to),
        })
    }
}

impl<'tcx> DebugLines<PlaceRepacker<'_, 'tcx>> for BorrowPCGActions<'tcx> {
    fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.0
            .iter()
            .map(|action| action.debug_line(repacker))
            .collect()
    }
}

use borrow_pcg::action::actions::BorrowPCGActions;
use std::sync::Mutex;
use utils::eval_stmt_data::EvalStmtData;

lazy_static::lazy_static! {
    /// Whether to record PCG information for each block. This is used for
    /// debugging only. This is set to true when the PCG is initially
    /// constructed, and then disabled after its construction. The reason for
    /// using a global variable is that debugging information is written during
    /// the dataflow operations of the PCG, which are also used when examining
    /// PCG results. We don't want to write the debugging information to disk
    /// during examination, of course.
    static ref RECORD_PCG: Mutex<bool> = Mutex::new(false);
}

struct PCGStmtVisualizationData<'a, 'tcx> {
    /// The value of the "latest" map at the end of the statement.
    latest: &'a Latest<'tcx>,
    free_pcg_repacks_start: &'a Vec<RepackOp<'tcx>>,
    free_pcg_repacks_middle: &'a Vec<RepackOp<'tcx>>,
    borrow_actions: &'a EvalStmtData<BorrowPCGActions<'tcx>>,
}

struct PcgSuccessorVisualizationData<'a, 'tcx> {
    owned_ops: &'a [RepackOp<'tcx>],
    borrow_ops: &'a BorrowPCGActions<'tcx>,
}

impl<'tcx, 'a> From<&'a PcgSuccessor<'tcx>> for PcgSuccessorVisualizationData<'a, 'tcx> {
    fn from(successor: &'a PcgSuccessor<'tcx>) -> Self {
        Self {
            owned_ops: successor.owned_ops(),
            borrow_ops: successor.borrow_ops(),
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for PcgSuccessorVisualizationData<'_, 'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "owned_ops": self.owned_ops.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
            "borrow_ops": self.borrow_ops.iter().map(|a| a.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for PCGStmtVisualizationData<'_, 'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "latest": self.latest.to_json(repacker),
            "free_pcg_repacks_start": self.free_pcg_repacks_start.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
            "free_pcg_repacks_middle": self.free_pcg_repacks_middle.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
            "borrow_actions": self.borrow_actions.to_json(repacker),
        })
    }
}

impl<'a, 'tcx> From<&'a PcgLocation<'tcx>> for PCGStmtVisualizationData<'a, 'tcx> {
    fn from(location: &'a PcgLocation<'tcx>) -> Self {
        Self {
            latest: &location.borrows.post_main.latest,
            free_pcg_repacks_start: &location.repacks_start,
            free_pcg_repacks_middle: &location.repacks_middle,
            borrow_actions: &location.borrow_pcg_actions,
        }
    }
}

pub trait BodyAndBorrows<'tcx> {
    fn body(&self) -> &Body<'tcx>;
    fn borrow_set(&self) -> &BorrowSet<'tcx>;
    fn region_inference_context(&self) -> &RegionInferenceContext<'tcx>;

    #[rustversion::since(2024-10-03)]
    fn output_facts(&self) -> &Option<Box<PoloniusOutput>>;

    #[rustversion::before(2024-10-03)]
    fn output_facts(&self) -> &Option<Rc<PoloniusOutput>>;

    fn location_table(&self) -> &LocationTable;
    fn input_facts(&self) -> &PoloniusInput;
}

impl<'tcx> BodyAndBorrows<'tcx> for borrowck::BodyWithBorrowckFacts<'tcx> {
    fn body(&self) -> &Body<'tcx> {
        &self.body
    }
    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        &self.borrow_set
    }
    fn region_inference_context(&self) -> &RegionInferenceContext<'tcx> {
        &self.region_inference_context
    }

    #[rustversion::since(2024-10-03)]
    fn output_facts(&self) -> &Option<Box<PoloniusOutput>> {
        &self.output_facts
    }

    #[rustversion::before(2024-10-03)]
    fn output_facts(&self) -> &Option<Rc<PoloniusOutput>> {
        &self.output_facts
    }

    fn location_table(&self) -> &LocationTable {
        self.location_table.as_ref().unwrap()
    }

    fn input_facts(&self) -> &PoloniusInput {
        self.input_facts.as_ref().unwrap()
    }
}

pub fn run_combined_pcs<'mir, 'tcx: 'mir>(
    mir: &'mir impl BodyAndBorrows<'tcx>,
    tcx: TyCtxt<'tcx>,
    visualization_output_path: Option<String>,
) -> FpcsOutput<'mir, 'tcx> {
    let bc: BorrowCheckerImpl<'mir, 'tcx> = BorrowCheckerImpl::new(tcx, mir);
    run_combined_pcs_with(mir, tcx, bc, visualization_output_path)
}

pub fn run_combined_pcs_with<'mir, 'tcx: 'mir, T: BodyAndBorrows<'tcx>>(
    mir: &'mir T,
    tcx: TyCtxt<'tcx>,
    bc: impl BorrowCheckerInterface<'mir, 'tcx> + 'mir,
    visualization_output_path: Option<String>,
) -> FpcsOutput<'mir, 'tcx> {
    let repacker = PlaceRepacker::new(mir.body(), tcx);
    let engine = PCGEngine::new(repacker, bc, visualization_output_path.clone());
    {
        let mut record_pcs = RECORD_PCG.lock().unwrap();
        *record_pcs = true;
    }
    let analysis = compute_fixpoint(PCGAnalysis(engine), tcx, mir.body());
    {
        let mut record_pcg = RECORD_PCG.lock().unwrap();
        *record_pcg = false;
    }
    if let Some(dir_path) = &visualization_output_path {
        for block in mir.body().basic_blocks.indices() {
            let state = analysis.entry_set_for_block(block);
            assert!(state.block() == block);
            let block_iterations_json_file =
                format!("{}/block_{}_iterations.json", dir_path, block.index());
            state
                .dot_graphs()
                .unwrap()
                .borrow()
                .write_json_file(&block_iterations_json_file);
        }
    }
    let mut fpcs_analysis =
        free_pcs::FreePcsAnalysis::new(analysis.into_results_cursor(mir.body()));

    if let Some(dir_path) = visualization_output_path {
        let edge_legend_file_path = format!("{}/edge_legend.dot", dir_path);
        let edge_legend_graph = crate::visualization::legend::generate_edge_legend().unwrap();
        std::fs::write(&edge_legend_file_path, edge_legend_graph)
            .expect("Failed to write edge legend");

        let node_legend_file_path = format!("{}/node_legend.dot", dir_path);
        let node_legend_graph = crate::visualization::legend::generate_node_legend().unwrap();
        std::fs::write(&node_legend_file_path, node_legend_graph)
            .expect("Failed to write node legend");
        generate_json_from_mir(&format!("{}/mir.json", dir_path), tcx, mir.body())
            .expect("Failed to generate JSON from MIR");

        let rp = PlaceRepacker::new(mir.body(), tcx);

        // Iterate over each statement in the MIR
        for (block, _data) in mir.body().basic_blocks.iter_enumerated() {
            let pcs_block_option = if let Ok(opt) = fpcs_analysis.get_all_for_bb(block) {
                opt
            } else {
                continue;
            };
            if pcs_block_option.is_none() {
                continue;
            }
            let pcs_block = pcs_block_option.unwrap();
            for (statement_index, statement) in pcs_block.statements.iter().enumerate() {
                if validity_checks_enabled() {
                    statement.assert_validity(rp);
                }
                let data = PCGStmtVisualizationData::from(statement);
                let pcg_data_file_path = format!(
                    "{}/block_{}_stmt_{}_pcg_data.json",
                    &dir_path,
                    block.index(),
                    statement_index
                );
                let pcg_data_json = data.to_json(rp);
                std::fs::write(&pcg_data_file_path, pcg_data_json.to_string())
                    .expect("Failed to write pcg data to JSON file");
            }
            for succ in pcs_block.terminator.succs {
                let data = PcgSuccessorVisualizationData::from(&succ);
                let pcg_data_file_path = format!(
                    "{}/block_{}_term_block_{}_pcg_data.json",
                    &dir_path,
                    block.index(),
                    succ.block().index()
                );
                let pcg_data_json = data.to_json(rp);
                std::fs::write(&pcg_data_file_path, pcg_data_json.to_string())
                    .expect("Failed to write pcg data to JSON file");
            }
        }
    }

    fpcs_analysis
}

#[macro_export]
macro_rules! pcg_validity_assert {
    ($($arg:tt)*) => {
        if $crate::validity_checks_enabled() {
            assert!($($arg)*);
        }
    };
}

#[macro_export]
macro_rules! pcg_validity_warn {
    ($cond:expr, $($arg:tt)*) => {
        if $crate::validity_checks_enabled() {
            if !$cond {
                tracing::warn!($($arg)*);
            }
        }
    };
}

pub(crate) fn validity_checks_enabled() -> bool {
    env_feature_enabled("PCG_VALIDITY_CHECKS").unwrap_or(cfg!(debug_assertions))
}
