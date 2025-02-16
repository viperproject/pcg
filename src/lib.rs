// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns, hash_extract_if, extract_if)]
#![feature(if_let_guard, let_chains)]
#![feature(never_type)]
pub mod borrows;
pub mod combined_pcs;
pub mod coupling;
pub mod free_pcs;
pub mod r#loop;
pub mod rustc_interface;
pub mod utils;
pub mod visualization;

use borrows::{
    borrow_pcg_action::{BorrowPCGAction, BorrowPCGActionKind},
    borrow_pcg_edge::LocalNode,
    borrow_pcg_expansion::BorrowPCGExpansion,
    borrows_graph::{validity_checks_enabled, Conditioned},
    borrows_visitor::BorrowPCGActions,
    latest::Latest,
    path_condition::PathConditions,
    region_projection_member::RegionProjectionMember,
    unblock_graph::BorrowPCGUnblockAction,
};
use combined_pcs::{BodyWithBorrowckFacts, PCGContext, PCGEngine, PlaceCapabilitySummary};
use free_pcs::{CapabilityKind, FreePcsLocation, RepackOp};
use rustc_interface::{
    borrowck::{self, BorrowSet, RegionInferenceContext},
    data_structures::fx::FxHashSet,
    dataflow::{compute_fixpoint, Analysis, PCGAnalysis},
    middle::{mir::Body, ty::TyCtxt},
    mir_dataflow,
};
use serde_json::json;
use utils::{
    display::{DebugLines, DisplayWithRepacker},
    validity::HasValidityCheck,
    Place, PlaceRepacker,
};
use visualization::mir_graph::generate_json_from_mir;

use utils::json::ToJsonWithRepacker;

pub type FpcsOutput<'mir, 'tcx> = free_pcs::FreePcsAnalysis<
    'mir,
    'tcx,
    PlaceCapabilitySummary<'mir, 'tcx>,
    PCGAnalysis<PCGEngine<'mir, 'tcx>>,
>;
/// Instructs that the current capability to the place (first [`CapabilityKind`]) should
/// be weakened to the second given capability. We guarantee that `_.1 > _.2`.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Weaken<'tcx> {
    pub(crate) place: Place<'tcx>,
    pub(crate) from: CapabilityKind,
    pub(crate) to: CapabilityKind,
}

impl<'tcx> Weaken<'tcx> {
    pub(crate) fn debug_line(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "Weaken {} from {:?} to {:?}",
            self.place.to_short_string(repacker),
            self.from,
            self.to
        )
    }

    pub(crate) fn new(place: Place<'tcx>, from: CapabilityKind, to: CapabilityKind) -> Self {
        assert!(
            from > to,
            "FROM capability ({:?}) is not greater than TO capability ({:?})",
            from,
            to
        );
        Self { place, from, to }
    }

    pub fn place(&self) -> Place<'tcx> {
        self.place
    }

    pub fn from_cap(&self) -> CapabilityKind {
        self.from
    }

    pub fn to_cap(&self) -> CapabilityKind {
        self.to
    }
}

/// Instructs that the current capability to the place should be restored to the given capability, e.g.
/// a lent exclusive capability should be restored to an exclusive capability.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct RestoreCapability<'tcx> {
    node: LocalNode<'tcx>,
    capability: CapabilityKind,
}

impl<'tcx> RestoreCapability<'tcx> {
    pub(crate) fn debug_line(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "Restore {} to {:?}",
            self.node.to_short_string(repacker),
            self.capability,
        )
    }

    pub(crate) fn new(node: LocalNode<'tcx>, capability: CapabilityKind) -> Self {
        Self { node, capability }
    }

    pub fn node(&self) -> LocalNode<'tcx> {
        self.node
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

#[derive(Clone, Debug)]
pub struct BorrowsBridge<'tcx> {
    pub(crate) actions: Vec<BorrowPCGAction<'tcx>>,
}

impl<'tcx> DebugLines<PlaceRepacker<'_, 'tcx>> for BorrowsBridge<'tcx> {
    fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.actions
            .iter()
            .map(|action| action.debug_line(repacker))
            .collect()
    }
}

impl<'tcx> BorrowsBridge<'tcx> {
    /// Actions applied to the PCG, in the order they occurred.
    pub fn actions(&self) -> &[BorrowPCGAction<'tcx>] {
        &self.actions
    }

    pub fn added_region_projection_members(
        &self,
    ) -> FxHashSet<Conditioned<RegionProjectionMember<'tcx>>> {
        self.actions
            .iter()
            .filter_map(|action| match action.kind() {
                BorrowPCGActionKind::AddRegionProjectionMember(member, path_conditions) => {
                    Some(Conditioned::new(member.clone(), path_conditions.clone()))
                }
                _ => None,
            })
            .collect()
    }

    pub fn weakens(&self) -> FxHashSet<Weaken<'tcx>> {
        self.actions
            .iter()
            .filter_map(|action| match action.kind() {
                BorrowPCGActionKind::Weaken(weaken) => Some(*weaken),
                _ => None,
            })
            .collect()
    }

    pub fn unblock_actions(&self) -> Vec<BorrowPCGUnblockAction<'tcx>> {
        self.actions
            .iter()
            .filter_map(|action| match action.kind() {
                BorrowPCGActionKind::RemoveEdge(edge) => Some(edge.clone().into()),
                _ => None,
            })
            .collect()
    }

    pub fn expands(&self) -> FxHashSet<Conditioned<BorrowPCGExpansion<'tcx>>> {
        self.actions
            .iter()
            .filter_map(|action| match action.kind() {
                BorrowPCGActionKind::InsertBorrowPCGExpansion(expansion, location) => Some(
                    Conditioned::new(expansion.clone(), PathConditions::AtBlock(location.block)),
                ),
                _ => None,
            })
            .collect()
    }
}

impl<'tcx> From<BorrowPCGActions<'tcx>> for BorrowsBridge<'tcx> {
    fn from(actions: BorrowPCGActions<'tcx>) -> Self {
        Self {
            actions: actions.to_vec(),
        }
    }
}

impl<'tcx> BorrowsBridge<'tcx> {
    pub(crate) fn new() -> Self {
        Self { actions: vec![] }
    }

    pub(crate) fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "actions": self.actions.iter().map(|a| a.debug_line_with_context(repacker)).collect::<Vec<_>>(),
        })
    }
}

use std::{rc::Rc, sync::Mutex};
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
    borrows_bridge_start: &'a BorrowsBridge<'tcx>,
    borrows_bridge_middle: &'a BorrowsBridge<'tcx>,
    actions: EvalStmtData<Vec<BorrowPCGAction<'tcx>>>,
}

impl<'a, 'tcx> ToJsonWithRepacker<'tcx> for PCGStmtVisualizationData<'a, 'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "latest": self.latest.to_json(repacker),
            "free_pcg_repacks_start": self.free_pcg_repacks_start.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
            "free_pcg_repacks_middle": self.free_pcg_repacks_middle.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
            "borrows_bridge_start": self.borrows_bridge_start.to_json(repacker),
            "borrows_bridge_middle": self.borrows_bridge_middle.to_json(repacker),
            "actions": self.actions.to_json(repacker),
        })
    }
}

impl<'a, 'tcx> From<&'a FreePcsLocation<'tcx>> for PCGStmtVisualizationData<'a, 'tcx> {
    fn from(location: &'a FreePcsLocation<'tcx>) -> Self {
        Self {
            latest: &location.borrows.post_main.latest,
            free_pcg_repacks_start: &location.repacks_start,
            free_pcg_repacks_middle: &location.repacks_middle,
            borrows_bridge_start: &location.extra_start,
            borrows_bridge_middle: &location.extra_middle,
            actions: location.actions.clone().map(|actions| actions.to_vec()),
        }
    }
}

pub trait BodyAndBorrows<'tcx> {
    fn body(&self) -> &Body<'tcx>;
    fn borrow_set(&self) -> &BorrowSet<'tcx>;
    fn region_inference_context(&self) -> &RegionInferenceContext<'tcx>;
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
}

pub fn run_combined_pcs<'mir, 'tcx>(
    mir: &'mir impl BodyAndBorrows<'tcx>,
    tcx: TyCtxt<'tcx>,
    visualization_output_path: Option<String>,
) -> FpcsOutput<'mir, 'tcx> {
    let cgx = PCGContext::new(
        tcx,
        mir.body(),
        mir.borrow_set(),
        mir.region_inference_context(),
        None,
    );
    let fpcg = PCGEngine::new(cgx, visualization_output_path.clone());
    {
        let mut record_pcs = RECORD_PCG.lock().unwrap();
        *record_pcs = true;
    }
    let analysis = compute_fixpoint(PCGAnalysis(fpcg), tcx, mir.body());
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

        let rp = PCGContext::new(
            tcx,
            mir.body(),
            mir.borrow_set(),
            mir.region_inference_context(),
            None,
        )
        .rp;

        // Iterate over each statement in the MIR
        for (block, _data) in mir.body().basic_blocks.iter_enumerated() {
            let pcs_block = fpcs_analysis.get_all_for_bb(block);
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

                for succ in pcs_block.terminator.succs.iter() {
                    let data = PCGStmtVisualizationData::from(succ);
                    let pcg_data_file_path = format!(
                        "{}/block_{}_term_block_{}_pcg_data.json",
                        &dir_path,
                        block.index(),
                        succ.location.block.index()
                    );
                    let pcg_data_json = data.to_json(rp);
                    std::fs::write(&pcg_data_file_path, pcg_data_json.to_string())
                        .expect("Failed to write pcg data to JSON file");
                }
            }
        }
    }

    fpcs_analysis
}
