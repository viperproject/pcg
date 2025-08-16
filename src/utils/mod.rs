//! Utility functions and data structures.
//!
// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub mod arena;
pub mod callbacks;
pub mod display;
pub mod eval_stmt_data;
pub(crate) mod initialized;
pub(crate) mod iter;
pub mod json;
pub(crate) mod liveness;
pub(crate) mod logging;
mod mutable;
pub mod place;
pub mod place_snapshot;
mod root_place;
pub mod validity;
pub mod visitor;

pub use mutable::*;
pub use place::*;
pub use place_snapshot::*;
pub use repacker::*;
pub(crate) mod data_structures;
pub(crate) mod domain_data;
pub(crate) mod repacker;
use crate::rustc_interface::middle::mir::BasicBlock;

#[cfg(test)]
#[rustversion::since(2025-05-24)]
pub(crate) mod test;

use lazy_static::lazy_static;
use std::collections::HashSet;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum DebugImgcat {
    JoinLoop,
    JoinOwned,
    JoinBorrows,
}

impl DebugImgcat {
    pub(crate) fn all() -> Vec<Self> {
        vec![Self::JoinLoop, Self::JoinOwned, Self::JoinBorrows]
    }
}

#[derive(Clone)]
pub struct PcgSettings<'a> {
    pub skip_bodies_with_loops: bool,
    pub max_basic_blocks: Option<usize>,
    pub max_nodes: Option<usize>,
    pub test_crates_start_from: Option<usize>,
    pub num_test_crates: Option<usize>,
    pub test_crate_parallelism: Option<usize>,
    pub check_cycles: bool,
    pub validity_checks: bool,
    pub debug_block: Option<BasicBlock>,
    pub debug_imgcat: &'a [DebugImgcat],
    pub validity_checks_warn_only: bool,
    pub panic_on_error: bool,
    pub polonius: bool,
    pub dump_mir_dataflow: bool,
    pub visualization: bool,
    pub visualization_data_dir: Option<String>,
    pub check_annotations: bool,
    pub emit_annotations: bool,
    pub check_function: Option<String>,
    pub skip_function: Option<String>,
}

impl PcgSettings<'_> {
    fn new() -> Self {
        let mut processed_vars = HashSet::new();

        // Process all known settings
        let skip_bodies_with_loops =
            Self::process_bool_var(&mut processed_vars, "PCG_SKIP_BODIES_WITH_LOOPS", false);
        let max_basic_blocks = Self::process_usize_var(&mut processed_vars, "PCG_MAX_BASIC_BLOCKS");
        let max_nodes = Self::process_usize_var(&mut processed_vars, "PCG_MAX_NODES");
        let test_crates_start_from =
            Self::process_usize_var(&mut processed_vars, "PCG_TEST_CRATES_START_FROM");
        let num_test_crates = Self::process_usize_var(&mut processed_vars, "PCG_NUM_TEST_CRATES");
        let test_crate_parallelism =
            Self::process_usize_var(&mut processed_vars, "PCG_TEST_CRATE_PARALLELISM");
        let check_cycles = Self::process_bool_var(&mut processed_vars, "PCG_CHECK_CYCLES", false);
        let validity_checks = Self::process_bool_var(
            &mut processed_vars,
            "PCG_VALIDITY_CHECKS",
            cfg!(debug_assertions),
        );
        let pcg_debug_block = Self::process_debug_block(&mut processed_vars);
        let debug_imgcat = Self::process_debug_imgcat(&mut processed_vars);
        let validity_checks_warn_only =
            Self::process_bool_var(&mut processed_vars, "PCG_VALIDITY_CHECKS_WARN_ONLY", false);
        let panic_on_error =
            Self::process_bool_var(&mut processed_vars, "PCG_PANIC_ON_ERROR", false);
        let polonius = Self::process_bool_var(&mut processed_vars, "PCG_POLONIUS", false);
        let dump_mir_dataflow =
            Self::process_bool_var(&mut processed_vars, "PCG_DUMP_MIR_DATAFLOW", false);
        let visualization = Self::process_bool_var(&mut processed_vars, "PCG_VISUALIZATION", false);
        let visualization_data_dir =
            Self::process_string_var(&mut processed_vars, "PCG_VISUALIZATION_DATA_DIR");
        let check_annotations =
            Self::process_bool_var(&mut processed_vars, "PCG_CHECK_ANNOTATIONS", false);
        let emit_annotations =
            Self::process_bool_var(&mut processed_vars, "PCG_EMIT_ANNOTATIONS", false);
        let check_function = Self::process_string_var(&mut processed_vars, "PCG_CHECK_FUNCTION");
        let skip_function = Self::process_string_var(&mut processed_vars, "PCG_SKIP_FUNCTION");

        // Check for unknown PCG_ environment variables
        Self::check_for_unknown_vars(&processed_vars);

        Self {
            skip_bodies_with_loops,
            max_basic_blocks,
            max_nodes,
            test_crates_start_from,
            num_test_crates,
            test_crate_parallelism,
            check_cycles,
            validity_checks,
            debug_block: pcg_debug_block,
            debug_imgcat,
            validity_checks_warn_only,
            panic_on_error,
            polonius,
            dump_mir_dataflow,
            visualization,
            visualization_data_dir,
            check_annotations,
            emit_annotations,
            check_function,
            skip_function,
        }
    }

    fn process_bool_var(processed: &mut HashSet<String>, var_name: &str, default: bool) -> bool {
        processed.insert(var_name.to_string());
        env_feature_enabled(var_name).unwrap_or(default)
    }

    fn process_usize_var(processed: &mut HashSet<String>, var_name: &str) -> Option<usize> {
        processed.insert(var_name.to_string());
        match std::env::var(var_name) {
            Ok(val) => {
                Some(val.parse().unwrap_or_else(|_| {
                    panic!("{} must be a valid usize, got: '{}'", var_name, val)
                }))
            }
            Err(_) => None,
        }
    }

    fn process_string_var(processed: &mut HashSet<String>, var_name: &str) -> Option<String> {
        processed.insert(var_name.to_string());
        match std::env::var(var_name) {
            Ok(val) if !val.is_empty() => Some(val),
            _ => None,
        }
    }

    fn process_debug_block(processed: &mut HashSet<String>) -> Option<BasicBlock> {
        processed.insert("PCG_DEBUG_BLOCK".to_string());
        match std::env::var("PCG_DEBUG_BLOCK") {
            Ok(val) => {
                if !val.starts_with("bb") {
                    panic!("PCG_DEBUG_BLOCK must start with 'bb'");
                }
                let block_id: usize = val[2..].parse().unwrap_or_else(|_| {
                    panic!(
                        "PCG_DEBUG_BLOCK must be in format 'bbN' where N is a number, got: '{}'",
                        val
                    )
                });
                Some(block_id.into())
            }
            Err(_) => None,
        }
    }

    fn process_debug_imgcat(processed: &mut HashSet<String>) -> &'static [DebugImgcat] {
        processed.insert("PCG_DEBUG_IMGCAT".to_string());
        match std::env::var("PCG_DEBUG_IMGCAT") {
            Ok(val) => {
                let vec: Vec<DebugImgcat> = val
                    .split(',')
                    .map(|s| s.trim())
                    .flat_map(|s| {
                        if s.to_lowercase() == "true" || s.to_lowercase() == "all" {
                            DebugImgcat::all()
                        } else if s.to_lowercase() == "join_loop" {
                            vec![DebugImgcat::JoinLoop]
                        } else if s.to_lowercase() == "join_owned" {
                            vec![DebugImgcat::JoinOwned]
                        } else if s.to_lowercase() == "join_borrows" {
                            vec![DebugImgcat::JoinBorrows]
                        } else {
                            panic!("Unexpected value for PCG_DEBUG_IMGCAT: {}", s);
                        }
                    })
                    .collect();
                // We are getting this from an env var, so we might as well leak it
                Box::leak(vec.into_boxed_slice())
            }
            Err(_) => &[],
        }
    }

    fn check_for_unknown_vars(processed: &HashSet<String>) {
        let unknown_vars: Vec<String> = std::env::vars()
            .filter_map(|(key, _)| {
                if key.starts_with("PCG_") && !processed.contains(&key) {
                    Some(key)
                } else {
                    None
                }
            })
            .collect();

        if !unknown_vars.is_empty() {
            panic!(
                "Unknown PCG_ environment variable(s) found: {}. Known variables are: {}",
                unknown_vars.join(", "),
                processed.iter().cloned().collect::<Vec<_>>().join(", ")
            );
        }
    }
}

lazy_static! {
    pub static ref SETTINGS: PcgSettings<'static> = PcgSettings::new();

    // Backward-compatible references to individual settings
    pub static ref SKIP_BODIES_WITH_LOOPS: bool = SETTINGS.skip_bodies_with_loops;
    pub static ref MAX_BASIC_BLOCKS: Option<usize> = SETTINGS.max_basic_blocks;
    pub static ref MAX_NODES: Option<usize> = SETTINGS.max_nodes;
    pub static ref TEST_CRATES_START_FROM: Option<usize> = SETTINGS.test_crates_start_from;
    pub static ref NUM_TEST_CRATES: Option<usize> = SETTINGS.num_test_crates;
    pub static ref TEST_CRATE_PARALLELISM: Option<usize> = SETTINGS.test_crate_parallelism;
    pub static ref CHECK_CYCLES: bool = SETTINGS.check_cycles;
    pub static ref VALIDITY_CHECKS: bool = SETTINGS.validity_checks;
    pub static ref DEBUG_BLOCK: Option<BasicBlock> = SETTINGS.debug_block;
    pub static ref DEBUG_IMGCAT: &'static [DebugImgcat] = SETTINGS.debug_imgcat;
    pub static ref VALIDITY_CHECKS_WARN_ONLY: bool = SETTINGS.validity_checks_warn_only;
    pub static ref PANIC_ON_ERROR: bool = SETTINGS.panic_on_error;
    pub static ref POLONIUS: bool = SETTINGS.polonius;
    pub static ref DUMP_MIR_DATAFLOW: bool = SETTINGS.dump_mir_dataflow;
    pub static ref VISUALIZATION: bool = SETTINGS.visualization;
    pub static ref VISUALIZATION_DATA_DIR: Option<String> = SETTINGS.visualization_data_dir.clone();
    pub static ref CHECK_ANNOTATIONS: bool = SETTINGS.check_annotations;
    pub static ref EMIT_ANNOTATIONS: bool = SETTINGS.emit_annotations;
    pub static ref CHECK_FUNCTION: Option<String> = SETTINGS.check_function.clone();
    pub static ref SKIP_FUNCTION: Option<String> = SETTINGS.skip_function.clone();
}

fn env_feature_enabled(feature: &str) -> Option<bool> {
    match std::env::var(feature) {
        Ok(val) => {
            if val.is_empty() {
                None
            } else {
                match val.as_str() {
                    "true" | "1" => Some(true),
                    "false" | "0" => Some(false),
                    other => panic!(
                        "Environment variable {} has unexpected value: '{}'. Expected one of: true, false, 1, 0, or empty string",
                        feature, other
                    ),
                }
            }
        }
        Err(_) => None,
    }
}
pub(crate) enum FilterMutResult {
    Changed,
    Unchanged,
    Remove,
}
