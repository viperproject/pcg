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
pub(crate) mod incoming_states;
pub(crate) mod initialized;
pub mod json;
pub(crate) mod liveness;
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

#[cfg(test)]
#[rustversion::since(2025-05-24)]
pub(crate) mod test;

use lazy_static::lazy_static;

lazy_static! {
    pub static ref MAX_BASIC_BLOCKS: Option<usize> = match std::env::var("PCG_MAX_BASIC_BLOCKS") {
        Ok(val) => Some(val.parse().unwrap()),
        Err(_) => None,
    };
    pub static ref MAX_NODES: Option<usize> = match std::env::var("PCG_MAX_NODES") {
        Ok(val) => Some(val.parse().unwrap()),
        Err(_) => None,
    };
    pub static ref TEST_CRATES_START_FROM: Option<usize> =
        match std::env::var("PCG_TEST_CRATES_START_FROM") {
            Ok(val) => Some(val.parse().unwrap()),
            Err(_) => None,
        };
    pub static ref CHECK_CYCLES: bool = env_feature_enabled("PCG_CHECK_CYCLES").unwrap_or(false);
    pub static ref VALIDITY_CHECKS: bool =
        env_feature_enabled("PCG_VALIDITY_CHECKS").unwrap_or(cfg!(debug_assertions));
    pub static ref COUPLING_DEBUG_IMGCAT: bool =
        env_feature_enabled("PCG_COUPLING_DEBUG_IMGCAT").unwrap_or(false);
    pub static ref BORROWS_DEBUG_IMGCAT: bool =
        env_feature_enabled("PCG_BORROWS_DEBUG_IMGCAT").unwrap_or(false);
    pub static ref VALIDITY_CHECKS_WARN_ONLY: bool =
        env_feature_enabled("PCG_VALIDITY_CHECKS_WARN_ONLY").unwrap_or(false);
    pub static ref PANIC_ON_ERROR: bool =
        env_feature_enabled("PCG_PANIC_ON_ERROR").unwrap_or(false);
    pub static ref POLONIUS: bool = env_feature_enabled("PCG_POLONIUS").unwrap_or(false);
    pub static ref DUMP_MIR_DATAFLOW: bool =
        env_feature_enabled("PCG_DUMP_MIR_DATAFLOW").unwrap_or(false);
}

fn env_feature_enabled(feature: &'static str) -> Option<bool> {
    match std::env::var(feature) {
        Ok(val) => {
            if val.is_empty() {
                None
            } else {
                match val.as_str() {
                    "true" | "1" => Some(true),
                    "false" | "0" => Some(false),
                    other => panic!(
                        "Environment variable {feature} has unexpected value: '{other}'. Expected one of: true, false, 1, 0, or empty string"
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
