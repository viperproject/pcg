// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub mod place;
pub(crate) mod repacker;
pub mod display;
mod mutable;
pub mod place_snapshot;
mod root_place;
// pub mod ty;
pub mod r#const;
pub mod debug_info;
pub mod validity;
pub use mutable::*;
pub use place::*;
pub use place_snapshot::*;
pub use repacker::*;
pub mod join_lattice_verifier;

pub fn env_feature_enabled(feature: &str) -> Option<bool> {
    match std::env::var(feature) {
        Ok(val) => {
            if val.is_empty() {
                None
            } else {
                match val.as_str() {
                    "true" | "1" => Some(true),
                    "false" | "0" => Some(false),
                    other => panic!("Environment variable {} has unexpected value: '{}'. Expected one of: true, false, 1, 0, or empty string", feature, other)
                }
            }
        },
        Err(_) => None
    }
}
