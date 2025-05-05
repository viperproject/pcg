// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub mod callbacks;
mod mutable;
mod root_place;
pub (crate) mod incoming_states;
pub (crate) mod redirect;
pub mod debug_info;
pub mod display;
pub mod eval_stmt_data;
pub mod json;
pub mod place;
pub mod place_snapshot;
pub mod r#const;
pub mod validity;
pub mod visitor;
pub use mutable::*;
pub use place::*;
pub use place_snapshot::*;
pub use repacker::*;
pub(crate) mod domain_data;
pub(crate) mod repacker;

#[cfg(test)]
pub(crate) mod test;

pub fn env_feature_enabled(feature: &str) -> Option<bool> {
    match std::env::var(feature) {
        Ok(val) => {
            if val.is_empty() {
                None
            } else {
                match val.as_str() {
                    "true" | "1" => Some(true),
                    "false" | "0" => Some(false),
                    other => panic!("Environment variable {feature} has unexpected value: '{other}'. Expected one of: true, false, 1, 0, or empty string")
                }
            }
        },
        Err(_) => None
    }
}
