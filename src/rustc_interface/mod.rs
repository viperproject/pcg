pub extern crate rustc_abi as abi;
pub extern crate rustc_ast as ast;
pub extern crate rustc_borrowck as rs_borrowck;
pub extern crate rustc_data_structures as data_structures;
pub extern crate rustc_driver as driver;
pub extern crate rustc_hir as hir;
pub extern crate rustc_index as index;
pub extern crate rustc_interface as interface;
pub extern crate rustc_middle as middle;
pub extern crate rustc_mir_dataflow as mir_dataflow;
pub extern crate rustc_span as span;
pub extern crate rustc_target as target;
pub extern crate rustc_session as session;

pub mod dataflow;
pub mod borrowck;
