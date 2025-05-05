pub extern crate rustc_abi as abi;
pub extern crate rustc_ast as ast;
pub extern crate rustc_borrowck as rs_borrowck;
pub extern crate rustc_data_structures as data_structures;
pub extern crate rustc_driver as driver;
pub extern crate rustc_hir as hir;
pub extern crate rustc_index as index;
pub extern crate rustc_infer as infer;
pub extern crate rustc_interface as interface;
pub extern crate rustc_middle as middle;
pub extern crate rustc_mir_dataflow as mir_dataflow;
pub extern crate rustc_session as session;
pub extern crate rustc_span as span;
pub extern crate rustc_target as target;

pub mod borrowck;
pub mod dataflow;

#[rustversion::since(2025-03-02)]
mod aliases {
    pub(crate) type PlaceTy<'tcx> = crate::rustc_interface::middle::mir::PlaceTy<'tcx>;
    pub(crate) type FieldIdx = crate::rustc_interface::abi::FieldIdx;
    pub(crate) type VariantIdx = crate::rustc_interface::abi::VariantIdx;
    pub(crate) type RustBitSet<T> = crate::rustc_interface::index::bit_set::DenseBitSet<T>;
}

#[rustversion::before(2025-03-02)]
mod aliases {
    pub(crate) type PlaceTy<'tcx> = crate::rustc_interface::middle::mir::tcx::PlaceTy<'tcx>;
    pub(crate) type FieldIdx = crate::rustc_interface::target::abi::FieldIdx;
    pub(crate) type VariantIdx = crate::rustc_interface::target::abi::VariantIdx;
    pub(crate) type RustBitSet<T> = crate::rustc_interface::index::bit_set::BitSet<T>;
}

pub(crate) use aliases::*;
