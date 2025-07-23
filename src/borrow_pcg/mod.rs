//! Logic and data structures relating to the borrowed places in the PCG.
pub mod action;
pub(crate) mod abstraction;
pub mod borrow_pcg_edge;
pub mod borrow_pcg_expansion;
pub(crate) mod domain;
pub mod graph;
pub mod state;
pub(crate) mod visitor;
pub mod edge;
pub mod edge_data;
pub(crate) mod has_pcs_elem;
pub mod latest;
pub mod path_condition;
pub mod region_projection;
pub mod unblock_graph;

pub use domain::AbstractionInputTarget;
pub use domain::AbstractionOutputTarget;
