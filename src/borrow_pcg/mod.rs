//! Logic and data structures relating to the borrowed places in the PCG.
pub(crate) mod abstraction;
pub mod action;
pub mod borrow_pcg_edge;
pub mod borrow_pcg_expansion;
pub(crate) mod domain;
pub mod edge;
pub mod edge_data;
pub mod graph;
pub(crate) mod has_pcs_elem;
pub mod path_condition;
pub mod region_projection;
pub mod state;
pub mod unblock_graph;
pub(crate) mod visitor;

pub use domain::AbstractionInputTarget;
pub use domain::AbstractionOutputTarget;
