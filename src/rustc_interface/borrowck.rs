pub use super::rs_borrowck::consumers::*;

pub use super::rs_borrowck::provide;

#[rustversion::since(2025-03-02)]
pub type LocationTable = PoloniusLocationTable;
