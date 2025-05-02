pub use super::rs_borrowck::consumers::*;

pub use super::rs_borrowck::provide;

#[rustversion::before(2024-12-14)]
pub use super::rs_borrowck::borrow_set::*;

#[rustversion::since(2025-03-02)]
pub (crate) type LocationTable = PoloniusLocationTable;
