use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::has_pcs_elem::{default_make_place_old, HasPcgElems, MakePlaceOld};
use crate::borrow_pcg::latest::Latest;
use crate::borrow_pcg::region_projection::LocalRegionProjection;
use crate::combined_pcs::{LocalNodeLike, PCGNode, PCGNodeLike};
use crate::pcg_validity_assert;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::utils::display::DisplayWithRepacker;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::{Place, PlaceRepacker};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FunctionCallRegionCoupling<'tcx> {
    pub(crate) inputs: Vec<LocalRegionProjection<'tcx>>,
    pub(crate) outputs: Vec<LocalRegionProjection<'tcx>>,
}

impl <'tcx> FunctionCallRegionCoupling<'tcx> {
    pub fn inputs(&self) -> &[LocalRegionProjection<'tcx>] {
        &self.inputs
    }
    pub fn outputs(&self) -> &[LocalRegionProjection<'tcx>] {
        &self.outputs
    }

    pub fn num_coupled_nodes(&self) -> usize {
        self.inputs.len()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for FunctionCallRegionCoupling<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        for input in self.inputs.iter() {
            input.check_validity(repacker)?;
        }
        for output in self.outputs.iter() {
            output.check_validity(repacker)?;
        }
        Ok(())
    }
}

impl<'tcx> MakePlaceOld<'tcx> for FunctionCallRegionCoupling<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        default_make_place_old(self, place, latest, repacker)
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for FunctionCallRegionCoupling<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.inputs
            .iter_mut()
            .flat_map(|rp| rp.pcg_elems())
            .collect::<Vec<_>>()
            .into_iter()
            .chain(
                self.outputs
                    .iter_mut()
                    .flat_map(|rp| rp.pcg_elems())
                    .collect::<Vec<_>>(),
            )
            .collect()
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for FunctionCallRegionCoupling<'tcx> {
    fn to_short_string(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "FunctionCallRegionCoupling({:?}, {:?})",
            self.inputs, self.outputs
        )
    }
}

impl<'tcx> FunctionCallRegionCoupling<'tcx> {
    pub(crate) fn new(
        inputs: FxHashSet<LocalRegionProjection<'tcx>>,
        outputs: FxHashSet<LocalRegionProjection<'tcx>>,
    ) -> Self {
        pcg_validity_assert!(inputs.len() == outputs.len());
        Self {
            inputs: inputs.into_iter().collect(),
            outputs: outputs.into_iter().collect(),
        }
    }
}

impl<'tcx> EdgeData<'tcx> for FunctionCallRegionCoupling<'tcx> {
    fn blocked_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.inputs
            .iter()
            .map(|rp| rp.to_pcg_node(repacker))
            .collect()
    }

    fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        self.outputs
            .iter()
            .map(|rp| rp.to_local_node(repacker))
            .collect()
    }
}
