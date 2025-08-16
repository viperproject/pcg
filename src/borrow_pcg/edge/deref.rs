use crate::{
    HasCompilerCtxt,
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        edge_data::{EdgeData, LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, LabelNodeContext, PlaceLabeller,
        },
        region_projection::{LifetimeProjectionLabel, LocalLifetimeProjection},
    },
    pcg::{LocalNodeLike, PCGNodeLike},
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, Place, SnapshotLocation, display::DisplayWithCompilerCtxt,
        maybe_old::MaybeLabelledPlace, validity::HasValidityCheck,
    },
};

/// A PCG Hyperedge from the a reference-typed place, and a lifetime projection
/// to the dereferenced place.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct DerefEdge<'tcx> {
    pub(crate) blocked_place: MaybeLabelledPlace<'tcx>,
    pub(crate) deref_place: MaybeLabelledPlace<'tcx>,
    /// The lifetime projection that is blocked in this edge. In general, this
    /// will not be labelled if `blocked_place` is a shared reference, and
    /// labelled with the MIR location of the dereference if `blocked_place` is
    /// a mutable reference.
    pub(crate) blocked_lifetime_projection: LocalLifetimeProjection<'tcx>,
}

impl<'tcx> DerefEdge<'tcx> {
    pub fn blocked_place(self) -> MaybeLabelledPlace<'tcx> {
        self.blocked_place
    }
    pub fn deref_place(self) -> MaybeLabelledPlace<'tcx> {
        self.deref_place
    }

    pub(crate) fn new<'a>(
        place: Place<'tcx>,
        blocked_lifetime_projection_label: Option<SnapshotLocation>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        let blocked_lifetime_projection = place
            .base_lifetime_projection(ctxt)
            .unwrap()
            .with_label(blocked_lifetime_projection_label.map(|l| l.into()), ctxt)
            .into();
        let blocked_place_label: Option<SnapshotLocation> = None;
        DerefEdge {
            blocked_place: MaybeLabelledPlace::new(place, blocked_place_label),
            deref_place: place.project_deref(ctxt).into(),
            blocked_lifetime_projection,
        }
    }
}

impl<'tcx> HasValidityCheck<'tcx> for DerefEdge<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.blocked_place.check_validity(ctxt)?;
        self.deref_place.check_validity(ctxt)?;
        self.blocked_lifetime_projection.check_validity(ctxt)?;
        if self.deref_place.last_projection().unwrap().1 != mir::PlaceElem::Deref {
            return Err("Deref edge deref place must end with a deref projection".to_string());
        }
        Ok(())
    }
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for DerefEdge<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        format!(
            "{{{}}} -> {{{}}}",
            self.blocked_place.to_short_string(ctxt),
            self.deref_place.to_short_string(ctxt)
        )
    }
}

impl<'tcx> LabelLifetimeProjection<'tcx> for DerefEdge<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        location: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        if predicate.matches(self.blocked_lifetime_projection.into(), ctxt) {
            self.blocked_lifetime_projection =
                self.blocked_lifetime_projection.with_label(location, ctxt);
            LabelLifetimeProjectionResult::Changed
        } else {
            LabelLifetimeProjectionResult::Unchanged
        }
    }
}

impl<'tcx> LabelEdgePlaces<'tcx> for DerefEdge<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let blocked_places = vec![
            &mut self.blocked_place,
            &mut self.blocked_lifetime_projection.base,
        ];
        let mut changed = false;
        for blocked_place in blocked_places {
            if let MaybeLabelledPlace::Current(place) = blocked_place {
                if predicate.applies_to(*place, LabelNodeContext::Other, ctxt) {
                    *blocked_place =
                        MaybeLabelledPlace::new(*place, Some(labeller.place_label(*place, ctxt)));
                    changed = true;
                }
            }
        }
        changed
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if let MaybeLabelledPlace::Current(place) = self.deref_place {
            if predicate.applies_to(place, LabelNodeContext::TargetOfExpansion, ctxt) {
                self.deref_place =
                    MaybeLabelledPlace::new(place, Some(labeller.place_label(place, ctxt)));
                return true;
            }
        }
        false
    }
}

impl<'tcx> EdgeData<'tcx> for DerefEdge<'tcx> {
    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: crate::utils::CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = crate::pcg::PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(
            vec![
                self.blocked_place.to_pcg_node(ctxt),
                self.blocked_lifetime_projection.to_pcg_node(ctxt),
            ]
            .into_iter(),
        )
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        ctxt: crate::utils::CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<
        dyn std::iter::Iterator<Item = crate::borrow_pcg::borrow_pcg_edge::LocalNode<'tcx>> + 'slf,
    >
    where
        'tcx: 'mir,
    {
        Box::new(vec![self.deref_place.to_local_node(ctxt)].into_iter())
    }
}
