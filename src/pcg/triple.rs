// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::{
    self, BorrowKind, Local, Location, MutBorrowKind, Operand, RETURN_PLACE, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind,
};

#[rustversion::before(2025-03-02)]
use crate::rustc_interface::middle::mir::Mutability;

#[rustversion::since(2025-03-02)]
use crate::rustc_interface::middle::mir::RawPtrKind;

use crate::utils::visitor::FallableVisitor;
use crate::{
    error::{PcgError, PcgUnsupportedError},
    pcg::CapabilityKind,
    utils::{CompilerCtxt, Place, display::DisplayWithCompilerCtxt},
};

#[derive(Debug, Clone, Copy)]
pub(crate) struct Triple<'tcx> {
    pre: PlaceCondition<'tcx>,
    post: Option<PlaceCondition<'tcx>>,
}

impl<'tcx> Triple<'tcx> {
    pub(crate) fn new(pre: PlaceCondition<'tcx>, post: Option<PlaceCondition<'tcx>>) -> Self {
        Self { pre, post }
    }

    pub fn pre(self) -> PlaceCondition<'tcx> {
        self.pre
    }
    pub fn post(self) -> Option<PlaceCondition<'tcx>> {
        self.post
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum PlaceCondition<'tcx> {
    /// Similar to read capability, but indicates that the place is expanded as part of a two-phase borrow.
    /// For example, if `let y = &mut *x` is a two-phase borrow, then we have `ExpandTwoPhase(*x)` as condition.
    /// This distinction is relevant for expanding lifetime projections: the lifetime projection base of *x will
    /// be labelled, similarly to the situation where the borrow was exclusive.
    ExpandTwoPhase(Place<'tcx>),
    Capability(Place<'tcx>, CapabilityKind),
    RemoveCapability(Place<'tcx>),
    AllocateOrDeallocate(Local),
    Unalloc(Local),
    Return,
}

impl<'tcx> PlaceCondition<'tcx> {
    fn new<T: Into<Place<'tcx>>>(place: T, capability: CapabilityKind) -> PlaceCondition<'tcx> {
        PlaceCondition::Capability(place.into(), capability)
    }

    fn exclusive<T: Into<Place<'tcx>>>(
        place: T,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> PlaceCondition<'tcx> {
        let place = place.into();
        pcg_validity_assert!(
            !place.projects_shared_ref(repacker),
            "Cannot get exclusive on projection of shared ref {}",
            place.to_short_string(repacker)
        );
        Self::new(place, CapabilityKind::Exclusive)
    }

    fn write<T: Into<Place<'tcx>>>(place: T) -> PlaceCondition<'tcx> {
        Self::new(place, CapabilityKind::Write)
    }

    fn read<T: Into<Place<'tcx>>>(place: T) -> PlaceCondition<'tcx> {
        Self::new(place, CapabilityKind::Read)
    }
}

pub(crate) struct TripleWalker<'a, 'tcx: 'a> {
    /// Evaluate all Operands/Rvalues
    pub(crate) operand_triples: Vec<Triple<'tcx>>,
    /// Evaluate all other statements/terminators
    pub(crate) main_triples: Vec<Triple<'tcx>>,
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
}

impl<'a, 'tcx> TripleWalker<'a, 'tcx> {
    pub(crate) fn new(repacker: CompilerCtxt<'a, 'tcx>) -> Self {
        Self {
            operand_triples: Vec::new(),
            main_triples: Vec::new(),
            ctxt: repacker,
        }
    }
}
impl<'tcx> FallableVisitor<'tcx> for TripleWalker<'_, 'tcx> {
    fn visit_operand_fallable(
        &mut self,
        operand: &mir::Operand<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        self.super_operand_fallable(operand, location)?;
        let triple = match *operand {
            Operand::Copy(place) => Triple {
                pre: PlaceCondition::read(place),
                post: None,
            },
            Operand::Move(place) => Triple {
                pre: PlaceCondition::exclusive(place, self.ctxt),
                post: Some(PlaceCondition::write(place)),
            },
            Operand::Constant(..) => return Ok(()),
        };
        self.operand_triples.push(triple);
        Ok(())
    }

    #[allow(unreachable_patterns)]
    fn visit_rvalue_fallable(
        &mut self,
        rvalue: &mir::Rvalue<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        self.super_rvalue_fallable(rvalue, location)?;
        use Rvalue::*;
        let triple = match rvalue {
            Use(_)
            | Repeat(_, _)
            | ThreadLocalRef(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Aggregate(_, _)
            | ShallowInitBox(_, _) => return Ok(()),

            &Ref(_, kind, place) => match kind {
                BorrowKind::Shared => Triple::new(
                    PlaceCondition::read(place),
                    Some(PlaceCondition::read(place)),
                ),
                BorrowKind::Mut {
                    kind: MutBorrowKind::TwoPhaseBorrow,
                } => Triple::new(
                    PlaceCondition::ExpandTwoPhase(place.into()),
                    Some(PlaceCondition::read(place)),
                ),
                BorrowKind::Fake(..) => return Ok(()),
                BorrowKind::Mut { .. } => Triple::new(
                    PlaceCondition::exclusive(place, self.ctxt),
                    Some(PlaceCondition::RemoveCapability(place.into())),
                ),
            },
            &RawPtr(mutbl, place) => {
                #[rustversion::since(2025-03-02)]
                let pre = if matches!(mutbl, RawPtrKind::Mut) {
                    PlaceCondition::exclusive(place, self.ctxt)
                } else {
                    PlaceCondition::read(place)
                };
                #[rustversion::before(2025-03-02)]
                let pre = if matches!(mutbl, Mutability::Mut) {
                    PlaceCondition::exclusive(place, self.ctxt)
                } else {
                    PlaceCondition::read(place)
                };
                Triple::new(pre, None)
            }
            &Len(place) | &Discriminant(place) | &CopyForDeref(place) => {
                Triple::new(PlaceCondition::read(place), None)
            }
            _ => todo!(),
        };
        self.operand_triples.push(triple);
        Ok(())
    }

    fn visit_statement_fallable(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.super_statement_fallable(statement, location)?;
        use StatementKind::*;
        let t = match statement.kind {
            Assign(box (place, ref rvalue)) => Triple {
                pre: PlaceCondition::write(place),
                post: rvalue
                    .capability()
                    .map(|cap| PlaceCondition::new(place, cap)),
            },
            FakeRead(box (_, place)) => Triple {
                pre: PlaceCondition::read(place),
                post: None,
            },
            // Looking into `rustc` it seems that `PlaceMention` is effectively ignored.
            PlaceMention(_) => return Ok(()),
            SetDiscriminant { box place, .. } => Triple {
                pre: PlaceCondition::exclusive(place, self.ctxt),
                post: None,
            },
            Deinit(box place) => Triple {
                pre: PlaceCondition::exclusive(place, self.ctxt),
                post: Some(PlaceCondition::write(place)),
            },
            StorageLive(local) => Triple {
                pre: PlaceCondition::Unalloc(local),
                post: Some(PlaceCondition::AllocateOrDeallocate(local)),
            },
            StorageDead(local) => Triple {
                pre: PlaceCondition::AllocateOrDeallocate(local),
                post: Some(PlaceCondition::Unalloc(local)),
            },
            Retag(_, box place) => Triple {
                pre: PlaceCondition::exclusive(place, self.ctxt),
                post: None,
            },
            _ => return Ok(()),
        };
        self.main_triples.push(t);
        Ok(())
    }

    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        self.super_terminator_fallable(terminator, location)?;
        use TerminatorKind::*;
        let t = match &terminator.kind {
            Goto { .. }
            | SwitchInt { .. }
            | UnwindResume
            | UnwindTerminate(_)
            | Unreachable
            | CoroutineDrop
            | Assert { .. }
            | FalseEdge { .. }
            | FalseUnwind { .. } => return Ok(()),
            Return => Triple {
                pre: PlaceCondition::Return,
                post: Some(PlaceCondition::write(RETURN_PLACE)),
            },
            &Drop { place, .. } => Triple {
                pre: PlaceCondition::write(place),
                post: None,
            },
            &Call { destination, .. } => Triple {
                pre: PlaceCondition::write(destination),
                post: Some(PlaceCondition::exclusive(destination, self.ctxt)),
            },
            &Yield { resume_arg, .. } => Triple {
                pre: PlaceCondition::write(resume_arg),
                post: Some(PlaceCondition::exclusive(resume_arg, self.ctxt)),
            },
            InlineAsm { .. } => {
                return Err(PcgError::unsupported(PcgUnsupportedError::InlineAssembly));
            }
            _ => todo!("{terminator:?}"),
        };
        self.main_triples.push(t);
        Ok(())
    }

    fn visit_place_fallable(
        &mut self,
        place: Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) -> Result<(), PcgError> {
        if place.contains_unsafe_deref(self.ctxt) {
            return Err(PcgError::unsupported(PcgUnsupportedError::DerefUnsafePtr));
        }
        Ok(())
    }
}

trait ProducesCapability {
    fn capability(&self) -> Option<CapabilityKind>;
}

impl ProducesCapability for Rvalue<'_> {
    #[allow(unreachable_patterns)]
    fn capability(&self) -> Option<CapabilityKind> {
        use Rvalue::*;
        match self {
            Ref(_, BorrowKind::Fake(_), _) => None,
            Use(_)
            | Repeat(_, _)
            | Ref(_, _, _)
            | RawPtr(_, _)
            | ThreadLocalRef(_)
            | Len(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Discriminant(_)
            | Aggregate(_, _)
            | CopyForDeref(_) => Some(CapabilityKind::Exclusive),
            ShallowInitBox(_, _) => Some(CapabilityKind::ShallowExclusive),
            _ => todo!(),
        }
    }
}
