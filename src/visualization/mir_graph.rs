use crate::{
    rustc_interface,
    utils::{display::DisplayWithCompilerCtxt, CompilerCtxt, Place},
};
use serde_derive::Serialize;
use std::{
    fs::File,
    io::{self},
};

use rustc_interface::middle::mir::{
    self, BinOp, Local, Operand, Rvalue, Statement, TerminatorKind, UnwindAction,
};

#[derive(Serialize)]
struct MirGraph {
    nodes: Vec<MirNode>,
    edges: Vec<MirEdge>,
}

#[derive(Serialize)]
struct MirStmt {
    stmt: String,
    loans_invalidated_start: Vec<String>,
    loans_invalidated_mid: Vec<String>,
}

#[derive(Serialize)]
struct MirNode {
    id: String,
    block: usize,
    stmts: Vec<MirStmt>,
    terminator: String,
}

#[derive(Serialize)]
struct MirEdge {
    source: String,
    target: String,
    label: String,
}

fn format_bin_op(op: &BinOp) -> String {
    match op {
        BinOp::Add => "+".to_string(),
        BinOp::Sub => "-".to_string(),
        BinOp::Mul => "*".to_string(),
        BinOp::Div => "/".to_string(),
        BinOp::Rem => "%".to_string(),
        BinOp::AddUnchecked => todo!(),
        BinOp::SubUnchecked => todo!(),
        BinOp::MulUnchecked => todo!(),
        BinOp::BitXor => "^".to_string(),
        BinOp::BitAnd => "&".to_string(),
        BinOp::BitOr => "|".to_string(),
        BinOp::Shl => "<<".to_string(),
        BinOp::ShlUnchecked => "<<".to_string(),
        BinOp::Shr => ">>".to_string(),
        BinOp::ShrUnchecked => ">>".to_string(),
        BinOp::Eq => "==".to_string(),
        BinOp::Lt => "<".to_string(),
        BinOp::Le => "<=".to_string(),
        BinOp::Ne => "!=".to_string(),
        BinOp::Ge => ">=".to_string(),
        BinOp::Gt => ">".to_string(),
        BinOp::Offset => todo!(),
        BinOp::Cmp => todo!(),
        BinOp::AddWithOverflow => "+".to_string(),
        BinOp::SubWithOverflow => "-".to_string(),
        BinOp::MulWithOverflow => "*".to_string(),
    }
}

fn format_local<'tcx>(local: &Local, repacker: CompilerCtxt<'_, 'tcx, '_>) -> String {
    let place: Place<'tcx> = (*local).into();
    place.to_short_string(repacker)
}

fn format_place<'tcx>(place: &mir::Place<'tcx>, repacker: CompilerCtxt<'_, 'tcx, '_>) -> String {
    let place: Place<'tcx> = (*place).into();
    place.to_short_string(repacker)
}

fn format_operand<'tcx>(operand: &Operand<'tcx>, repacker: CompilerCtxt<'_, 'tcx, '_>) -> String {
    match operand {
        Operand::Copy(p) => format_place(p, repacker),
        Operand::Move(p) => format!("move {}", format_place(p, repacker)),
        Operand::Constant(c) => format!("{}", c),
    }
}

fn format_rvalue<'tcx>(rvalue: &Rvalue<'tcx>, repacker: CompilerCtxt<'_, 'tcx, '_>) -> String {
    match rvalue {
        Rvalue::Use(operand) => format_operand(operand, repacker),
        Rvalue::Repeat(operand, c) => format!("repeat {} {}", format_operand(operand, repacker), c),
        Rvalue::Ref(_region, kind, place) => {
            let kind = match kind {
                mir::BorrowKind::Shared => "",
                mir::BorrowKind::Mut { .. } => "mut",
                mir::BorrowKind::Fake(_) => "fake",
            };
            format!("&{} {}", kind, format_place(place, repacker))
        }
        Rvalue::RawPtr(kind, place) => {
            let kind = match kind {
                mir::Mutability::Mut => "mut",
                mir::Mutability::Not => "const",
            };
            format!("*{} {}", kind, format_place(place, repacker))
        }
        Rvalue::ThreadLocalRef(_) => todo!(),
        Rvalue::Len(x) => format!("len({})", format_place(x, repacker)),
        Rvalue::Cast(_, operand, ty) => format!("{} as {}", format_operand(operand, repacker), ty),
        Rvalue::BinaryOp(op, box (lhs, rhs)) => {
            format!(
                "{} {} {}",
                format_operand(lhs, repacker),
                format_bin_op(op),
                format_operand(rhs, repacker)
            )
        }
        Rvalue::NullaryOp(op, _) => format!("{:?}", op),
        Rvalue::UnaryOp(op, val) => {
            format!("{:?} {}", op, format_operand(val, repacker))
        }
        Rvalue::Discriminant(place) => format!("Discriminant({})", format_place(place, repacker)),
        Rvalue::Aggregate(kind, ops) => {
            format!(
                "Aggregate {:?} {}",
                kind,
                ops.iter()
                    .map(|op| format_operand(op, repacker))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        Rvalue::ShallowInitBox(operand, _) => format!("Box({})", format_operand(operand, repacker)),
        Rvalue::CopyForDeref(place) => format!("CopyForDeref({})", format_place(place, repacker)),
    }
}
fn format_terminator<'tcx>(
    terminator: &TerminatorKind<'tcx>,
    repacker: CompilerCtxt<'_, 'tcx, '_>,
) -> String {
    match terminator {
        TerminatorKind::Call {
            func,
            args,
            destination,
            target: _,
            unwind: _,
            call_source: _,
            fn_span: _,
        } => {
            format!(
                "{} = {}({})",
                format_place(destination, repacker),
                format_operand(func, repacker),
                args.iter()
                    .map(|arg| format_operand(&arg.node, repacker))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        _ => format!("{:?}", terminator),
    }
}

fn format_stmt<'tcx>(stmt: &Statement<'tcx>, repacker: CompilerCtxt<'_, 'tcx, '_>) -> String {
    match &stmt.kind {
        mir::StatementKind::Assign(box (place, rvalue)) => {
            format!(
                "{} = {}",
                format_place(place, repacker),
                format_rvalue(rvalue, repacker)
            )
        }
        mir::StatementKind::FakeRead(box (_, place)) => {
            format!("FakeRead({})", format_place(place, repacker))
        }
        mir::StatementKind::SetDiscriminant {
            place,
            variant_index,
        } => format!(
            "SetDiscriminant({} {:?})",
            format_place(place, repacker),
            variant_index
        ),
        mir::StatementKind::Deinit(_) => todo!(),
        mir::StatementKind::StorageLive(local) => {
            format!("StorageLive({})", format_local(local, repacker))
        }
        mir::StatementKind::StorageDead(local) => {
            format!("StorageDead({})", format_local(local, repacker))
        }
        mir::StatementKind::Retag(_, _) => todo!(),
        mir::StatementKind::PlaceMention(place) => {
            format!("PlaceMention({})", format_place(place, repacker))
        }
        mir::StatementKind::AscribeUserType(_, _) => "AscribeUserType(...)".to_string(),
        _ => todo!(),
    }
}

fn mk_mir_graph(ctxt: CompilerCtxt<'_, '_, '_>) -> MirGraph {
    let mut nodes = Vec::new();
    let mut edges = Vec::new();

    for (bb, data) in ctxt.body().basic_blocks.iter_enumerated() {
        let stmts = data.statements.iter().enumerate().map(|(idx, stmt)| {
            let stmt = format_stmt(stmt, ctxt);
            let bc = ctxt.bc;
            let invalidated_at = &bc.input_facts().loan_invalidated_at;
            let location = mir::Location {
                block: bb,
                statement_index: idx,
            };
            let loans_invalidated_start = invalidated_at
                .iter()
                .filter_map(|(point, idx)| {
                    if *point == bc.location_table().start_index(location) {
                        let borrow_region = bc.borrow_set()[*idx].region();
                        Some(format!("{:?}", borrow_region))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            let loans_invalidated_mid = invalidated_at
                .iter()
                .filter_map(|(point, idx)| {
                    if *point == bc.location_table().mid_index(location) {
                        let borrow_region = bc.borrow_set()[*idx].region();
                        Some(format!("{:?}", borrow_region))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            MirStmt {
                stmt,
                loans_invalidated_start,
                loans_invalidated_mid,
            }
        });

        let terminator = format_terminator(&data.terminator().kind, ctxt);

        nodes.push(MirNode {
            id: format!("{:?}", bb),
            block: bb.as_usize(),
            stmts: stmts.collect(),
            terminator,
        });

        match &data.terminator().kind {
            TerminatorKind::Goto { target } => {
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", target),
                    label: "goto".to_string(),
                });
            }
            TerminatorKind::SwitchInt { discr: _, targets } => {
                for (val, target) in targets.iter() {
                    edges.push(MirEdge {
                        source: format!("{:?}", bb),
                        target: format!("{:?}", target),
                        label: format!("{}", val),
                    });
                }
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", targets.otherwise()),
                    label: "otherwise".to_string(),
                });
            }
            TerminatorKind::UnwindResume => {}
            TerminatorKind::UnwindTerminate(_) => todo!(),
            TerminatorKind::Return => {}
            TerminatorKind::Unreachable => {}
            TerminatorKind::Drop {
                place: _,
                target,
                unwind: _,
                replace: _,
            } => {
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", target),
                    label: "drop".to_string(),
                });
            }
            TerminatorKind::Call {
                func: _,
                args: _,
                destination: _,
                target,
                unwind,
                call_source: _,
                fn_span: _,
            } => {
                if let Some(target) = target {
                    edges.push(MirEdge {
                        source: format!("{:?}", bb),
                        target: format!("{:?}", target),
                        label: "call".to_string(),
                    });
                    match unwind {
                        UnwindAction::Continue => todo!(),
                        UnwindAction::Unreachable => todo!(),
                        UnwindAction::Terminate(_) => todo!(),
                        UnwindAction::Cleanup(cleanup) => {
                            edges.push(MirEdge {
                                source: format!("{:?}", bb),
                                target: format!("{:?}", cleanup),
                                label: "unwind".to_string(),
                            });
                        }
                    }
                }
            }
            TerminatorKind::Assert {
                cond: _,
                expected: _,
                msg: _,
                target,
                unwind,
            } => {
                match unwind {
                    UnwindAction::Continue => todo!(),
                    UnwindAction::Unreachable => todo!(),
                    UnwindAction::Terminate(_) => todo!(),
                    UnwindAction::Cleanup(cleanup) => {
                        edges.push(MirEdge {
                            source: format!("{:?}", bb),
                            target: format!("{:?}", cleanup),
                            label: "unwind".to_string(),
                        });
                    }
                }
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", target),
                    label: "success".to_string(),
                });
            }
            TerminatorKind::Yield {
                value: _,
                resume: _,
                resume_arg: _,
                drop: _,
            } => todo!(),
            TerminatorKind::FalseEdge {
                real_target,
                imaginary_target: _,
            } => {
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", real_target),
                    label: "real".to_string(),
                });
            }
            TerminatorKind::FalseUnwind {
                real_target,
                unwind: _,
            } => {
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", real_target),
                    label: "real".to_string(),
                });
            }
            TerminatorKind::InlineAsm { .. } => todo!(),
            TerminatorKind::CoroutineDrop => todo!(),
            _ => todo!(),
        }
    }

    MirGraph { nodes, edges }
}
pub(crate) fn generate_json_from_mir(path: &str, ctxt: CompilerCtxt<'_, '_, '_>) -> io::Result<()> {
    let mir_graph = mk_mir_graph(ctxt);
    let mut file = File::create(path)?;
    serde_json::to_writer(&mut file, &mir_graph)?;
    Ok(())
}
