use crate::{
    rustc_interface,
    utils::{display::DisplayWithRepacker, Place, PlaceRepacker},
};
use serde_derive::Serialize;
use std::{
    fs::File,
    io::{self},
};

use rustc_interface::middle::{
    mir::{self, BinOp, Body, Local, Operand, Rvalue, Statement, TerminatorKind, UnwindAction},
    ty::TyCtxt,
};

#[derive(Serialize)]
struct MirGraph {
    nodes: Vec<MirNode>,
    edges: Vec<MirEdge>,
}

#[derive(Serialize)]
struct MirNode {
    id: String,
    block: usize,
    stmts: Vec<String>,
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
        BinOp::BitXor => todo!(),
        BinOp::BitAnd => "&".to_string(),
        BinOp::BitOr => todo!(),
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

fn format_local<'tcx>(local: &Local, repacker: PlaceRepacker<'_, 'tcx>) -> String {
    let place: Place<'tcx> = (*local).into();
    place.to_short_string(repacker)
}

fn format_place<'tcx>(place: &mir::Place<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> String {
    let place: Place<'tcx> = (*place).into();
    place.to_short_string(repacker)
}

fn format_operand<'tcx>(operand: &Operand<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> String {
    match operand {
        Operand::Copy(p) => format_place(p, repacker),
        Operand::Move(p) => format!("move {}", format_place(p, repacker)),
        Operand::Constant(c) => format!("{}", c),
    }
}

fn format_rvalue<'tcx>(rvalue: &Rvalue<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> String {
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
        Rvalue::Len(x) => format!("len({})", format_place(&x, repacker)),
        Rvalue::Cast(_, operand, ty) => format!("{} as {}", format_operand(operand, repacker), ty),
        Rvalue::BinaryOp(op, box (lhs, rhs)) => {
            format!(
                "{} {} {}",
                format_operand(lhs, repacker),
                format_bin_op(op),
                format_operand(rhs, repacker)
            )
        }
        Rvalue::NullaryOp(_, _) => todo!(),
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
        Rvalue::ShallowInitBox(_, _) => todo!(),
        Rvalue::CopyForDeref(_) => todo!(),
    }
}
fn format_terminator<'tcx>(
    terminator: &TerminatorKind<'tcx>,
    repacker: PlaceRepacker<'_, 'tcx>,
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

fn format_stmt<'tcx>(stmt: &Statement<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> String {
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
            place: _,
            variant_index: _,
        } => todo!(),
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
        mir::StatementKind::AscribeUserType(_, _) => {
            format!("AscribeUserType(...)")
        }
        _ => todo!(),
    }
}

fn mk_mir_graph<'mir, 'tcx>(tcx: TyCtxt<'tcx>, body: &'mir Body<'tcx>) -> MirGraph {
    let mut nodes = Vec::new();
    let mut edges = Vec::new();

    let repacker = PlaceRepacker::new(body, tcx);

    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let stmts = data
            .statements
            .iter()
            .map(|stmt| format_stmt(stmt, repacker));

        let terminator = format_terminator(&data.terminator().kind, repacker);

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
                            label: format!("unwind"),
                        });
                    }
                }
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", target),
                    label: format!("success"),
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
pub fn generate_json_from_mir<'mir, 'tcx>(
    path: &str,
    tcx: TyCtxt<'tcx>,
    body: &'mir Body<'tcx>,
) -> io::Result<()> {
    let mir_graph = mk_mir_graph(tcx, body);
    let mut file = File::create(path)?;
    serde_json::to_writer(&mut file, &mir_graph)?;
    Ok(())
}
