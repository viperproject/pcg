use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPCGEdgeRef, LocalNode},
        edge::{kind::BorrowPCGEdgeKind, outlives::BorrowFlowEdgeKind},
        edge_data::EdgeData,
    },
    pcg::{LocalNodeLike, PCGNode, PCGNodeLike},
    rustc_interface::data_structures::fx::FxHashSet,
    utils::{CompilerCtxt, HasPlace},
};

use super::BorrowsGraph;

#[derive(Eq, PartialEq, Hash, Debug)]
struct Alias<'tcx> {
    node: PCGNode<'tcx>,
    exact_alias: bool,
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn ancestor_edges<'graph, 'mir: 'graph, 'bc: 'graph, C: Copy>(
        &'graph self,
        node: LocalNode<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx, C>,
    ) -> FxHashSet<BorrowPCGEdgeRef<'tcx, 'graph>> {
        let mut result: FxHashSet<BorrowPCGEdgeRef<'tcx, 'graph>> = FxHashSet::default();
        let mut stack = vec![node];
        let mut seen: FxHashSet<PCGNode<'tcx>> = FxHashSet::default();
        while let Some(node) = stack.pop() {
            if seen.insert(node.into()) {
                for edge in self.edges_blocked_by(node, repacker) {
                    result.insert(edge);
                    for node in edge.blocked_nodes(repacker) {
                        if let Some(local_node) = node.try_to_local_node(repacker) {
                            stack.push(local_node);
                        }
                    }
                }
            }
        }
        result
    }
    pub(crate) fn aliases<C: Copy>(
        &self,
        node: LocalNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        let mut result: FxHashSet<PCGNode<'tcx>> = FxHashSet::default();
        result.insert(node.into());
        let mut stack = vec![node];
        while let Some(node) = stack.pop() {
            for alias in self.aliases_all_projections(node, repacker) {
                if result.insert(alias) {
                    if let Some(local_node) = alias.try_to_local_node(repacker) {
                        stack.push(local_node);
                    }
                }
            }
        }
        result
    }

    pub(crate) fn aliases_all_projections<C: Copy>(
        &self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        let mut results: FxHashSet<Alias<'tcx>> = FxHashSet::default();
        for (place, proj) in node.iter_projections(ctxt) {
            results.insert(Alias {
                node: place.into(),
                exact_alias: true,
            });
            let candidates: Vec<_> = results.drain().collect();
            for alias in candidates {
                if !alias.exact_alias {
                    continue;
                }
                let local_node = if let Some(local_node) = alias.node.try_to_local_node(ctxt) {
                    local_node
                } else {
                    continue;
                };
                let local_node = if let Ok(n) = local_node.project_deeper(proj, ctxt) {
                    n
                } else {
                    continue;
                };
                results.extend(self.direct_aliases(
                    local_node,
                    ctxt,
                    &mut FxHashSet::default(),
                    true,
                ));
                if let PCGNode::Place(p) = local_node
                    && let Some(rp) = p.deref_to_rp(ctxt)
                {
                    for node in self.nodes(ctxt) {
                        if let Some(PCGNode::RegionProjection(p)) = node.try_to_local_node(ctxt) {
                            if p.base() == rp.base() && p.region_idx == rp.region_idx {
                                results.extend(self.direct_aliases(
                                    p.to_local_node(ctxt),
                                    ctxt,
                                    &mut FxHashSet::default(),
                                    true,
                                ));
                            }
                        }
                    }
                }
            }
        }
        results.into_iter().map(|a| a.node).collect()
    }

    #[tracing::instrument(skip(self, repacker, seen, direct))]
    fn direct_aliases<C: Copy>(
        &self,
        node: LocalNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
        seen: &mut FxHashSet<PCGNode<'tcx>>,
        direct: bool,
    ) -> FxHashSet<Alias<'tcx>> {
        let mut result = FxHashSet::default();
        result.insert(Alias {
            node: node.into(),
            exact_alias: direct,
        });

        let extend = |blocked: PCGNode<'tcx>,
                      seen: &mut FxHashSet<PCGNode<'tcx>>,
                      result: &mut FxHashSet<Alias<'tcx>>,
                      exact_alias: bool| {
            if seen.insert(blocked) {
                result.insert(Alias {
                    node: blocked,
                    exact_alias,
                });
                if let Some(local_node) = blocked.try_to_local_node(repacker) {
                    result.extend(self.direct_aliases(local_node, repacker, seen, exact_alias));
                }
            }
        };

        for edge in self.edges_blocked_by(node, repacker) {
            match edge.kind {
                BorrowPCGEdgeKind::Borrow(borrow_edge) => {
                    let blocked = borrow_edge.blocked_place();
                    extend(blocked.into(), seen, &mut result, direct);
                }
                BorrowPCGEdgeKind::BorrowPCGExpansion(e) => {
                    for node in e.blocked_nodes(repacker) {
                        if let PCGNode::RegionProjection(p) = node {
                            extend(
                                p.to_pcg_node(repacker),
                                seen,
                                &mut result,
                                e.is_deref(repacker),
                            );
                        }
                    }
                }
                BorrowPCGEdgeKind::Abstraction(abstraction_type) => {
                    for input in abstraction_type.inputs() {
                        extend(input.to_pcg_node(repacker), seen, &mut result, false);
                    }
                }
                BorrowPCGEdgeKind::BorrowFlow(outlives) => match &outlives.kind {
                    BorrowFlowEdgeKind::Move => {
                        extend(
                            outlives.long().to_pcg_node(repacker),
                            seen,
                            &mut result,
                            true,
                        );
                    }
                    BorrowFlowEdgeKind::BorrowOutlives { regions_equal }
                        if !regions_equal || direct => {}
                    _ => {
                        extend(
                            outlives.long().to_pcg_node(repacker),
                            seen,
                            &mut result,
                            false,
                        );
                    }
                },
            }
        }
        result
    }
}

#[cfg(test)]
#[test]
fn test_aliases() {
    use rustc_utils::test_utils::Placer;

    use crate::borrow_pcg::borrow_checker::r#impl::BorrowCheckerImpl;
    use crate::free_pcs::PcgLocation;
    use crate::rustc_interface::middle::mir::{self, START_BLOCK};
    use crate::rustc_interface::span::Symbol;

    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr)
        .init();

    use crate::{run_pcg, BodyAndBorrows, PcgOutput};

    fn check_all_statements<'mir, 'tcx>(
        body: &'mir mir::Body<'tcx>,
        pcg: &mut PcgOutput<'mir, 'tcx>,
        f: impl Fn(mir::Location, &PcgLocation<'tcx>),
    ) {
        for block in body.basic_blocks.indices() {
            let stmts_option = pcg.get_all_for_bb(block).unwrap();
            let stmts = if let Some(stmts) = stmts_option {
                stmts
            } else {
                continue;
            };
            for (i, stmt) in stmts.statements.iter().enumerate() {
                let location = mir::Location {
                    block,
                    statement_index: i,
                };
                f(location, stmt);
            }
        }
    }
    // interior_mutability_observable
    let input = r#"
        use std::cell::RefCell;
        fn main() {
            let x = RefCell::new(0);
            *x.borrow_mut() = 1;
            x;
        }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let bb = pcg.get_all_for_bb(3usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[1];
        let placer = Placer::new(tcx, &body.body);
        let x = placer.local("x").mk();
        let temp4 = mir::Local::from(4_usize).into();
        let temp: mir::Place<'_> = mir::Local::from(2_usize).into();
        let aliases = stmt.aliases(
            temp.project_deeper(&[mir::ProjectionElem::Deref], tcx),
            &body.body(),
            tcx,
        );
        // *_2 aliases _4 at bb3[1]
        assert!(
            aliases.contains(&temp4),
            "Aliases: {:?} does not contain {:?}",
            aliases,
            temp4
        );
        assert!(aliases.contains(&x));
    });

    // pointer_reborrow_nested
    let input = r#"
        fn main() {
            let mut x: i32 = 1;
            let mut y = &mut x;
            let z = &mut y;
            let w = &mut **z;
            *w = 2;
            *y;
        }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let bb = pcg.get_all_for_bb(0usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[12];
        let placer = Placer::new(tcx, &body.body);
        let w = placer.local("w").mk();
        let w_deref = w.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let x = placer.local("x").mk();
        let aliases = stmt.aliases(w_deref, body.body(), tcx);
        // *w aliases x at bb0[12]
        assert!(
            aliases.contains(&x),
            "Aliases: {:?} does not contain {:?}",
            aliases,
            x
        );
    });

    // slice_write
    let input = r#"
        fn main() {
            let mut x = [0u8; 2];
            let y = &mut x[..1];
            y[0] = 0;
            x;
        }
        "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let bb = pcg.get_all_for_bb(1usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[2];
        let placer = Placer::new(tcx, &body.body);
        let y = placer.local("y").mk();
        let y_deref = y.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let local3: mir::Place<'_> = mir::Local::from(3_usize).into();
        let local3_deref = local3.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let aliases = stmt.aliases(y_deref, body.body(), tcx);
        assert!(aliases.contains(&local3_deref));
        assert!(pcg
            .results_for_all_blocks()
            .unwrap()
            .all_place_aliases(y_deref, body.body(), tcx)
            .contains(&local3_deref));
    });

    // recurse_parent_privacy
    let input = r#"
                struct Foo(i32);
                fn whee(f: &mut Foo) {
                    fn ok(f: &mut Foo) { f.0 = 1; }
                    ok(f);
                }
                "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let bb = pcg.get_all_for_bb(0usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[2];
        let placer = Placer::new(tcx, &body.body);
        let f = placer.local("f").mk();
        let f_deref = f.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let local3: mir::Place<'_> = mir::Local::from(3_usize).into();
        let local3_deref = local3.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let aliases = stmt.aliases(local3_deref, body.body(), tcx);
        assert!(aliases.contains(&f_deref));
        assert!(!aliases.contains(&f));
    });

    // enum_write_branch_read_branch
    let input = r#"
fn main() {
    enum Foo {
        X(i32),
        Y(i32),
    }
    let mut x = Foo::X(1);
    if let Foo::X(z) = &mut x {
        *z += 1;
    }
    if let Foo::Y(z) = &mut x {
        *z += 1;
    }
    if let Foo::X(z) = x {
        z;
    }
}
        "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let bb = pcg.get_all_for_bb(2usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[1];
        let init_z: mir::Place<'_> = mir::Local::from(5_usize).into();
        let z_deref = init_z.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let local3: mir::Place<'_> = mir::Local::from(3_usize).into();
        let deref3 = local3.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let deref_target = deref3.project_deeper(
            &[
                mir::ProjectionElem::Downcast(Some(Symbol::intern("X")), 0usize.into()),
                mir::ProjectionElem::Field(0usize.into(), tcx.types.i32),
            ],
            tcx,
        );
        let aliases = stmt.aliases(z_deref, &body.body, tcx);
        eprintln!("aliases: {:?}", aliases);
        eprintln!("deref_target: {:?}", deref_target);
        assert!(aliases.contains(&deref_target));
        assert!(pcg
            .results_for_all_blocks()
            .unwrap()
            .all_place_aliases(z_deref, &body.body, tcx)
            .contains(&deref_target));
        assert!(!aliases.contains(&deref3));
    });

    // enum_write_branch_read_whole
    let input = r#"
    fn main() {
    enum Foo {
        X(i32),
        Y(i32),
    }
    let mut x = Foo::X(1);
    if let Foo::X(z) = &mut x {
        *z += 1;
    }
    if let Foo::Y(z) = &mut x {
        *z += 1;
    }
    x;
    }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let bb = pcg.get_all_for_bb(3usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[0];
        let init_z: mir::Place<'_> = mir::Local::from(5_usize).into();
        let z_deref = init_z.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let local3: mir::Place<'_> = mir::Local::from(3_usize).into();
        let deref3 = local3.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let deref_target = deref3.project_deeper(
            &[
                mir::ProjectionElem::Downcast(Some(Symbol::intern("X")), 0usize.into()),
                mir::ProjectionElem::Field(0usize.into(), tcx.types.i32),
            ],
            tcx,
        );
        let aliases = stmt.aliases(z_deref, &body.body, tcx);
        eprintln!("aliases: {:?}", aliases);
        eprintln!("deref_target: {:?}", deref_target);
        assert!(aliases.contains(&deref_target));
        assert!(!aliases.contains(&deref3));
    });

    // 59_struct_ptrs_deep.rs
    let input = r#"
    struct A(i32);
    struct B<'a>(&'a A);
    struct C<'a, 'b>(&'b B<'a>);
    struct D<'a, 'b, 'c>(&'c C<'a, 'b>);

    fn foo() {
        let x = D(&C(&B(&A(0))));
        let y = x.0 .0 .0 .0 + 1;
    }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let placer = Placer::new(tcx, &body.body);
        let x = placer.local("x").mk();
        check_all_statements(&body.body, &mut pcg, |_location, stmt| {
            let _ = stmt.aliases(x, &body.body, tcx);
            // assert!(
            //     !stmt
            //         .aliases(star_temp.into(), repacker)
            //         .contains(&temp.into()),
            //     "Bad alias for {:?}",
            //     location
            // );
        });
    });

    let input = r#"
fn main() {
    struct Foo<'a>(&'a mut i32);
    let mut x = 1;
    let f = Foo(&mut x);
    *f.0 += 1;
    x;
}
"#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let temp: mir::Place<'_> = mir::Local::from(4_usize).into();
        let star_temp = temp.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        check_all_statements(&body.body, &mut pcg, |location, stmt| {
            assert!(
                !stmt.aliases(star_temp, &body.body, tcx).contains(&temp),
                "Bad alias for {:?}",
                location
            );
        });
    });

    let input = r#"
            fn main() {
                use std::time::Instant;
                fn run_expensive_calculation(){}
                let start = Instant::now();
                run_expensive_calculation();
                let elapsed = start.elapsed();
                println!("Elapsed: {}s", elapsed.as_secs());
            }"#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let temp_9: mir::Place<'_> = mir::Local::from(9_usize).into();
        let deref_temp_9 = temp_9.project_deeper(&[mir::ProjectionElem::Deref], tcx);

        let temp_19: mir::Place<'_> = mir::Local::from(19_usize).into();

        check_all_statements(&body.body, &mut pcg, |location, stmt| {
            assert!(
                !stmt
                    .aliases(deref_temp_9, &body.body, tcx)
                    .contains(&temp_19),
                "Bad alias for {:?}",
                location
            );
        });
    });

    // From flowistry_basic.rs
    let input = r#"
    fn main() {
      fn foo<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32 { x }

      let a = 1;
      let b = 2;
      let c = &a;
      let d = &b;
      let e = foo(c, d);
    }"#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let placer = Placer::new(tcx, &body.body);
        let bb0 = pcg.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let last_bg = bb0.statements.last().unwrap();
        let e_deref = placer.local("e").deref().mk();
        let a = placer.local("a").mk();
        assert!(last_bg.aliases(e_deref, &body.body, tcx).contains(&a));
    });

    // deep2
    let input = r#"
        fn foo() {
            let mut a = 1;
            let mut b  = &mut a;
            let mut c = &mut b;
            let d = **c;
        }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let placer = Placer::new(tcx, &body.body);
        let bb0 = pcg.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let last_bg = &bb0.statements[10];
        let starstarc = placer.local("c").deref().deref().mk();
        let a = placer.local("a").mk();
        assert!(last_bg.aliases(starstarc, &body.body, tcx).contains(&a));
    });

    // flowistry_pointer_deep
    let input = r#"
        fn foo() {
            let x = 1;
            let y = &&&x;
            let a = ***y;
        }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let placer = Placer::new(tcx, &body.body);
        let bb0 = pcg.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let stmt = &bb0.statements[11];
        let deref = placer.local("y").deref().mk();
        let deref_3 = placer.local("y").deref().deref().deref().mk();
        let x = placer.local("x").mk();
        assert!(stmt.aliases(deref_3, &body.body, tcx).contains(&x));
        assert!(!stmt
            .aliases(deref_3, &body.body, tcx)
            .contains(&mir::Local::from(3usize).into()));
        assert!(!stmt
            .aliases(deref_3, &body.body, tcx)
            .contains(&mir::Local::from(4usize).into()));
        assert!(!pcg
            .results_for_all_blocks()
            .unwrap()
            .all_place_aliases(deref, &body.body, tcx)
            .contains(&mir::Local::from(4usize).into()));
    });

    let input = r#"
        fn main() {
            fn other(x: &mut i32, y: i32, z: i32) { *x += y; }
            let mut x = 1;
            let y = 1;
            let z = 1;
            other(&mut x, y, z);
            (x);
        }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let bc = BorrowCheckerImpl::new(tcx, body);
        let mut pcg = run_pcg(body.body(), tcx, &bc, None);
        let placer = Placer::new(tcx, &body.body);
        let bb0 = pcg.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let last_bg = &bb0.statements[13];
        let temp: mir::Place<'_> = mir::Local::from(5_usize).into();
        let star_5 = temp.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let x = placer.local("x").mk();
        assert!(last_bg.aliases(star_5, &body.body, tcx).contains(&x));
    });
}
