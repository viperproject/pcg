use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdgeRef, LocalNode},
        edge::{kind::BorrowPcgEdgeKind, outlives::BorrowFlowEdgeKind},
        edge_data::EdgeData,
    },
    pcg::{LocalNodeLike, PCGNodeLike, PcgNode},
    rustc_interface::data_structures::fx::FxHashSet,
    utils::{CompilerCtxt, HasPlace, data_structures::HashSet},
};

use super::BorrowsGraph;

#[derive(Eq, PartialEq, Hash, Debug)]
struct Alias<'tcx> {
    node: PcgNode<'tcx>,
    exact_alias: bool,
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn ancestor_edges<'graph, 'mir: 'graph, 'bc: 'graph>(
        &'graph self,
        node: LocalNode<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> FxHashSet<BorrowPcgEdgeRef<'tcx, 'graph>> {
        let mut result: FxHashSet<BorrowPcgEdgeRef<'tcx, 'graph>> = FxHashSet::default();
        let mut stack = vec![node];
        let mut seen: FxHashSet<PcgNode<'tcx>> = FxHashSet::default();
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
    pub(crate) fn aliases<BC: Copy>(
        &self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> FxHashSet<PcgNode<'tcx>> {
        let mut result: FxHashSet<PcgNode<'tcx>> = FxHashSet::default();
        result.insert(node.into());
        let mut stack = vec![node];
        while let Some(node) = stack.pop() {
            for alias in self.aliases_all_projections(node, ctxt) {
                if result.insert(alias)
                    && let Some(local_node) = alias.try_to_local_node(ctxt)
                {
                    stack.push(local_node);
                }
            }
        }
        result
    }

    pub(crate) fn aliases_all_projections<BC: Copy>(
        &self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> FxHashSet<PcgNode<'tcx>> {
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
                if let PcgNode::Place(p) = local_node
                    && let Some(rp) = p.deref_to_rp(ctxt)
                {
                    for node in self.nodes(ctxt) {
                        if let Some(PcgNode::LifetimeProjection(p)) = node.try_to_local_node(ctxt)
                            && p.base() == rp.base()
                            && p.region_idx == rp.region_idx
                        {
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
        results.into_iter().map(|a| a.node).collect()
    }

    #[tracing::instrument(skip(self, repacker, seen, direct))]
    fn direct_aliases<'slf, BC: Copy>(
        &self,
        node: LocalNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, BC>,
        seen: &mut FxHashSet<PcgNode<'tcx>>,
        direct: bool,
    ) -> FxHashSet<Alias<'tcx>> {
        let mut result = HashSet::default();
        result.insert(Alias {
            node: node.into(),
            exact_alias: direct,
        });

        let extend = |blocked: PcgNode<'tcx>,
                      seen: &mut FxHashSet<PcgNode<'tcx>>,
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
                BorrowPcgEdgeKind::Deref(deref_edge) => {
                    let blocked = deref_edge.deref_place;
                    extend(blocked.into(), seen, &mut result, direct);
                }
                BorrowPcgEdgeKind::Borrow(borrow_edge) => {
                    let blocked = borrow_edge.blocked_place();
                    extend(blocked.into(), seen, &mut result, direct);
                }
                BorrowPcgEdgeKind::BorrowPcgExpansion(e) => {
                    for node in e.blocked_nodes(repacker) {
                        if let PcgNode::LifetimeProjection(p) = node {
                            extend(
                                p.to_pcg_node(repacker),
                                seen,
                                &mut result,
                                e.is_deref(repacker),
                            );
                        }
                    }
                }
                BorrowPcgEdgeKind::Abstraction(abstraction_type) => {
                    for input in abstraction_type.inputs() {
                        extend(input.to_pcg_node(repacker), seen, &mut result, false);
                    }
                }
                BorrowPcgEdgeKind::BorrowFlow(outlives) => match &outlives.kind {
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

#[rustversion::since(2025-05-24)]
#[cfg(test)]
#[test]
fn test_aliases() {
    use std::alloc::Allocator;

    use crate::owned_pcg::PcgLocation;
    use crate::rustc_interface::middle::mir::{self, START_BLOCK};
    use crate::rustc_interface::span::Symbol;

    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr)
        .init();

    use crate::PcgOutput;
    use crate::utils::test::run_pcg_on_str;

    fn check_all_statements<'mir, 'tcx>(
        body: &'mir mir::Body<'tcx>,
        analysis: &mut PcgOutput<'mir, 'tcx>,
        f: impl Fn(mir::Location, &PcgLocation<'tcx>),
    ) {
        for block in body.basic_blocks.indices() {
            let stmts_option = analysis.get_all_for_bb(block).unwrap();
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
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();
        let bb = analysis.get_all_for_bb(3usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[1];
        let x = ctxt.local_place("x").unwrap();
        let temp4 = mir::Local::from(4_usize).into();
        let temp: mir::Place<'_> = mir::Local::from(2_usize).into();
        let aliases = stmt.aliases(
            temp.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx()),
            ctxt.body(),
            ctxt.tcx(),
        );
        // *_2 aliases _4 at bb3[1]
        assert!(
            aliases.contains(&temp4),
            "Aliases: {:?} does not contain {:?}",
            aliases,
            temp4
        );
        assert!(aliases.contains(&(x.to_rust_place(ctxt))));
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
    run_pcg_on_str(input, |mut analysis| {
        let bb = analysis.get_all_for_bb(0usize.into()).unwrap().unwrap();
        let ctxt = analysis.ctxt();
        let stmt = &bb.statements[12];
        let w = ctxt.local_place("w").unwrap().to_rust_place(ctxt);
        let w_deref = w.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        let x = ctxt.local_place("x").unwrap().to_rust_place(ctxt);
        let aliases = stmt.aliases(w_deref, ctxt.body(), ctxt.tcx());
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
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();

        let bb = analysis.get_all_for_bb(1usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[2];

        let y = ctxt.local_place("y").unwrap().to_rust_place(ctxt);
        let y_deref = y.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        let local3: mir::Place<'_> = mir::Local::from(3_usize).into();
        let local3_deref = local3.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        let aliases = stmt.aliases(y_deref, ctxt.body(), ctxt.tcx());
        assert!(aliases.contains(&local3_deref));
        assert!(
            analysis
                .results_for_all_blocks()
                .unwrap()
                .all_place_aliases(y_deref, ctxt.body(), ctxt.tcx())
                .contains(&local3_deref)
        );
    });

    // recurse_parent_privacy
    let input = r#"
                struct Foo(i32);
                fn whee(f: &mut Foo) {
                    fn ok(f: &mut Foo) { f.0 = 1; }
                    ok(f);
                }
                "#;
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();

        let bb = analysis.get_all_for_bb(0usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[2];

        let f = ctxt.local_place("f").unwrap().to_rust_place(ctxt);
        let f_deref = f.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        let local3: mir::Place<'_> = mir::Local::from(3_usize).into();
        let local3_deref = local3.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        let aliases = stmt.aliases(local3_deref, ctxt.body(), ctxt.tcx());
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
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();
        let bb = analysis.get_all_for_bb(2usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[1];
        let init_z: mir::Place<'_> = mir::Local::from(5_usize).into();
        let z_deref = init_z.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        let local3: mir::Place<'_> = mir::Local::from(3_usize).into();
        let deref3 = local3.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        let deref_target = deref3.project_deeper(
            &[
                mir::ProjectionElem::Downcast(Some(Symbol::intern("X")), 0usize.into()),
                mir::ProjectionElem::Field(0usize.into(), ctxt.tcx().types.i32),
            ],
            ctxt.tcx(),
        );
        let aliases = stmt.aliases(z_deref, &ctxt.body(), ctxt.tcx());
        eprintln!("aliases: {:?}", aliases);
        eprintln!("deref_target: {:?}", deref_target);
        assert!(aliases.contains(&deref_target));
        assert!(
            analysis
                .results_for_all_blocks()
                .unwrap()
                .all_place_aliases(z_deref, &ctxt.body(), ctxt.tcx())
                .contains(&deref_target)
        );
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
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();
        let bb = analysis.get_all_for_bb(3usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[0];
        let init_z: mir::Place<'_> = mir::Local::from(5_usize).into();
        let z_deref = init_z.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        let local3: mir::Place<'_> = mir::Local::from(3_usize).into();
        let deref3 = local3.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        let deref_target = deref3.project_deeper(
            &[
                mir::ProjectionElem::Downcast(Some(Symbol::intern("X")), 0usize.into()),
                mir::ProjectionElem::Field(0usize.into(), ctxt.tcx().types.i32),
            ],
            ctxt.tcx(),
        );
        let aliases = stmt.aliases(z_deref, &ctxt.body(), ctxt.tcx());
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
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();

        let x = ctxt.local_place("x").unwrap().to_rust_place(ctxt);
        check_all_statements(&ctxt.body(), &mut analysis, |_location, stmt| {
            let _ = stmt.aliases(x, &ctxt.body(), ctxt.tcx());
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
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();

        let temp: mir::Place<'_> = mir::Local::from(4_usize).into();
        let star_temp = temp.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        check_all_statements(&ctxt.body(), &mut analysis, |location, stmt| {
            assert!(
                !stmt
                    .aliases(star_temp, &ctxt.body(), ctxt.tcx())
                    .contains(&temp),
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
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();

        let temp_9: mir::Place<'_> = mir::Local::from(9_usize).into();
        let deref_temp_9 = temp_9.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());

        let temp_19: mir::Place<'_> = mir::Local::from(19_usize).into();

        check_all_statements(&ctxt.body(), &mut analysis, |location, stmt| {
            assert!(
                !stmt
                    .aliases(deref_temp_9, &ctxt.body(), ctxt.tcx())
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
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();

        let bb0 = analysis.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let last_bg = bb0.statements.last().unwrap();
        let e_deref = ctxt
            .local_place("e")
            .unwrap()
            .project_deref(ctxt)
            .to_rust_place(ctxt);
        let a = ctxt.local_place("a").unwrap().to_rust_place(ctxt);
        assert!(
            last_bg
                .aliases(e_deref, ctxt.body(), ctxt.tcx())
                .contains(&a)
        );
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
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();

        let bb0 = analysis.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let last_bg = &bb0.statements[10];
        let starstarc = ctxt
            .local_place("c")
            .unwrap()
            .project_deref(ctxt)
            .project_deref(ctxt)
            .to_rust_place(ctxt);
        let a = ctxt.local_place("a").unwrap().to_rust_place(ctxt);
        assert!(
            last_bg
                .aliases(starstarc, ctxt.body(), ctxt.tcx())
                .contains(&a)
        );
    });

    // flowistry_pointer_deep
    let input = r#"
        fn foo() {
            let x = 1;
            let y = &&&x;
            let a = ***y;
        }
    "#;
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();

        let bb0 = analysis.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let stmt = &bb0.statements[11];
        let y_deref = ctxt.local_place("y").unwrap().project_deref(ctxt);
        let y_deref_3 = y_deref
            .project_deref(ctxt)
            .project_deref(ctxt)
            .to_rust_place(ctxt);
        let x = ctxt.local_place("x").unwrap().to_rust_place(ctxt);
        assert!(
            stmt.aliases(y_deref_3, &ctxt.body(), ctxt.tcx())
                .contains(&x)
        );
        assert!(
            !stmt
                .aliases(y_deref_3, &ctxt.body(), ctxt.tcx())
                .contains(&mir::Local::from(3usize).into())
        );
        assert!(
            !stmt
                .aliases(y_deref_3, &ctxt.body(), ctxt.tcx())
                .contains(&mir::Local::from(4usize).into())
        );
        assert!(
            !analysis
                .results_for_all_blocks()
                .unwrap()
                .all_place_aliases(y_deref.to_rust_place(ctxt), &ctxt.body(), ctxt.tcx())
                .contains(&mir::Local::from(4usize).into())
        );
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
    run_pcg_on_str(input, |mut analysis| {
        let ctxt = analysis.ctxt();

        let bb0 = analysis.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let last_bg = &bb0.statements[13];
        let temp: mir::Place<'_> = mir::Local::from(5_usize).into();
        let star_5 = temp.project_deeper(&[mir::ProjectionElem::Deref], ctxt.tcx());
        let x = ctxt.local_place("x").unwrap().to_rust_place(ctxt);
        assert!(
            last_bg
                .aliases(star_5, &ctxt.body(), ctxt.tcx())
                .contains(&x)
        );
    });
}
