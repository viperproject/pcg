use super::display::{DebugLines, DisplayDiff};

#[derive(Debug, Clone)]
pub(crate) struct JoinLatticeVerifier<T> {
    #[allow(dead_code)]
    graph: petgraph::Graph<T, ()>,
}

#[allow(unused)]
pub(crate) struct JoinComputation<T> {
    pub(crate) lhs: T,
    pub(crate) rhs: T,
    pub(crate) result: T,
}

impl<T: Clone + PartialEq + std::fmt::Debug> JoinLatticeVerifier<T> {
    pub(crate) fn new() -> Self {
        Self {
            graph: petgraph::Graph::new(),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn record_join_result<U: Copy>(&mut self, computation: JoinComputation<T>, ctxt: U)
    where
        T: DebugLines<U>,
    {
        // Add nodes if they don't exist
        let lhs_idx = self.get_or_add_node(computation.lhs.clone());
        let rhs_idx = self.get_or_add_node(computation.rhs.clone());
        let result_idx = self.get_or_add_node(computation.result.clone());

        // Add edges from inputs to result
        if lhs_idx != result_idx {
            self.graph.add_edge(lhs_idx, result_idx, ());
        }
        if rhs_idx != result_idx {
            self.graph.add_edge(rhs_idx, result_idx, ());
        }

        // Verify acyclicity
        use petgraph::visit::{DfsPostOrder, Walker};
        use std::collections::HashSet;

        // For each node, try to find a cycle starting from it
        for start in self.graph.node_indices() {
            let mut visited = HashSet::new();
            let mut stack = vec![];
            let mut on_stack = HashSet::new();

            fn dfs<T: Clone + PartialEq + std::fmt::Debug>(
                graph: &petgraph::Graph<T, ()>,
                node: petgraph::graph::NodeIndex,
                visited: &mut HashSet<petgraph::graph::NodeIndex>,
                stack: &mut Vec<petgraph::graph::NodeIndex>,
                on_stack: &mut HashSet<petgraph::graph::NodeIndex>,
            ) -> Option<Vec<T>> {
                if on_stack.contains(&node) {
                    // Found cycle. Collect nodes from the cycle
                    let cycle_start_idx = stack.iter().position(|&x| x == node).unwrap();
                    let cycle: Vec<_> = stack[cycle_start_idx..]
                        .iter()
                        .map(|&idx| graph[idx].clone())
                        .collect();
                    return Some(cycle);
                }

                if visited.contains(&node) {
                    return None;
                }

                visited.insert(node);
                on_stack.insert(node);
                stack.push(node);

                for neighbor in graph.neighbors(node) {
                    if let Some(cycle) = dfs(graph, neighbor, visited, stack, on_stack) {
                        return Some(cycle);
                    }
                }

                stack.pop();
                on_stack.remove(&node);
                None
            }

            if let Some(cycle) = dfs(&self.graph, start, &mut visited, &mut stack, &mut on_stack) {
                eprintln!("Found cycle:");
                for (i, elem) in cycle.iter().enumerate() {
                    eprintln!("Node #{}", i);
                    for line in elem.debug_lines(ctxt) {
                        eprintln!("{}", line);
                    }
                    eprintln!("---");
                }
                eprintln!("Node diffs:");
                for i in 0..cycle.len() {
                    let curr = &cycle[i];
                    let next = &cycle[(i + 1) % cycle.len()];
                    eprintln!("{}\n---\n", curr.fmt_diff(next, ctxt));
                }
                panic!("Join lattice must be acyclic.");
            }
        }

        // Verify join property: if there exists a node R with edges from both lhs and rhs, it must be equal to result
        for node_idx in self.graph.node_indices() {
            let has_lhs_edge = self
                .graph
                .edges_connecting(lhs_idx, node_idx)
                .next()
                .is_some();
            let has_rhs_edge = self
                .graph
                .edges_connecting(rhs_idx, node_idx)
                .next()
                .is_some();

            if has_lhs_edge && has_rhs_edge {
                assert_eq!(
                    self.graph[node_idx], computation.result,
                    "Node with edges from both join inputs must equal join result"
                );
            }
        }
    }

    fn get_or_add_node(&mut self, value: T) -> petgraph::graph::NodeIndex {
        // Try to find existing node with this value
        for node_idx in self.graph.node_indices() {
            if self.graph[node_idx] == value {
                return node_idx;
            }
        }
        // If not found, add new node
        self.graph.add_node(value)
    }
}
