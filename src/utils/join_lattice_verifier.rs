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
    pub(crate) fn record_join_result(&mut self, computation: JoinComputation<T>) {
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
        use petgraph::algo::is_cyclic_directed;
        assert!(
            !is_cyclic_directed(&self.graph),
            "Join lattice must be acyclic. Graph: {:?}",
            self.graph
        );

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
