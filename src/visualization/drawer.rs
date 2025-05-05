use std::io::{self};

use crate::visualization::dot_graph::DotGraph;

use super::{Graph, GraphDrawer};

impl<T: io::Write> GraphDrawer<T> {
    pub fn new(out: T) -> Self {
        Self { out }
    }

    pub(crate) fn draw(mut self, graph: Graph) -> io::Result<()> {
        let dot_graph = DotGraph {
            name: "CapabilitySummary".to_string(),
            nodes: graph.nodes.iter().map(|g| g.to_dot_node()).collect(),
            edges: graph.edges.into_iter().map(|e| e.to_dot_edge()).collect(),
        };
        writeln!(self.out, "{dot_graph}")
    }
}
