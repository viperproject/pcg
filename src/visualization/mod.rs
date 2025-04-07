// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[rustversion::since(2024-12-14)]
pub mod bc_facts_graph;
pub mod dot_graph;
pub mod drawer;
pub mod graph_constructor;
mod grapher;
pub mod legend;
pub mod mir_graph;
mod node;

use crate::{
    borrow_pcg::{graph::BorrowsGraph, state::BorrowsState},
    free_pcs::{CapabilityKind, CapabilityLocals},
    pcg::place_capabilities::PlaceCapabilities,
    rustc_interface::middle::mir::Location,
    utils::{Place, CompilerCtxt, SnapshotLocation},
};
use std::{
    collections::HashSet,
    fs::File,
    io::{self},
};

use dot::escape_html;
use graph_constructor::BorrowsGraphConstructor;

use self::{
    dot_graph::{
        DotEdge, DotFloatAttr, DotLabel, DotNode, DotStringAttr, EdgeDirection, EdgeOptions,
    },
    graph_constructor::PcgGraphConstructor,
};

pub fn place_id(place: &Place<'_>) -> String {
    format!("{:?}", place)
}

pub struct GraphDrawer<T: io::Write> {
    out: T,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct NodeId(char, usize);

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.0, self.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GraphNode {
    id: NodeId,
    node_type: NodeType,
}

impl GraphNode {
    #[cfg(test)]
    fn label(&self) -> String {
        self.node_type.label()
    }

    fn to_dot_node(&self) -> DotNode {
        match &self.node_type {
            NodeType::PlaceNode {
                owned,
                capability,
                location,
                label,
                ty,
            } => {
                let capability_text = match capability {
                    Some(k) => format!("{:?}", k),
                    None => "".to_string(),
                };
                let location_text = match location {
                    Some(l) => escape_html(&format!(" at {:?}", l)),
                    None => "".to_string(),
                };
                let color = if location.is_some()
                    || capability.is_none()
                    || matches!(capability, Some(CapabilityKind::Write))
                {
                    "gray"
                } else if *owned {
                    "black"
                } else {
                    "darkgreen"
                };
                let (style, penwidth) = if *owned {
                    (None, None)
                } else {
                    (
                        Some(DotStringAttr("rounded".to_string())),
                        Some(DotFloatAttr(1.5)),
                    )
                };
                let label = format!(
                    "<FONT FACE=\"courier\">{}&nbsp;{}{}</FONT>",
                    escape_html(label),
                    escape_html(&capability_text),
                    escape_html(&location_text),
                );
                DotNode {
                    id: self.id.to_string(),
                    label: DotLabel::Html(label),
                    color: DotStringAttr(color.to_string()),
                    font_color: DotStringAttr(color.to_string()),
                    shape: DotStringAttr("rect".to_string()),
                    style,
                    penwidth,
                    tooltip: Some(DotStringAttr(ty.clone())),
                }
            }
            NodeType::RegionProjectionNode {
                label,
                base_ty: place_ty,
            } => DotNode {
                id: self.id.to_string(),
                label: DotLabel::Text(label.clone()),
                color: DotStringAttr("blue".to_string()),
                font_color: DotStringAttr("blue".to_string()),
                shape: DotStringAttr("octagon".to_string()),
                style: None,
                penwidth: None,
                tooltip: Some(DotStringAttr(place_ty.clone())),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NodeType {
    PlaceNode {
        owned: bool,
        label: String,
        capability: Option<CapabilityKind>,
        location: Option<SnapshotLocation>,
        ty: String,
    },
    RegionProjectionNode {
        label: String,
        base_ty: String,
    },
}

impl NodeType {
    #[cfg(test)]
    pub(crate) fn label(&self) -> String {
        match self {
            NodeType::PlaceNode { label, .. } => label.clone(),
            NodeType::RegionProjectionNode { label, .. } => label.clone(),
        }
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum GraphEdge {
    Abstract {
        blocked: NodeId,
        blocking: NodeId,
        label: String,
    },
    // For literal borrows
    Alias {
        blocked_place: NodeId,
        blocking_place: NodeId,
    },
    Borrow {
        borrowed_place: NodeId,
        assigned_region_projection: NodeId,
        kind: String,
        location: Option<Location>,
        region: Option<String>,
        path_conditions: String,
    },
    Projection {
        source: NodeId,
        target: NodeId,
    },
    DerefExpansion {
        source: NodeId,
        target: NodeId,
        path_conditions: String,
    },
    Block {
        source: NodeId,
        target: NodeId,
        kind: String,
    },
    Coupled {
        source: NodeId,
        target: NodeId,
        directed: bool,
    },
}

impl GraphEdge {
    pub(super) fn to_dot_edge(&self) -> DotEdge {
        match self {
            GraphEdge::Projection { source, target } => DotEdge {
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward),
            },
            GraphEdge::Alias {
                blocked_place,
                blocking_place,
            } => DotEdge {
                from: blocked_place.to_string(),
                to: blocking_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("grey".to_string())
                    .with_style("dashed".to_string()),
            },
            GraphEdge::Borrow {
                borrowed_place,
                assigned_region_projection: assigned_place,
                location: _,
                region,
                kind,
                path_conditions,
            } => DotEdge {
                to: assigned_place.to_string(),
                from: borrowed_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("orange".to_string())
                    .with_label(format!(
                        "{} {}",
                        kind,
                        region.as_ref().cloned().unwrap_or("".to_string())
                    ))
                    .with_tooltip(path_conditions.clone()),
            },
            GraphEdge::DerefExpansion {
                source,
                target,
                path_conditions,
            } => DotEdge {
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("green".to_string())
                    .with_tooltip(path_conditions.clone()),
            },
            GraphEdge::Abstract {
                blocked,
                blocking,
                label,
            } => DotEdge {
                from: blocked.to_string(),
                to: blocking.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_label(label.clone())
                    .with_penwidth(3.0),
            },
            GraphEdge::Block {
                source,
                target,
                kind,
            } => DotEdge {
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_label(kind.clone())
                    .with_color("purple".to_string()),
            },
            GraphEdge::Coupled {
                source,
                target,
                directed,
            } => {
                let edge_options = if *directed {
                    EdgeOptions::directed(EdgeDirection::Forward)
                } else {
                    EdgeOptions::undirected().with_weight(2.0)
                };
                DotEdge {
                    from: source.to_string(),
                    to: target.to_string(),
                    options: edge_options
                        .with_color("red".to_string())
                        .with_style("dashed".to_string()),
                }
            }
        }
    }
}

pub(crate) struct Graph {
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge>,
}

impl Graph {
    fn new(nodes: Vec<GraphNode>, edges: HashSet<GraphEdge>) -> Self {
        Self { nodes, edges }
    }

    #[cfg(test)]
    pub(crate) fn edge_between_labelled_nodes(
        &self,
        label1: &str,
        label2: &str,
    ) -> Result<&GraphEdge, String> {
        let label_1_id = self
            .nodes
            .iter()
            .find(|n| n.label() == label1)
            .map(|n| n.id)
            .ok_or(format!("No node with label: {}", label1))?;
        let label_2_id = self
            .nodes
            .iter()
            .find(|n| n.label() == label2)
            .map(|n| n.id)
            .ok_or(format!("No node with label: {}", label2))?;
        self.edges
            .iter()
            .find(|edge| {
                let dot_edge = edge.to_dot_edge();
                dot_edge.from == label_1_id.to_string() && dot_edge.to == label_2_id.to_string()
            })
            .ok_or(format!(
                "Edges exists, no edge between {} and {}",
                label1, label2
            ))
    }
}

pub(crate) fn generate_borrows_dot_graph<'a, 'tcx: 'a>(
    repacker: CompilerCtxt<'a, 'tcx>,
    borrows_domain: &BorrowsGraph<'tcx>,
) -> io::Result<String> {
    let constructor = BorrowsGraphConstructor::new(borrows_domain, repacker);
    let graph = constructor.construct_graph();
    let mut buf = vec![];
    let drawer = GraphDrawer::new(&mut buf);
    drawer.draw(graph)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub(crate) fn generate_dot_graph<'a, 'tcx: 'a>(
    repacker: CompilerCtxt<'a, 'tcx>,
    summary: &CapabilityLocals<'tcx>,
    borrows_domain: &BorrowsState<'tcx>,
    capabilities: &PlaceCapabilities<'tcx>,
    file_path: &str,
) -> io::Result<()> {
    let constructor = PcgGraphConstructor::new(summary, repacker, borrows_domain, capabilities);
    let graph = constructor.construct_graph();
    let drawer = GraphDrawer::new(File::create(file_path).unwrap_or_else(|e| {
        panic!("Failed to create file at path: {}: {}", file_path, e);
    }));
    drawer.draw(graph)
}
