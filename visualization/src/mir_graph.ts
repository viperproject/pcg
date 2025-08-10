import { MirGraphEdge, MirGraphNode } from "./api";
import { computeTableHeight } from "./components/BasicBlockTable";
import { BasicBlockData, DagreEdge, DagreInputNode, DagreNode } from "./types";
import * as dagre from "@dagrejs/dagre";

export type FilterOptions = {
  showUnwindEdges: boolean;
  path: number[] | null;
};

export function filterNodesAndEdges(
  nodes: MirGraphNode[],
  edges: MirGraphEdge[],
  options: FilterOptions
): {
  filteredNodes: MirGraphNode[];
  filteredEdges: MirGraphEdge[];
} {
  let filteredNodes = nodes;
  let filteredEdges = edges;
  if (!options.showUnwindEdges) {
    filteredNodes = nodes.filter((node) => node.terminator.stmt !== "resume");
    filteredEdges = edges.filter((edge) => edge.label !== "unwind");
  }
  if (options.path) {
    filteredNodes = filteredNodes.filter((node) =>
      options.path.includes(node.block)
    );
    filteredEdges = filteredEdges.filter((edge) => {
      const sourceNode = nodes.find((n) => n.id === edge.source);
      const targetNode = nodes.find((n) => n.id === edge.target);
      return (
        sourceNode &&
        targetNode &&
        options.path.includes(sourceNode.block) &&
        options.path.includes(targetNode.block)
      );
    });
  }

  return { filteredNodes, filteredEdges };
}

export function layoutSizedNodes(
  nodes: DagreInputNode<BasicBlockData>[],
  edges: any
) {
  const g = new dagre.graphlib.Graph().setDefaultEdgeLabel(() => ({}));
  g.setGraph({ ranksep: 100, rankdir: "TB", marginy: 100 });

  edges.forEach((edge: any) => g.setEdge(edge.source, edge.target));
  nodes.forEach((node) => g.setNode(node.id, node));

  dagre.layout(g);

  let height = g.graph().height;
  if (!isFinite(height)) {
    height = null;
  }

  return {
    nodes: nodes as DagreNode<BasicBlockData>[],
    edges,
    height,
  };
}

export function layoutUnsizedNodes(
  nodes: MirGraphNode[],
  edges: { source: string; target: string }[]
): {
  nodes: DagreNode<BasicBlockData>[];
  height: number;
} {
  const heightCalculatedNodes = nodes.map((node) => {
    return {
      id: node.id,
      data: {
        block: node.block,
        stmts: node.stmts,
        terminator: node.terminator,
      },
      height: computeTableHeight(node),
      width: 300,
    };
  });
  const g = layoutSizedNodes(heightCalculatedNodes, edges);
  return {
    nodes: g.nodes,
    height: g.height,
  };
}

export function toDagreEdges(edges: MirGraphEdge[]): DagreEdge[] {
  return edges.map((edge, idx) => ({
    id: `${edge.source}-${edge.target}-${idx}`,
    source: edge.source,
    target: edge.target,
    data: { label: edge.label },
    type: "straight",
  }));
}
