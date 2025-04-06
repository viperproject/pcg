import React from "react";
import BasicBlockNode from "./BasicBlockNode";
import Edge from "./Edge";
import {
  CurrentPoint,
  DagreEdge,
  DagreNode,
  BasicBlockData,
} from "../types";

import { MirGraphNode } from "../api";

interface MirGraphProps {
  nodes: DagreNode<BasicBlockData>[];
  edges: DagreEdge[];
  mirNodes: MirGraphNode[];
  currentPoint: CurrentPoint;
  setCurrentPoint: (point: CurrentPoint) => void;
  isBlockOnSelectedPath: (block: number) => boolean;
  height: number | null;
}

const MirGraph: React.FC<MirGraphProps> = ({
  nodes,
  edges,
  mirNodes,
  currentPoint,
  setCurrentPoint,
  isBlockOnSelectedPath,
  height,
}) => {
  // Helper to find block number from node ID (like 'bb0')
  const findBlockByNodeId = (nodeId: string): number | undefined => {
    return mirNodes.find((n) => n.id === nodeId)?.block;
  };

  return (
    <div
      className="graph-container"
      style={{ height: height ? height + 100 : "auto", position: "relative" }}
    >
      <div id="mir-graph">
        {nodes.map((node) => (
          <BasicBlockNode
            isOnSelectedPath={isBlockOnSelectedPath(node.data.block)}
            key={node.id}
            data={node.data}
            height={node.height}
            position={{
              x: node.x,
              y: node.y,
            }}
            currentPoint={currentPoint}
            setCurrentPoint={setCurrentPoint}
          />
        ))}
      </div>
      <svg
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          pointerEvents: "none",
        }}
      >
        {edges.map((edge) => {
          const sourceBlock = findBlockByNodeId(edge.source);
          const targetBlock = findBlockByNodeId(edge.target);
          const isSelected =
            currentPoint.type === "terminator" &&
            currentPoint.block1 === sourceBlock &&
            currentPoint.block2 === targetBlock;

          return (
            <Edge
              key={edge.id}
              edge={edge}
              nodes={nodes}
              selected={isSelected}
              onSelect={() => {
                if (sourceBlock !== undefined && targetBlock !== undefined) {
                  setCurrentPoint({
                    type: "terminator",
                    block1: sourceBlock,
                    block2: targetBlock,
                  });
                }
              }}
            />
          );
        })}
      </svg>
    </div>
  );
};

export default MirGraph;
