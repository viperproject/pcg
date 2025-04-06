import React from "react";
import { openDotGraphInNewWindow } from "../dot_graph";
import { CurrentPoint } from "../types";

interface BorrowCheckerGraphsProps {
  currentPoint: CurrentPoint;
  selectedFunction: string;
}
export default function BorrowCheckerGraphs({
  currentPoint,
  selectedFunction,
}: BorrowCheckerGraphsProps) {
  return (
    <>
      <button
        style={{ marginLeft: "10px" }}
        onClick={async () => {
          if (currentPoint.type == "stmt") {
            const dotFilePath = `data/${selectedFunction}/bc_facts_graph_bb${currentPoint.block}_${currentPoint.stmt}_start.dot`;
            openDotGraphInNewWindow(dotFilePath);
          }
        }}
      >
        Polonius Subset Graph (This Location [Start])
      </button>
      <br />
      <button
        style={{ marginLeft: "10px" }}
        onClick={async () => {
          if (currentPoint.type == "stmt") {
            const dotFilePath = `data/${selectedFunction}/bc_facts_graph_bb${currentPoint.block}_${currentPoint.stmt}_mid.dot`;
            openDotGraphInNewWindow(dotFilePath);
          }
        }}
      >
        Polonius Subset Graph (This Location [Mid])
      </button>
      <br />
      <button
        style={{ marginLeft: "10px" }}
        onClick={async () => {
          if (currentPoint.type == "stmt") {
            const dotFilePath = `data/${selectedFunction}/bc_facts_graph_anywhere.dot`;
            openDotGraphInNewWindow(dotFilePath);
          }
        }}
      >
        Polonius Subset Graph (Anywhere)
      </button>
      <br />
      <button
        style={{ marginLeft: "10px" }}
        onClick={async () => {
          if (currentPoint.type == "stmt") {
            const dotFilePath = `data/${selectedFunction}/region_inference_outlives.dot`;
            openDotGraphInNewWindow(dotFilePath);
          }
        }}
      >
        Region Inference Outlives Graph
      </button>
    </>
  );
}
