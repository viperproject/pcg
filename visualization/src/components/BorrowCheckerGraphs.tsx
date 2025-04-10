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
      <br />
      <button
        style={{ marginLeft: "10px" }}
        onClick={async () => {
          if (currentPoint.type == "stmt") {
            const path = `data/${selectedFunction}/bc_facts_bb${currentPoint.block}_${currentPoint.stmt}.txt`;
            const text = await fetch(path).then((res) => res.text());
            console.log(text);
          }
        }}
      >
        Log Polonius Output Facts To Console
      </button>
    </>
  );
}
