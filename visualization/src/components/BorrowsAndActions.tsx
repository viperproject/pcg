import React from "react";
import {
  PathData,
  Borrow,
  BorrowAction,
  Reborrow,
  MaybeOldPlace,
  PcgActions,
  PlaceExpand,
  PCGNode,
  MaybeRemotePlace,
  LocalNode,
  PCGStmtVisualizationData,
  PcgProgramPointData,
  CurrentPoint,
} from "../types";
import { PcgIteration } from "../api";
import { openDotGraphInNewWindow } from "../dot_graph";
import * as Viz from "@viz-js/viz";

function MaybeOldPlaceDisplay({
  maybeOldPlace,
}: {
  maybeOldPlace: MaybeOldPlace;
}) {
  if (typeof maybeOldPlace === "string") {
    return <span>{maybeOldPlace}</span>;
  }
  return (
    <span style={{ fontFamily: "monospace" }}>
      {maybeOldPlace.place} {maybeOldPlace.at ? `at ${maybeOldPlace.at}` : ""}
    </span>
  );
}

function MaybeRemotePlaceDisplay({
  maybeRemotePlace,
}: {
  maybeRemotePlace: MaybeRemotePlace;
}) {
  if (typeof maybeRemotePlace === "string") {
    return <span>{maybeRemotePlace}</span>;
  }
  return <MaybeOldPlaceDisplay maybeOldPlace={maybeRemotePlace} />;
}

function ReborrowDisplay({ reborrow }: { reborrow: Reborrow }) {
  return (
    <div>
      <p>
        Assigned Place:{" "}
        <MaybeOldPlaceDisplay maybeOldPlace={reborrow?.assigned_place} />
      </p>
      <p>
        Blocked Place:{" "}
        <MaybeOldPlaceDisplay maybeOldPlace={reborrow?.blocked_place} />
      </p>
      <p>Mutable: {reborrow?.is_mut ? "Yes" : "No"}</p>
    </div>
  );
}

function BridgeExpands({ expands }: { expands: PlaceExpand[] }) {
  return (
    <div>
      {expands.map((expand, idx) => (
        <div key={`expand-${idx}`}>
          <PCGNodeDisplay node={expand.base} />→
          <span>
            {expand.expansion.map((e, idx2) => (
              <PCGNodeDisplay key={`expand-${idx}-${idx2}`} node={e} />
            ))}
          </span>
        </div>
      ))}
    </div>
  );
}

function BorrowDisplay({ borrow }: { borrow: Borrow }) {
  return (
    <div>
      <p>
        Assigned:{" "}
        <MaybeOldPlaceDisplay maybeOldPlace={borrow?.assigned_place} />
      </p>
      <p>
        Borrowed:{" "}
        <MaybeOldPlaceDisplay maybeOldPlace={borrow?.borrowed_place} />
      </p>
      <p>Is Mutable: {borrow?.is_mut ? "Yes" : "No"}</p>
      <p>Kind: {borrow?.kind}</p>
    </div>
  );
}

function PCGNodeDisplay({ node }: { node: PCGNode<MaybeRemotePlace> }) {
  if (typeof node === "string") {
    return <span>{node}</span>;
  } else if ("region" in node) {
    return (
      <span>
        <MaybeRemotePlaceDisplay maybeRemotePlace={node.place} />↓{node.region}
      </span>
    );
  }
  return <span>{JSON.stringify(node)}</span>;
}

function PcgActionsDisplay({
  actions,
  stmtIteration,
  selectedFunction,
  phase,
}: {
  actions: PcgActions;
  stmtIteration?: { iterations: PcgIteration[] };
  selectedFunction?: string;
  phase: string;
}) {
  const getActionGraphFilename = (actionIndex: number): string | null => {
    if (!stmtIteration || stmtIteration.iterations.length === 0 || !selectedFunction) {
      return null;
    }

    // Use the most recent iteration
    const mostRecentIteration = stmtIteration.iterations[stmtIteration.iterations.length - 1];

    // Map display phase names to iteration phase names
    const phaseMapping: Record<string, string> = {
      "pre_operands": "PreOperands",
      "post_operands": "PostOperands",
      "pre_main": "PreMain",
      "post_main": "PostMain",
      "actions": "actions" // fallback for the simple case
    };

    const iterationPhaseName = phaseMapping[phase] || phase;
    const phaseActions = mostRecentIteration.actions[iterationPhaseName];

    if (!phaseActions || !(actionIndex in phaseActions)) {
      return null;
    }

    // Return the filename with the correct path
    return `data/${selectedFunction}/${phaseActions[actionIndex]}`;
  };

  return (
    <ul>
      {actions.map((action, index) => {
        const graphFilename = getActionGraphFilename(index);
        return (
          <li key={`action-${index}`} style={{ display: "flex", alignItems: "center", gap: "10px" }}>
            <span>{action}</span>
            {graphFilename && (
              <button
                style={{
                  fontSize: "12px",
                  padding: "2px 6px",
                  backgroundColor: "#e6f3ff",
                  border: "1px solid #007acc",
                  borderRadius: "3px",
                  cursor: "pointer",
                }}
                onClick={() => openDotGraphInNewWindow(graphFilename)}
                title="Show graph after this action"
              >
                Show Graph
              </button>
            )}
          </li>
        );
      })}
    </ul>
  );
}

export default function PCGOps({
  data,
  stmtIteration,
  selectedFunction,
}: {
  data: PcgProgramPointData;
  stmtIteration?: { iterations: PcgIteration[] };
  selectedFunction?: string;
}) {
  let content;
  if ("latest" in data) {
    content = (
      <>
        {[
          "pre_operands" as const,
          "post_operands" as const,
          "pre_main" as const,
          "post_main" as const,
        ].map((key) => (
          <div key={key}>
            <h5>{key}</h5>
            <PcgActionsDisplay
              actions={data.actions[key]}
              stmtIteration={stmtIteration}
              selectedFunction={selectedFunction}
              phase={key}
            />
          </div>
        ))}
      </>
    );
  } else {
    content = (
      <>
        <h4>Actions</h4>
        <PcgActionsDisplay
          actions={data.actions}
          stmtIteration={stmtIteration}
          selectedFunction={selectedFunction}
          phase="actions"
        />
      </>
    );
  }
  return (
    <div
      style={{
        position: "fixed",
        bottom: "20px",
        right: "20px",
        backgroundColor: "white",
        boxShadow: "0 0 10px rgba(0,0,0,0.1)",
        padding: "10px",
        maxWidth: "300px",
        overflowY: "auto",
        maxHeight: "80vh",
      }}
    >
      {content}
    </div>
  );
}
