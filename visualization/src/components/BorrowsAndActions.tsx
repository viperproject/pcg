import React, { useState, useEffect } from "react";
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
  onShowGraph,
  onDeselectPcg,
  selectedAction,
  onActionSelect,
}: {
  actions: PcgActions;
  stmtIteration?: { iterations: PcgIteration[] };
  selectedFunction?: string;
  phase: string;
  onShowGraph?: (filename: string) => void;
  onDeselectPcg?: () => void;
  selectedAction?: { phase: string; index: number };
  onActionSelect?: (phase: string, index: number) => void;
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

  const handleActionClick = (index: number) => {
    const graphFilename = getActionGraphFilename(index);
    if (graphFilename && onShowGraph && onDeselectPcg && onActionSelect) {
      onDeselectPcg(); // Unselect any currently selected PCG
      onShowGraph(graphFilename); // Show the graph in main view
      onActionSelect(phase, index); // Mark this action as selected
    }
  };

  return (
    <ul>
      {actions.map((action, index) => {
        const graphFilename = getActionGraphFilename(index);
        const isSelected = selectedAction?.phase === phase && selectedAction?.index === index;
        return (
          <li key={`action-${index}`} style={{ display: "flex", alignItems: "center", gap: "10px" }}>
            <span
              style={{
                cursor: graphFilename ? "pointer" : "default",
                padding: "4px 8px",
                borderRadius: "4px",
                backgroundColor: isSelected ? "#007acc" : "transparent",
                color: isSelected ? "white" : "inherit",
                border: isSelected ? "1px solid #007acc" : "1px solid transparent",
                flex: 1,
              }}
              onClick={() => graphFilename && handleActionClick(index)}
              title={graphFilename ? "Click to show graph in main view" : undefined}
            >
              {action}
            </span>
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
  onShowGraph,
  onDeselectPcg,
}: {
  data: PcgProgramPointData;
  stmtIteration?: { iterations: PcgIteration[] };
  selectedFunction?: string;
  onShowGraph?: (filename: string) => void;
  onDeselectPcg?: () => void;
}) {
  const [selectedAction, setSelectedAction] = useState<{ phase: string; index: number } | undefined>(undefined);

  // Collect all actions with their phase info for keyboard navigation
  const getAllActions = () => {
    const allActions: Array<{ action: string; index: number; phase: string }> = [];

    if ("latest" in data) {
      const phases = ["pre_operands", "post_operands", "pre_main", "post_main"] as const;
      phases.forEach((phase) => {
        data.actions[phase].forEach((action, index) => {
          allActions.push({ action, index, phase });
        });
      });
    } else {
      data.actions.forEach((action, index) => {
        allActions.push({ action, index, phase: "actions" });
      });
    }

    return allActions;
  };

  const allActions = getAllActions();

  // Keyboard navigation
  useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      if (event.key === 'q' || event.key === 'a') {
        event.preventDefault();

        if (allActions.length === 0) return;

        let newGlobalIndex: number;
        if (!selectedAction) {
          newGlobalIndex = event.key === 'q' ? allActions.length - 1 : 0;
        } else {
          const currentGlobalIndex = allActions.findIndex(
            (actionData) => actionData.phase === selectedAction.phase && actionData.index === selectedAction.index
          );

          if (event.key === 'q') {
            newGlobalIndex = currentGlobalIndex > 0 ? currentGlobalIndex - 1 : allActions.length - 1;
          } else {
            newGlobalIndex = currentGlobalIndex < allActions.length - 1 ? currentGlobalIndex + 1 : 0;
          }
        }

        const actionData = allActions[newGlobalIndex];
        setSelectedAction({ phase: actionData.phase, index: actionData.index });

        // Get the graph filename for this action
        const getActionGraphFilename = (actionIndex: number, phase: string): string | null => {
          if (!stmtIteration || stmtIteration.iterations.length === 0 || !selectedFunction) {
            return null;
          }

          const mostRecentIteration = stmtIteration.iterations[stmtIteration.iterations.length - 1];
          const phaseMapping: Record<string, string> = {
            "pre_operands": "PreOperands",
            "post_operands": "PostOperands",
            "pre_main": "PreMain",
            "post_main": "PostMain",
            "actions": "actions"
          };

          const iterationPhaseName = phaseMapping[phase] || phase;
          const phaseActions = mostRecentIteration.actions[iterationPhaseName];

          if (!phaseActions || !(actionIndex in phaseActions)) {
            return null;
          }

          return `data/${selectedFunction}/${phaseActions[actionIndex]}`;
        };

        const graphFilename = getActionGraphFilename(actionData.index, actionData.phase);
        if (graphFilename && onShowGraph && onDeselectPcg) {
          onDeselectPcg();
          onShowGraph(graphFilename);
        }
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [selectedAction, allActions, stmtIteration, selectedFunction, onShowGraph, onDeselectPcg]);

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
              onShowGraph={onShowGraph}
              onDeselectPcg={onDeselectPcg}
              selectedAction={selectedAction}
              onActionSelect={(phase, index) => setSelectedAction({ phase, index })}
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
          onShowGraph={onShowGraph}
          onDeselectPcg={onDeselectPcg}
          selectedAction={selectedAction}
          onActionSelect={(phase, index) => setSelectedAction({ phase, index })}
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
      <div style={{ marginTop: "10px", fontSize: "12px", color: "#666" }}>
        Press 'q'/'a' to navigate between actions
      </div>
    </div>
  );
}
