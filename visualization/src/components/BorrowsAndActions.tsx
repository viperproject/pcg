import React, { useState, useEffect } from "react";
import {
  EvalStmtPhase,
  PcgActions,
  PcgProgramPointData,
  SelectedAction,
} from "../types";
import { IterationActions, PcgIteration } from "../api";

function PcgActionsDisplay({
  actions,
  selectedFunction,
  phase,
  selectedAction,
  onActionSelect,
}: {
  actions: PcgActions;
  selectedFunction?: string;
  phase: EvalStmtPhase;
  selectedAction?: { phase: EvalStmtPhase; index: number };
  onActionSelect?: (phase: EvalStmtPhase, index: number) => void;
}) {
  const handleActionClick = (index: number) => {
    onActionSelect(phase, index); // Mark this action as selected
  };

  return (
    <ul>
      {actions.map((action, index) => {
        const isSelected =
          selectedAction?.phase === phase && selectedAction?.index === index;
        return (
          <li
            key={`action-${index}`}
            style={{ display: "flex", alignItems: "center", gap: "10px" }}
          >
            <span
              style={{
                cursor: "pointer",
                padding: "4px 8px",
                borderRadius: "4px",
                backgroundColor: isSelected ? "#007acc" : "transparent",
                color: isSelected ? "white" : "inherit",
                border: isSelected
                  ? "1px solid #007acc"
                  : "1px solid transparent",
                flex: 1,
              }}
              onClick={() => handleActionClick(index)}
              title={"Click to show graph in main view"}
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
  selectedFunction,
  selectedAction,
  setSelectedAction,
}: {
  data: PcgProgramPointData;
  selectedFunction?: string;
  selectedAction: SelectedAction | null;
  setSelectedAction: (action: SelectedAction) => void;
}) {
  // Collect all actions with their phase info for keyboard navigation
  const getAllActions = () => {
    const allActions: Array<{
      action: string;
      index: number;
      phase: EvalStmtPhase;
    }> = [];

    if ("latest" in data) {
      const phases = [
        "pre_operands",
        "post_operands",
        "pre_main",
        "post_main",
      ] as const;
      phases.forEach((phase) => {
        data.actions[phase].forEach((action, index) => {
          allActions.push({ action, index, phase });
        });
      });
    }

    return allActions;
  };

  const allActions = getAllActions();

  // Keyboard navigation
  useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      if (event.key === "q" || event.key === "a") {
        event.preventDefault();

        if (allActions.length === 0) return;

        let newGlobalIndex: number;
        if (!selectedAction) {
          newGlobalIndex = event.key === "q" ? allActions.length - 1 : 0;
        } else {
          const currentGlobalIndex = allActions.findIndex(
            (actionData) =>
              actionData.phase === selectedAction.phase &&
              actionData.index === selectedAction.index
          );

          if (event.key === "q") {
            newGlobalIndex =
              currentGlobalIndex > 0
                ? currentGlobalIndex - 1
                : allActions.length - 1;
          } else {
            newGlobalIndex =
              currentGlobalIndex < allActions.length - 1
                ? currentGlobalIndex + 1
                : 0;
          }
        }

        const actionData = allActions[newGlobalIndex];
        setSelectedAction({ phase: actionData.phase, index: actionData.index });

      }
    };

    window.addEventListener("keydown", handleKeyDown);
    return () => window.removeEventListener("keydown", handleKeyDown);
  }, [
    selectedAction,
    allActions,
    selectedFunction,
  ]);

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
              selectedFunction={selectedFunction}
              phase={key}
              selectedAction={selectedAction}
              onActionSelect={(phase, index) =>
                setSelectedAction({ phase, index })
              }
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
          selectedFunction={selectedFunction}
          phase={null}
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
