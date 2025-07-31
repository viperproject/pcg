import React, { useState, useEffect } from "react";
import {
  EvalStmtPhase,
  PcgAction,
  PcgActions,
  PcgProgramPointData,
  PCGStmtVisualizationData,
  PcgSuccessorVisualizationData,
  SelectedAction,
} from "../types";

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
              title={
                typeof action === "object" ? action.debug_context : undefined
              }
            >
              {typeof action === "object" ? action.kind : action}
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
  // Drag state
  const [isDragging, setIsDragging] = useState(false);
  const [position, setPosition] = useState({ x: 0, y: 0 });
  const [dragStart, setDragStart] = useState({ x: 0, y: 0 });
  const [initialized, setInitialized] = useState(false);

  // Collect all actions with their phase info for keyboard navigation
  const getAllActions = () => {
    const allActions: Array<{
      action: PcgAction;
      index: number;
      phase: EvalStmtPhase;
    }> = [];

    // Check if data.actions is an object (PCGStmtVisualizationData) or array (PcgSuccessorVisualizationData)
    if (!Array.isArray(data.actions)) {
      // data is PCGStmtVisualizationData
      const stmtData = data as PCGStmtVisualizationData;
      const phases = [
        "pre_operands",
        "post_operands",
        "pre_main",
        "post_main",
      ] as const;
      phases.forEach((phase) => {
        stmtData.actions[phase].forEach((action, index) => {
          allActions.push({ action, index, phase });
        });
      });
    }

    return allActions;
  };

  const allActions = getAllActions();

  // Initialize position on first render
  useEffect(() => {
    if (!initialized) {
      setPosition({
        x: window.innerWidth - 320,
        y: window.innerHeight - 200,
      });
      setInitialized(true);
    }
  }, [initialized]);

  // Drag handlers
  const handleMouseDown = (event: React.MouseEvent) => {
    setIsDragging(true);
    setDragStart({
      x: event.clientX - position.x,
      y: event.clientY - position.y,
    });
  };

  const handleMouseMove = (event: MouseEvent) => {
    if (isDragging) {
      setPosition({
        x: event.clientX - dragStart.x,
        y: event.clientY - dragStart.y,
      });
    }
  };

  const handleMouseUp = () => {
    setIsDragging(false);
  };

  // Mouse event listeners for dragging
  useEffect(() => {
    if (isDragging) {
      window.addEventListener("mousemove", handleMouseMove);
      window.addEventListener("mouseup", handleMouseUp);
      return () => {
        window.removeEventListener("mousemove", handleMouseMove);
        window.removeEventListener("mouseup", handleMouseUp);
      };
    }
  }, [isDragging, dragStart]);

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
  }, [selectedAction, allActions, selectedFunction]);

  let content;
  // Check if data.actions is an object (PCGStmtVisualizationData) or array (PcgSuccessorVisualizationData)
  if (!Array.isArray(data.actions)) {
    // data is PCGStmtVisualizationData
    const stmtData = data as PCGStmtVisualizationData;
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
              actions={stmtData.actions[key]}
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
    // data is PcgSuccessorVisualizationData
    const successorData = data as PcgSuccessorVisualizationData;
    content = (
      <>
        <h4>Actions</h4>
        <PcgActionsDisplay
          actions={successorData.actions}
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
        top: `${position.y}px`,
        left: `${position.x}px`,
        backgroundColor: "white",
        boxShadow: "0 0 10px rgba(0,0,0,0.1)",
        padding: "10px",
        maxWidth: "300px",
        overflowY: "auto",
        maxHeight: "80vh",
        cursor: isDragging ? "grabbing" : "grab",
        userSelect: "none",
      }}
      onMouseDown={handleMouseDown}
    >
      {content}
      <div style={{ marginTop: "10px", fontSize: "12px", color: "#666" }}>
        Press 'q'/'a' to navigate between actions
      </div>
    </div>
  );
}
