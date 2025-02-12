import React from "react";

export type Selection = number;

export function PCSGraphSelector({
  iterations,
  selected,
  onSelect,
}: {
  iterations: [string, string][];
  selected: Selection;
  onSelect: (selection: Selection) => void;
}) {
  let selectedIdx =
    selected > iterations.length ? iterations.length - 1 : selected;
  return (
    <div style={{ position: "fixed", right: "50px", top: "20px" }}>
      {iterations.map(([name, filename], index) => (
        <div
          key={filename}
          style={{
            border: "1px solid #000",
            padding: "10px",
            backgroundColor: selectedIdx === index ? "lightgreen" : "transparent",
            cursor: "pointer",
          }}
          onClick={() => onSelect(index)}
        >
          {name}
        </div>
      ))}
    </div>
  );
}
