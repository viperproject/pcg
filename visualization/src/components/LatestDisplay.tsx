import React from "react";
export function LatestDisplay({ latest }: { latest: Record<string, string> }) {
  return (
    <div>
      {Object.entries(latest).map(([place, location]) => (
        <div key={place}>{`${place} -> ${location}`}</div>
      ))}
    </div>
  );
}
