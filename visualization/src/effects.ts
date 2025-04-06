import { MirGraphNode } from "./api";
import { CurrentPoint } from "./types";

export const keydown = (
  event: KeyboardEvent,
  nodes: MirGraphNode[],
  filteredNodes: MirGraphNode[],
  setCurrentPoint: React.Dispatch<React.SetStateAction<CurrentPoint>>
) => {
  if (
    event.key === "ArrowUp" ||
    event.key === "ArrowDown" ||
    event.key === "j" ||
    event.key === "k"
  ) {
    event.preventDefault(); // Prevent scrolling
    const direction =
      event.key === "ArrowUp" || event.key === "k" ? "up" : "down";

    setCurrentPoint((prevPoint: CurrentPoint) => {
      if (prevPoint.type === "terminator") {
        return; // TODO
      }
      const currentNode = nodes.find((node) => node.block === prevPoint.block);
      if (!currentNode) return prevPoint;

      const isSelectable = (node: { stmts: string[] }, idx: number) => {
        return idx >= 0 && idx <= node.stmts.length;
      };

      const getNextStmtIdx = (node: { stmts: string[] }, from: number) => {
        const offset = direction === "up" ? -1 : 1;
        let idx = from + offset;
        if (isSelectable(node, idx)) {
          return idx;
        } else {
          return null;
        }
      };

      const nextStmtIdx = getNextStmtIdx(currentNode, prevPoint.stmt);
      if (nextStmtIdx !== null) {
        return { ...prevPoint, stmt: nextStmtIdx };
      } else {
        const currBlockIdx = filteredNodes.findIndex(
          (node) => node.block === prevPoint.block
        );
        if (direction === "down") {
          const nextBlockIdx = (currBlockIdx + 1) % filteredNodes.length;
          const data = filteredNodes[nextBlockIdx];
          return {
            type: "stmt",
            block: filteredNodes[nextBlockIdx].block,
            stmt: getNextStmtIdx(data, -1),
          };
        } else {
          const nextBlockIdx =
            (currBlockIdx - 1 + filteredNodes.length) % filteredNodes.length;
          const data = filteredNodes[nextBlockIdx];
          return {
            type: "stmt",
            block: data.block,
            stmt: data.stmts.length,
          };
        }
      }
    });
  } else if (event.key >= "0" && event.key <= "9") {
    const newBlock = parseInt(event.key);
    setCurrentPoint({ type: "stmt", block: newBlock, stmt: 0 });
  }
};
