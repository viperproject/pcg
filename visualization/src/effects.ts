import {
  getPathData,
  getPCSIterations,
  MirGraphNode,
  MirStmt,
  PcgBlockDotGraphs,
} from "./api";
import { CurrentPoint, PathData } from "./types";

export function reloadIterations(
  selectedFunction: string,
  currentPoint: CurrentPoint,
  setIterations: React.Dispatch<React.SetStateAction<PcgBlockDotGraphs>>
) {
  if (currentPoint.type != "stmt") {
    setIterations([]);
    return;
  }
  const fetchIterations = async () => {
    const iterations = await getPCSIterations(
      selectedFunction,
      currentPoint.block
    );
    setIterations(iterations);
  };

  fetchIterations();
}

export async function reloadPathData(
  selectedFunction: string,
  selectedPath: number,
  currentPoint: CurrentPoint,
  paths: number[][],
  setPathData: React.Dispatch<React.SetStateAction<PathData>>
) {
  if (paths.length === 0 || selectedPath >= paths.length) return;

  const currentPath = paths[selectedPath];
  const currentBlockIndex = currentPath.indexOf(
    currentPoint.type === "stmt" ? currentPoint.block : currentPoint.block1
  );

  if (currentBlockIndex === -1) {
    setPathData(null);
    return;
  }

  const pathToCurrentBlock = currentPath.slice(0, currentBlockIndex + 1);

  try {
    const data: PathData = await getPathData(
      selectedFunction,
      pathToCurrentBlock,
      currentPoint.type === "stmt"
        ? {
            stmt: currentPoint.stmt,
          }
        : {
            terminator: currentPoint.block2,
          }
    );
    setPathData(data);
  } catch (error) {
    console.error("Error fetching path data:", error);
  }
}

export function addKeyDownListener(
  nodes: MirGraphNode[],
  filteredNodes: MirGraphNode[],
  setCurrentPoint: React.Dispatch<React.SetStateAction<CurrentPoint>>
) {
  const handleKeyDown = (event: KeyboardEvent) => {
    keydown(event, nodes, filteredNodes, setCurrentPoint);
  };
  console.log("add keydown listener");
  window.addEventListener("keydown", handleKeyDown);
  return () => {
    console.log("removing keydown listener");
    window.removeEventListener("keydown", handleKeyDown);
  };
}

function keydown(
  event: KeyboardEvent,
  nodes: MirGraphNode[],
  filteredNodes: MirGraphNode[],
  setCurrentPoint: React.Dispatch<React.SetStateAction<CurrentPoint>>
) {
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

      const isSelectable = (node: { stmts: MirStmt[] }, idx: number) => {
        return idx >= 0 && idx <= node.stmts.length;
      };

      const getNextStmtIdx = (node: { stmts: MirStmt[] }, from: number) => {
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
            selectedAction: null,
          };
        } else {
          const nextBlockIdx =
            (currBlockIdx - 1 + filteredNodes.length) % filteredNodes.length;
          const data = filteredNodes[nextBlockIdx];
          return {
            type: "stmt",
            block: data.block,
            stmt: data.stmts.length,
            selectedAction: null,
          };
        }
      }
    });
  } else if (event.key >= "0" && event.key <= "9") {
    const newBlock = parseInt(event.key);
    setCurrentPoint({
      type: "stmt",
      block: newBlock,
      stmt: 0,
      selectedAction: null,
    });
  }
}
