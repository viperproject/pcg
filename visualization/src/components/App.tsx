import React, {
  useState,
  useEffect,
  useCallback,
  useMemo,
  useRef,
} from "react";
import * as Viz from "@viz-js/viz";
import { fetchDotFile, openDotGraphInNewWindow } from "../dot_graph";

import PCGOps from "./PcgActionsDisplay";
import {
  CurrentPoint,
  PathData,
  PcgProgramPointData,
  SelectedAction,
} from "../types";
import SymbolicHeap from "./SymbolicHeap";
import PathConditions from "./PathConditions";
import MirGraph from "./MirGraph";
import Assertions, { Assertion } from "./Assertions";
import {
  MirGraphEdge,
  MirGraphNode,
  getGraphData,
  getPcgProgramPointData,
  getPaths,
  PcgBlockDotGraphs,
  StmtActions,
  PcgStmt,
} from "../api";
import {
  filterNodesAndEdges,
  layoutUnsizedNodes,
  toDagreEdges,
} from "../mir_graph";
import { Selection, PCGGraphSelector } from "./PCSGraphSelector";
import FunctionSelector from "./FunctionSelector";
import PathSelector from "./PathSelector";
import LegendButton from "./LegendButton";
import {
  addKeyDownListener,
  reloadPathData,
  reloadIterations,
} from "../effects";
import BorrowCheckerGraphs from "./BorrowCheckerGraphs";

const getActionGraphFilename = (
  selectedFunction: string,
  actionGraphFilenames: string[],
  actionIndex: number
): string | null => {
  return `data/${selectedFunction}/${actionGraphFilenames[actionIndex]}`;
};

function getPCGDotGraphFilename(
  currentPoint: CurrentPoint,
  selectedFunction: string,
  selected: number,
  graphs: PcgBlockDotGraphs
): string | null {
  if (currentPoint.type !== "stmt" || graphs.length <= currentPoint.stmt) {
    return null;
  }
  const selectedAction = getSelectedAction(currentPoint);
  if (selectedAction) {
    const iterationActions = getIterationActions(graphs, currentPoint);
    const actionGraphFilenames = iterationActions[selectedAction.phase];
    return getActionGraphFilename(
      selectedFunction,
      actionGraphFilenames,
      selectedAction.index
    );
  }

  const phases: [string, string][] = graphs[currentPoint.stmt].at_phase;

  // Handle deselection case
  if (selected < 0) {
    return null;
  }

  const filename: string =
    selected >= phases.length
      ? phases[phases.length - 1][1]
      : phases[selected][1];
  return `data/${selectedFunction}/${filename}`;
}

interface AppProps {
  initialFunction: string;
  initialPaths: number[][];
  initialAssertions: Assertion[];
  functions: Record<string, string>;
  initialPath?: number;
}

function getSelectedAction(currentPoint: CurrentPoint): SelectedAction | null {
  if (currentPoint.type !== "stmt") {
    return null;
  }
  return currentPoint.selectedAction;
}

export const App: React.FC<AppProps> = ({
  initialFunction,
  initialPaths,
  initialAssertions,
  functions,
  initialPath = 0,
}) => {
  const [iterations, setIterations] = useState<PcgBlockDotGraphs>([]);
  const [selected, setSelected] = useState<Selection>(999); // HACK - always show last iteration
  const [pathData, setPathData] = useState<PathData | null>(null);
  const [pcgProgramPointData, setPcgProgramPointData] =
    useState<PcgProgramPointData | null>(null);
  const [currentPoint, setCurrentPoint] = useState<CurrentPoint>({
    type: "stmt",
    block: 0,
    stmt: 0,
    selectedAction: null,
  });

  const [selectedFunction, setSelectedFunction] = useState<string>(
    initialFunction || Object.keys(functions)[0]
  );
  const [selectedPath, setSelectedPath] = useState<number>(initialPath);
  const [paths, setPaths] = useState<number[][]>(initialPaths);
  const [assertions, setAssertions] = useState<Assertion[]>(initialAssertions);
  const [nodes, setNodes] = useState<MirGraphNode[]>([]);
  const [edges, setEdges] = useState<MirGraphEdge[]>([]);
  const [showPathBlocksOnly, setShowPathBlocksOnly] = useState(
    localStorage.getItem("showPathBlocksOnly") === "true"
  );
  const [showUnwindEdges, setShowUnwindEdges] = useState(false);
  const [showPCG, setShowPCG] = useState(
    localStorage.getItem("showPCG") !== "false"
  );
  const [showPCGSelector, setShowPCGSelector] = useState(
    localStorage.getItem("showPCGSelector") !== "false"
  );
  const [showPCGOps, setShowPCGOps] = useState(
    localStorage.getItem("showPCGOps") !== "false"
  );

  // State for panel resizing
  const [leftPanelWidth, setLeftPanelWidth] = useState<string>(
    localStorage.getItem("leftPanelWidth") || "50%"
  );
  const [isDragging, setIsDragging] = useState<boolean>(false);
  const dividerRef = useRef<HTMLDivElement>(null);

  const { filteredNodes, filteredEdges } = filterNodesAndEdges(nodes, edges, {
    showUnwindEdges,
    path:
      showPathBlocksOnly && selectedPath < paths.length
        ? paths[selectedPath]
        : null,
  });

  const layoutResult = useMemo(() => {
    return layoutUnsizedNodes(filteredNodes, filteredEdges);
  }, [filteredNodes, filteredEdges]);

  const dagreNodes = layoutResult.nodes;
  const dagreEdges = useMemo(() => {
    return toDagreEdges(filteredEdges);
  }, [filteredEdges]);

  async function loadPCGDotGraph() {
    const dotGraph = document.getElementById("pcg-graph");
    if (!dotGraph) {
      console.error("Dot graph element not found");
      return;
    }
    const dotFilePath = getPCGDotGraphFilename(
      currentPoint,
      selectedFunction,
      selected,
      iterations
    );
    if (!dotFilePath) {
      dotGraph.innerHTML = "";
    } else {
      const dotData = await fetchDotFile(dotFilePath);

      Viz.instance().then(function (viz) {
        dotGraph.innerHTML = "";
        dotGraph.appendChild(viz.renderSVGElement(dotData));
      });
    }
  }

  useEffect(() => {
    const graph = document.getElementById("pcg-graph");
    if (showPCG) {
      graph.style.display = "block";
    } else {
      graph.style.display = "none";
    }
  }, [showPCG]);

  useEffect(() => {
    loadPCGDotGraph();
  }, [iterations, currentPoint, selectedFunction, selected]);

  useEffect(() => {
    if (selectedFunction) {
      (async function () {
        const mirGraph = await getGraphData(selectedFunction);
        setNodes(mirGraph.nodes);
        setEdges(mirGraph.edges);
        setPaths(await getPaths(selectedFunction));
      })();
    }
  }, [selectedFunction]);

  useEffect(() => {
    const fetchPcgStmtVisualizationData = async () => {
      try {
        const pcgStmtVisualizationData = await getPcgProgramPointData(
          selectedFunction,
          currentPoint
        );
        setPcgProgramPointData(pcgStmtVisualizationData);
      } catch (error) {
        console.error("Error fetching pcg stmt visualization data:", error);
      }
    };

    reloadPathData(
      selectedFunction,
      selectedPath,
      currentPoint,
      paths,
      setPathData
    );
    fetchPcgStmtVisualizationData();
  }, [selectedFunction, selectedPath, currentPoint, paths]);

  useEffect(() => {
    reloadIterations(selectedFunction, currentPoint, setIterations);
  }, [selectedFunction, currentPoint]);

  useEffect(() => {
    return addKeyDownListener(nodes, filteredNodes, setCurrentPoint);
  }, [nodes, showPathBlocksOnly]);

  function addLocalStorageCallback(key: string, value: any) {
    useEffect(() => {
      localStorage.setItem(key, value.toString());
    }, [value]);
  }

  addLocalStorageCallback("selectedFunction", selectedFunction);
  addLocalStorageCallback("selectedPath", selectedPath);
  addLocalStorageCallback("showPathBlocksOnly", showPathBlocksOnly);
  addLocalStorageCallback("showPCG", showPCG);
  addLocalStorageCallback("showPCGSelector", showPCGSelector);
  addLocalStorageCallback("showPCGOps", showPCGOps);
  addLocalStorageCallback("leftPanelWidth", leftPanelWidth);

  const isBlockOnSelectedPath = useCallback(
    (block: number) => {
      if (paths.length === 0 || selectedPath >= paths.length) return false;
      return paths[selectedPath].includes(block);
    },
    [paths, selectedPath]
  );

  const pcgGraphSelector =
    showPCGSelector &&
    currentPoint.type === "stmt" &&
    iterations.length > currentPoint.stmt ? (
      <PCGGraphSelector
        iterations={iterations[currentPoint.stmt].at_phase}
        // If there's a selected action, we're not currently associated with a phase
        selected={getSelectedAction(currentPoint) === null ? selected : null}
        onSelect={(newIdx) => {
          setCurrentPoint({
            ...currentPoint,
            selectedAction: null,
          });
          setSelected(newIdx);
        }}
      />
    ) : null;

  // Divider drag handlers
  const handleMouseDown = (e: React.MouseEvent) => {
    setIsDragging(true);
    e.preventDefault();
  };

  const handleMouseUp = useCallback(() => {
    setIsDragging(false);
  }, []);

  const handleMouseMove = useCallback(
    (e: MouseEvent) => {
      if (!isDragging) return;

      const rootElement = document.getElementById("root");
      if (!rootElement) return;

      const rootRect = rootElement.getBoundingClientRect();
      const newLeftWidth = ((e.clientX - rootRect.left) / rootRect.width) * 100;

      // Enforce min/max constraints (e.g., 20% - 80%)
      const clampedWidth = Math.min(Math.max(newLeftWidth, 20), 80);
      setLeftPanelWidth(`${clampedWidth}%`);
    },
    [isDragging]
  );

  // Add and remove event listeners for dragging
  useEffect(() => {
    document.addEventListener("mousemove", handleMouseMove);
    document.addEventListener("mouseup", handleMouseUp);

    return () => {
      document.removeEventListener("mousemove", handleMouseMove);
      document.removeEventListener("mouseup", handleMouseUp);
    };
  }, [handleMouseMove, handleMouseUp]);

  return (
    <div style={{ display: "flex", width: "100%" }}>
      <div
        style={{
          position: "relative",
          minHeight: "100vh",
          flex: "none",
          width: leftPanelWidth,
          overflow: "auto",
        }}
      >
        <div>
          <FunctionSelector
            functions={functions}
            selectedFunction={selectedFunction}
            onChange={setSelectedFunction}
          />
          <br />
          <PathSelector
            paths={paths}
            selectedPath={selectedPath}
            setSelectedPath={setSelectedPath}
            showPathBlocksOnly={showPathBlocksOnly}
            setShowPathBlocksOnly={setShowPathBlocksOnly}
          />
          <label>
            <input
              type="checkbox"
              checked={showPCG}
              onChange={(e) => setShowPCG(e.target.checked)}
            />
            Show PCG
          </label>
          <button
            style={{ marginLeft: "10px" }}
            onClick={async () => {
              const dotFilePath = getPCGDotGraphFilename(
                currentPoint,
                selectedFunction,
                selected,
                iterations
              );
              if (dotFilePath) {
                openDotGraphInNewWindow(dotFilePath);
              }
            }}
          >
            Open Current PCG in New Window
          </button>
          <br />
          <BorrowCheckerGraphs
            currentPoint={currentPoint}
            selectedFunction={selectedFunction}
          />
          <br />
          <label>
            <input
              type="checkbox"
              checked={showPCGSelector}
              onChange={(e) => setShowPCGSelector(e.target.checked)}
            />
            Show PCG selector
          </label>
          <br />
          <label>
            <input
              type="checkbox"
              checked={showPCGOps}
              onChange={(e) => setShowPCGOps(e.target.checked)}
            />
            Show PCG operations
          </label>
          <LegendButton selectedFunction={selectedFunction} />
        </div>
        <MirGraph
          nodes={dagreNodes}
          edges={dagreEdges}
          mirNodes={nodes}
          currentPoint={currentPoint}
          setCurrentPoint={setCurrentPoint}
          height={layoutResult.height}
          isBlockOnSelectedPath={isBlockOnSelectedPath}
        />
        {pcgProgramPointData && showPCGOps && (
          <>
            <PCGOps
              data={pcgProgramPointData}
              selectedFunction={selectedFunction}
              selectedAction={getSelectedAction(currentPoint)}
              setSelectedAction={(selectedAction) => {
                if (currentPoint.type === "stmt") {
                  setCurrentPoint({
                    ...currentPoint,
                    selectedAction,
                  });
                }
              }}
            />
          </>
        )}
        {pathData && (
          <div style={{ position: "absolute", top: "20px", right: "20px" }}>
            <SymbolicHeap heap={pathData.heap} />
            <PathConditions pcs={pathData.pcs} />
            <Assertions assertions={assertions} />
          </div>
        )}
        {pcgGraphSelector}
      </div>

      {/* Draggable divider */}
      <div
        ref={dividerRef}
        style={{
          width: "10px",
          cursor: "col-resize",
          background: "#ccc",
          position: "relative",
          zIndex: 100,
          display: showPCG ? "block" : "none",
        }}
        onMouseDown={handleMouseDown}
      >
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "2px",
            width: "6px",
            height: "30px",
            background: "#999",
            borderRadius: "3px",
            transform: "translateY(-50%)",
          }}
        ></div>
      </div>

      <div id="pcg-graph" style={{ flex: 1, overflow: "auto" }}></div>
    </div>
  );
};

function getIterationActions(
  dotGraphs: PcgBlockDotGraphs,
  currentPoint: CurrentPoint
): StmtActions {
  if (currentPoint.type !== "stmt" || dotGraphs.length <= currentPoint.stmt) {
    return {};
  }
  const stmt = dotGraphs[currentPoint.stmt];
  return stmt.actions;
}
