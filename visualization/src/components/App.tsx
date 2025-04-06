import React, { useState, useEffect, useCallback, useMemo } from "react";
import * as Viz from "@viz-js/viz";
import { fetchDotFile, openDotGraphInNewWindow } from "../dot_graph";

import PCGOps from "./BorrowsAndActions";
import {
  CurrentPoint,
  DagreEdge,
  PathData,
  PcgProgramPointData,
} from "../types";
import SymbolicHeap from "./SymbolicHeap";
import PathConditions from "./PathConditions";
import MirGraph from "./MirGraph";
import Assertions, { Assertion } from "./Assertions";
import {
  MirGraphEdge,
  MirGraphNode,
  getGraphData,
  getPathData,
  getPcgProgramPointData,
  getPaths,
  getPCSIterations,
  PCSIterations,
} from "../api";
import { filterNodesAndEdges, layoutUnsizedNodes } from "../mir_graph";
import { Selection, PCGGraphSelector } from "./PCSGraphSelector";
import FunctionSelector from "./FunctionSelector";
import PathSelector from "./PathSelector";
import LegendButton from "./LegendButton";
import { keydown } from "../effects";
import BorrowCheckerGraphs from "./BorrowCheckerGraphs";

function toDagreEdges(edges: MirGraphEdge[]): DagreEdge[] {
  return edges.map((edge, idx) => ({
    id: `${edge.source}-${edge.target}-${idx}`,
    source: edge.source,
    target: edge.target,
    data: { label: edge.label },
    type: "straight",
  }));
}

interface AppProps {
  initialFunction: string;
  initialPaths: number[][];
  initialAssertions: Assertion[];
  functions: Record<string, string>;
  initialPath?: number;
}

export const App: React.FC<AppProps> = ({
  initialFunction,
  initialPaths,
  initialAssertions,
  functions,
  initialPath = 0,
}) => {
  const [iterations, setIterations] = useState<PCSIterations>([]);
  const [selected, setSelected] = useState<Selection>(999); // HACK - always show last iteration
  const [pathData, setPathData] = useState<PathData | null>(null);
  const [pcgProgramPointData, setPcgProgramPointData] =
    useState<PcgProgramPointData | null>(null);
  const [currentPoint, setCurrentPoint] = useState<CurrentPoint>({
    type: "stmt",
    block: 0,
    stmt: 0,
  });

  const [selectedFunction, setSelectedFunction] = useState<string>(
    initialFunction || Object.keys(functions)[0]
  );
  const [selectedPath, setSelectedPath] = useState<number>(initialPath);
  const [paths, setPaths] = useState<number[][]>(initialPaths);
  const [assertions, setAssertions] =
    useState<Assertion[]>(initialAssertions);
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

  async function loadPCSDotGraph() {
    const dotGraph = document.getElementById("dot-graph");
    if (!dotGraph) {
      console.error("Dot graph element not found");
      return;
    }
    if (currentPoint.type !== "stmt") {
      dotGraph.innerHTML = "";
      return;
    }
    if (iterations.length <= currentPoint.stmt) {
      return;
    }
    const stmtIterations = iterations[currentPoint.stmt].flatMap(
      (phases) => phases
    );
    const filename =
      selected >= stmtIterations.length
        ? stmtIterations[stmtIterations.length - 1][1]
        : stmtIterations[selected][1];
    const dotFilePath = `data/${selectedFunction}/${filename}`;
    const dotData = await fetchDotFile(dotFilePath);

    Viz.instance().then(function (viz) {
      dotGraph.innerHTML = "";
      dotGraph.appendChild(viz.renderSVGElement(dotData));
    });
  }

  useEffect(() => {
    const graph = document.getElementById("dot-graph");
    if (showPCG) {
      graph.style.display = "block";
    } else {
      graph.style.display = "none";
    }
  }, [showPCG]);

  useEffect(() => {
    loadPCSDotGraph();
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
    const fetchPathData = async () => {
      if (paths.length === 0 || selectedPath >= paths.length) return;

      const currentPath = paths[selectedPath];
      const currentBlockIndex = currentPath.indexOf(
        currentPoint.type === "stmt"
          ? currentPoint.block
          : currentPoint.block1
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
    };

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

    fetchPathData();
    fetchPcgStmtVisualizationData();
  }, [selectedFunction, selectedPath, currentPoint, paths]);

  useEffect(() => {
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
  }, [selectedFunction, currentPoint]);

  useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      keydown(event, nodes, filteredNodes, setCurrentPoint);
    };
    window.addEventListener("keydown", handleKeyDown);
    return () => {
      window.removeEventListener("keydown", handleKeyDown);
    };
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

  const isBlockOnSelectedPath = useCallback(
    (block: number) => {
      if (paths.length === 0 || selectedPath >= paths.length) return false;
      return paths[selectedPath].includes(block);
    },
    [paths, selectedPath]
  );

  const pcsGraphSelector =
    currentPoint.type === "stmt" && iterations.length > currentPoint.stmt ? (
      <PCGGraphSelector
        iterations={iterations[currentPoint.stmt].flatMap((phases) => phases)}
        selected={selected}
        onSelect={setSelected}
      />
    ) : null;

  return (
    <div style={{ position: "relative", minHeight: "100vh" }}>
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
            if (
              currentPoint.type !== "stmt" ||
              iterations.length <= currentPoint.stmt
            ) {
              return;
            }
            const stmtIterations = iterations[currentPoint.stmt].flatMap(
              (phases) => phases
            );
            const filename =
              selected >= stmtIterations.length
                ? stmtIterations[stmtIterations.length - 1][1]
                : stmtIterations[selected][1];
            const dotFilePath = `data/${selectedFunction}/${filename}`;
            openDotGraphInNewWindow(dotFilePath);
          }}
        >
          Open in New Window
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
          <PCGOps data={pcgProgramPointData} />
          {"latest" in pcgProgramPointData && (
            <LatestDisplay latest={pcgProgramPointData.latest} />
          )}
        </>
      )}
      {pathData && (
        <div style={{ position: "absolute", top: "20px", right: "20px" }}>
          <SymbolicHeap heap={pathData.heap} />
          <PathConditions pcs={pathData.pcs} />
          <Assertions assertions={assertions} />
        </div>
      )}
      {pcsGraphSelector &&
        showPCGSelector &&
        currentPoint.type === "stmt" && (
          <PCGGraphSelector
            iterations={iterations[currentPoint.stmt].flatMap(
              (phases) => phases
            )}
            selected={selected}
            onSelect={setSelected}
          />
        )}
    </div>
  );
};

function LatestDisplay({ latest }: { latest: Record<string, string> }) {
  return (
    <div>
      {Object.entries(latest).map(([place, location]) => (
        <div key={place}>{`${place} -> ${location}`}</div>
      ))}
    </div>
  );
}
