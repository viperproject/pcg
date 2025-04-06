import React, { useState, useEffect, useCallback, useMemo } from "react";
import { createRoot } from "react-dom/client";
import ReactDOMServer from "react-dom/server";
import * as dagre from "@dagrejs/dagre";
import * as Viz from "@viz-js/viz";
import { fetchDotFile, openDotGraphInNewWindow } from "./dot_graph";

import PCGOps from "./components/BorrowsAndActions";
import { computeTableHeight } from "./components/BasicBlockTable";
import {
  BasicBlockData,
  CurrentPoint,
  DagreEdge,
  DagreInputNode,
  DagreNode,
  PathData,
  PcgProgramPointData,
} from "./types";
import SymbolicHeap from "./components/SymbolicHeap";
import PathConditions from "./components/PathConditions";
import MirGraph from "./components/MirGraph";
import Assertions, { Assertion } from "./components/Assertions";
import {
  MirGraphEdge,
  MirGraphNode,
  getAssertions,
  getFunctions,
  getGraphData,
  getPathData,
  getPcgProgramPointData,
  getPaths,
  getPCSIterations,
  PCSIterations,
} from "./api";
import { filterNodesAndEdges } from "./mir_graph";
import { Selection, PCGGraphSelector } from "./components/PCSGraphSelector";
import FunctionSelector from "./components/FunctionSelector";
import PathSelector from "./components/PathSelector";
import LegendButton from "./components/LegendButton";

const layoutSizedNodes = (
  nodes: DagreInputNode<BasicBlockData>[],
  edges: any
) => {
  const g = new dagre.graphlib.Graph().setDefaultEdgeLabel(() => ({}));
  g.setGraph({ ranksep: 100, rankdir: "TB", marginy: 100 });

  edges.forEach((edge: any) => g.setEdge(edge.source, edge.target));
  nodes.forEach((node) => g.setNode(node.id, node));

  dagre.layout(g);

  let height = g.graph().height;
  if (!isFinite(height)) {
    height = null;
  }

  return {
    nodes: nodes as DagreNode<BasicBlockData>[],
    edges,
    height,
  };
};

function toDagreEdges(edges: MirGraphEdge[]): DagreEdge[] {
  return edges.map((edge, idx) => ({
    id: `${edge.source}-${edge.target}-${idx}`,
    source: edge.source,
    target: edge.target,
    data: { label: edge.label },
    type: "straight",
  }));
}

function layoutUnsizedNodes(
  nodes: MirGraphNode[],
  edges: { source: string; target: string }[]
): {
  nodes: DagreNode<BasicBlockData>[];
  height: number;
} {
  const heightCalculatedNodes = nodes.map((node) => {
    return {
      id: node.id,
      data: {
        block: node.block,
        stmts: node.stmts,
        terminator: node.terminator,
      },
      height: computeTableHeight(node),
      width: 300,
    };
  });
  const g = layoutSizedNodes(heightCalculatedNodes, edges);
  return {
    nodes: g.nodes,
    height: g.height,
  };
}

async function main() {
  const _viz = await Viz.instance();
  const functions = await getFunctions();
  let initialFunction = localStorage.getItem("selectedFunction");
  if (!initialFunction || !Object.keys(functions).includes(initialFunction)) {
    initialFunction = Object.keys(functions)[0];
  }
  const initialPaths = await getPaths(initialFunction);
  const initialAssertions = await getAssertions(initialFunction);

  let initialPath = 0;
  let initialPathStr = localStorage.getItem("selectedPath");
  if (initialPathStr) {
    initialPath = parseInt(initialPathStr);
    if (initialPath >= initialPaths.length) {
      initialPath = 0;
    }
  } else {
    initialPath = 0;
  }

  const App: React.FC<{}> = () => {
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
      initialFunction || functions[0]
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
            const currentNode = nodes.find(
              (node) => node.block === prevPoint.block
            );
            if (!currentNode) return prevPoint;

            const isSelectable = (node: { stmts: string[] }, idx: number) => {
              return idx >= 0 && idx <= node.stmts.length;
            };

            const getNextStmtIdx = (
              node: { stmts: string[] },
              from: number
            ) => {
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
                  (currBlockIdx - 1 + filteredNodes.length) %
                  filteredNodes.length;
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
          <button
            style={{ marginLeft: "10px" }}
            onClick={async () => {
              if (currentPoint.type == "stmt") {
                const dotFilePath = `data/${selectedFunction}/bc_facts_graph_bb${currentPoint.block}_${currentPoint.stmt}_start.dot`;
                openDotGraphInNewWindow(dotFilePath);
              }
            }}
          >
            Polonius Subset Graph (This Location [Start])
          </button>
          <br />
          <button
            style={{ marginLeft: "10px" }}
            onClick={async () => {
              if (currentPoint.type == "stmt") {
                const dotFilePath = `data/${selectedFunction}/bc_facts_graph_bb${currentPoint.block}_${currentPoint.stmt}_mid.dot`;
                openDotGraphInNewWindow(dotFilePath);
              }
            }}
          >
            Polonius Subset Graph (This Location [Mid])
          </button>
          <br />
          <button
            style={{ marginLeft: "10px" }}
            onClick={async () => {
              if (currentPoint.type == "stmt") {
                const dotFilePath = `data/${selectedFunction}/bc_facts_graph_anywhere.dot`;
                openDotGraphInNewWindow(dotFilePath);
              }
            }}
          >
            Polonius Subset Graph (Anywhere)
          </button>
          <br />
          <button
            style={{ marginLeft: "10px" }}
            onClick={async () => {
              if (currentPoint.type == "stmt") {
                const dotFilePath = `data/${selectedFunction}/region_inference_outlives.dot`;
                openDotGraphInNewWindow(dotFilePath);
              }
            }}
          >
            Region Inference Outlives Graph
          </button>
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

  const rootElement = document.getElementById("root");
  if (rootElement) {
    const root = createRoot(rootElement);
    root.render(<App />);
  }
}

function LatestDisplay({ latest }: { latest: Record<string, string> }) {
  return (
    <div>
      {Object.entries(latest).map(([place, location]) => (
        <div key={place}>{`${place} -> ${location}`}</div>
      ))}
    </div>
  );
}

main();
