import { Assertion } from "./components/Assertions";
import {
  CurrentPoint,
  PcgProgramPointData,
  PCGStmtVisualizationData,
} from "./types";

export type MirStmt = {
  stmt: string;
  loans_invalidated_start: string[];
  loans_invalidated_mid: string[];
  borrows_in_scope_start: string[];
  borrows_in_scope_mid: string[];
};

export type MirGraphNode = {
  id: string;
  block: number;
  stmts: MirStmt[];
  terminator: MirStmt;
};

export type MirGraphEdge = {
  source: string;
  target: string;
  label: string;
};

type MirGraph = {
  nodes: MirGraphNode[];
  edges: MirGraphEdge[];
};

export type StmtActions = Record<string, string[]>;

export type PcgStmt = {
  at_phase: [string, string][];
  actions: StmtActions;
};

export type PcgBlockDotGraphs = PcgStmt[];

const fetchJsonFile = async (filePath: string) => {
  const response = await fetch(filePath);
  return await response.json();
};

export async function getPCSIterations(
  functionName: string,
  block: number
): Promise<PcgBlockDotGraphs> {
  const iterations = await fetchJsonFile(
    `data/${functionName}/block_${block}_iterations.json`
  );
  return iterations;
}

export async function getGraphData(func: string): Promise<MirGraph> {
  const graphFilePath = `data/${func}/mir.json`;
  return await fetchJsonFile(graphFilePath);
}

export async function getFunctions(): Promise<Record<string, string>> {
  return await fetchJsonFile("data/functions.json");
}

export const getPaths = async (functionName: string) => {
  try {
    const paths: number[][] = await fetchJsonFile(
      `data/${functionName}/paths.json`
    );
    return paths;
  } catch (error) {
    // Paths are only present for symbolic execution
    return [];
  }
};

export const getAssertions = async (functionName: string) => {
  try {
    const assertions: Assertion[] = await fetchJsonFile(
      `data/${functionName}/assertions.json`
    );
    return assertions;
  } catch (error) {
    // Assertions are only present for symbolic execution
    return [];
  }
};

export async function getPcgProgramPointData(
  functionName: string,
  currentPoint: CurrentPoint
): Promise<PcgProgramPointData> {
  let path =
    currentPoint.type === "stmt"
      ? `block_${currentPoint.block}_stmt_${currentPoint.stmt}`
      : `block_${currentPoint.block1}_term_block_${currentPoint.block2}`;

  return await fetchJsonFile(`data/${functionName}/${path}_pcg_data.json`);
}

export async function getPathData(
  functionName: string,
  path: number[],
  point:
    | {
        stmt: number;
      }
    | {
        terminator: number;
      }
) {
  const last_component =
    "stmt" in point ? `stmt_${point.stmt}` : `bb${point.terminator}_transition`;
  const endpoint = `data/${functionName}/path_${path.map((block) => `bb${block}`).join("_")}_${last_component}.json`;
  return await fetchJsonFile(endpoint);
}
