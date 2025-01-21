import { Assertion } from "./components/Assertions";
import { PCGStmtVisualizationData } from "./types";

export type MirGraphNode = {
  id: string;
  block: number;
  stmts: string[];
  terminator: string;
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

export type PCSIterations = [string, string][][][];

const fetchJsonFile = async (filePath: string) => {
  const response = await fetch(filePath);
  return await response.json();
};

export async function getPCSIterations(
  functionName: string,
  block: number
): Promise<PCSIterations> {
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
    console.error(error);
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
    console.error(error);
    return [];
  }
};

export async function getPCGStmtVisualizationData(
  functionName: string,
  block: number,
  stmt: number
): Promise<PCGStmtVisualizationData> {
  return await fetchJsonFile(
    `data/${functionName}/block_${block}_stmt_${stmt}_pcg_data.json`
  );
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
