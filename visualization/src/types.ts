import { MirStmt } from "./api";

export type EvalStmtPhase =
  | "pre_operands"
  | "post_operands"
  | "pre_main"
  | "post_main";

export type SelectedAction = {
  phase: EvalStmtPhase;
  index: number;
};

export type CurrentPoint =
  | {
      type: "stmt";
      block: number;
      stmt: number;
      selectedAction: SelectedAction | null;
    }
  | {
      type: "terminator";
      block1: number;
      block2: number;
    };

export type BasicBlockData = {
  block: number;
  stmts: MirStmt[];
  terminator: MirStmt;
};

export type DagreInputNode<T> = {
  id: string;
};

export type DagreEdge = {
  id: string;
  source: string;
  target: string;
  data: {
    label: string;
  };
  type: string;
};

export type DagreNode<T> = {
  id: string;
  data: T;
  x: number;
  y: number;
  width: number;
  height: number;
};

export type Place = string;

export type MaybeOldPlace =
  | Place
  | {
      place: Place;
      at?: string;
    };

export type Borrow = {
  assigned_place: MaybeOldPlace;
  borrowed_place: MaybeOldPlace;
  is_mut: boolean;
  kind: string;
};

export type Reborrow = {
  blocked_place: MaybeOldPlace;
  assigned_place: MaybeOldPlace;
  is_mut: boolean;
};

export type BorrowAction = {
  action: "AddBorrow" | "RemoveBorrow";
  borrow: Borrow;
};

export type ReborrowAction =
  | {
      action: "AddReborrow" | "RemoveReborrow";
      reborrow: Reborrow;
    }
  | {
      action: "ExpandPlace";
      place: MaybeOldPlace;
    };

export type Conditioned<T> = {
  value: T;
  conditions: any;
};

export type PlaceExpand = {
  base: PCGNode<MaybeOldPlace>;
  expansion: PCGNode<MaybeOldPlace>[];
};

export type Weaken = {
  place: string;
  old: string;
  new: string;
};

export type MaybeRemotePlace = string | MaybeOldPlace;

export type RegionProjection<T> = {
  place: T;
  region: string;
};

export type PCGNode<T> = RegionProjection<T> | T;
export type LocalNode = PCGNode<MaybeOldPlace>;

export type RegionProjectionMember = {
  inputs: PCGNode<MaybeRemotePlace>[];
  outputs: LocalNode[];
};

type BorrowPCGEdge = string;

export type BorrowPCGUnblockAction = {
  edge: BorrowPCGEdge;
};

export type PcgAction =
  | string
  | {
      kind: string;
      debug_context: string | null;
    };

export type PcgActions = PcgAction[];

export type PathData = {
  heap: Record<string, { value: string; ty: string; old: boolean }>;
  pcs: string;
};

export type PCGStmtVisualizationData = {
  actions: EvalStmtData<PcgActions>;
};

export type PcgSuccessorVisualizationData = {
  actions: string[];
};

export type PcgProgramPointData =
  | PCGStmtVisualizationData
  | PcgSuccessorVisualizationData;

type EvalStmtData<T> = {
  pre_operands: T;
  post_operands: T;
  pre_main: T;
  post_main: T;
};
