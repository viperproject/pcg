export type CurrentPoint = {
  type: "stmt";
  block: number;
  stmt: number;
} | {
  type: "terminator";
  block1: number;
  block2: number;
};

export type BasicBlockData = {
  block: number;
  stmts: string[];
  terminator: string;
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

export type MaybeOldPlace = {
  place: string;
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
  conditions: any
};

export type PlaceExpand = {
  base: MaybeOldPlace,
  expansion: string[]
}

export type ReborrowBridge = {
  expands: Conditioned<PlaceExpand>[];
  added_reborrows: Conditioned<Reborrow>[];
  ug: {
    dot_graph: string,
    empty: boolean
  }
};

export type PathData = {
  heap: Record<string, { value: string; ty: string; old: boolean }>;
  pcs: string;
  borrow_actions_start: BorrowAction[];
  borrow_actions_mid: BorrowAction[];
  reborrow_start: ReborrowBridge;
  reborrow_middle?: ReborrowBridge;
  borrows: {
    borrows: Borrow[];
  };
  repacks_middle: string[];
  repacks_start: string[];
};
