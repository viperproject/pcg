import React from "react";
import {
  PathData,
  Borrow,
  BorrowAction,
  Reborrow,
  MaybeOldPlace,
  BorrowPCGActions,
  PlaceExpand,
  PCGNode,
  MaybeRemotePlace,
  LocalNode,
  PCGStmtVisualizationData,
  PcgProgramPointData,
} from "../types";
import * as Viz from "@viz-js/viz";

function MaybeOldPlaceDisplay({
  maybeOldPlace,
}: {
  maybeOldPlace: MaybeOldPlace;
}) {
  if (typeof maybeOldPlace === "string") {
    return <span>{maybeOldPlace}</span>;
  }
  return (
    <span style={{ fontFamily: "monospace" }}>
      {maybeOldPlace.place} {maybeOldPlace.at ? `at ${maybeOldPlace.at}` : ""}
    </span>
  );
}

function MaybeRemotePlaceDisplay({
  maybeRemotePlace,
}: {
  maybeRemotePlace: MaybeRemotePlace;
}) {
  if (typeof maybeRemotePlace === "string") {
    return <span>{maybeRemotePlace}</span>;
  }
  return <MaybeOldPlaceDisplay maybeOldPlace={maybeRemotePlace} />;
}

function ReborrowDisplay({ reborrow }: { reborrow: Reborrow }) {
  return (
    <div>
      <p>
        Assigned Place:{" "}
        <MaybeOldPlaceDisplay maybeOldPlace={reborrow?.assigned_place} />
      </p>
      <p>
        Blocked Place:{" "}
        <MaybeOldPlaceDisplay maybeOldPlace={reborrow?.blocked_place} />
      </p>
      <p>Mutable: {reborrow?.is_mut ? "Yes" : "No"}</p>
    </div>
  );
}

function BridgeExpands({ expands }: { expands: PlaceExpand[] }) {
  return (
    <div>
      {expands.map((expand, idx) => (
        <div key={`expand-${idx}`}>
          <PCGNodeDisplay node={expand.base} />→
          <span>
            {expand.expansion.map((e, idx2) => (
              <PCGNodeDisplay key={`expand-${idx}-${idx2}`} node={e} />
            ))}
          </span>
        </div>
      ))}
    </div>
  );
}

function BorrowDisplay({ borrow }: { borrow: Borrow }) {
  return (
    <div>
      <p>
        Assigned:{" "}
        <MaybeOldPlaceDisplay maybeOldPlace={borrow?.assigned_place} />
      </p>
      <p>
        Borrowed:{" "}
        <MaybeOldPlaceDisplay maybeOldPlace={borrow?.borrowed_place} />
      </p>
      <p>Is Mutable: {borrow?.is_mut ? "Yes" : "No"}</p>
      <p>Kind: {borrow?.kind}</p>
    </div>
  );
}

function PCGNodeDisplay({ node }: { node: PCGNode<MaybeRemotePlace> }) {
  if (typeof node === "string") {
    return <span>{node}</span>;
  } else if ("region" in node) {
    return (
      <span>
        <MaybeRemotePlaceDisplay maybeRemotePlace={node.place} />↓{node.region}
      </span>
    );
  }
  return <span>{JSON.stringify(node)}</span>;
}

function BorrowsBridgeDisplay({ actions }: { actions: BorrowPCGActions }) {
  return (
    <ul>
      {actions.map((action, index) => (
        <li key={`action-${index}`}>{action}</li>
      ))}
    </ul>
  );
}

export default function PCGOps({ data }: { data: PcgProgramPointData }) {
  let content;
  if ("free_pcg_repacks_start" in data) {
    content = (
      <>
        {[
          "pre_operands" as const,
          "post_operands" as const,
          "pre_main" as const,
          "post_main" as const,
        ].map((key) => (
          <div key={key}>
            <h5>{key}</h5>
            <BorrowsBridgeDisplay actions={data.borrow_actions[key]} />
          </div>
        ))}
        <h4>Repacks (Start)</h4>
        <ul>
          {data.free_pcg_repacks_start.map((repack, index) => (
            <li key={`start-${index}`}>{repack}</li>
          ))}
        </ul>
        <h4>Repacks (Middle)</h4>
        <ul>
          {data.free_pcg_repacks_middle.map((repack, index) => (
            <li key={`mid-${index}`}>{repack}</li>
          ))}
        </ul>
      </>
    );
  } else {
    content = (
      <>
        <h4>Owned Ops</h4>
        <ul>
          {data.owned_ops.map((op, index) => <li key={`owned-${index}`}>{op}</li>)}
        </ul>
        <h4>Borrow Ops</h4>
        <ul>
          {data.borrow_ops.map((op, index) => (
            <li key={`borrow-${index}`}>{op}</li>
          ))}
        </ul>
      </>
    );
  }
  return (
    <div
      style={{
        position: "fixed",
        bottom: "20px",
        right: "20px",
        backgroundColor: "white",
        boxShadow: "0 0 10px rgba(0,0,0,0.1)",
        padding: "10px",
        maxWidth: "300px",
        overflowY: "auto",
        maxHeight: "80vh",
      }}
    >
      {content}
    </div>
  );
}
