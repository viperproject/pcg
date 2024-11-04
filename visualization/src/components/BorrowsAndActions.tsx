import React from "react";
import {
  PathData,
  Borrow,
  BorrowAction,
  Reborrow,
  ReborrowAction,
  MaybeOldPlace,
  ReborrowBridge,
  PlaceExpand,
} from "../types";
import * as Viz from "@viz-js/viz";

function MaybeOldPlaceDisplay({
  maybeOldPlace,
}: {
  maybeOldPlace: MaybeOldPlace;
}) {
  return (
    <div>
      {maybeOldPlace.place} {maybeOldPlace.at ? `at ${maybeOldPlace.at}` : ""}
    </div>
  );
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
          {expand.base.place} -&gt; {expand.expansion.join(", ")}
        </div>
      ))}
    </div>
  );
}

function BorrowDisplay({ borrow }: { borrow: Borrow }) {
  return (
    <div>
      <p>Assigned: {borrow?.assigned_place?.place}</p>
      <p>Borrowed: {borrow?.borrowed_place?.place}</p>
      <p>Is Mutable: {borrow?.is_mut ? "Yes" : "No"}</p>
      <p>Kind: {borrow?.kind}</p>
    </div>
  );
}

function ReborrowBridgeDisplay({ bridge }: { bridge: ReborrowBridge }) {
  return (
    <div>
      {bridge.expands.length > 0 && (
        <div>
          Expands
          <BridgeExpands expands={bridge.expands.map((e) => e.value)} />
        </div>
      )}
      {bridge.added_borrows.length > 0 && (
        <div>
          Borrows
          <ul>
            {bridge.added_borrows.map((reborrow, index) => (
              <li key={`reborrow-${index}`}>
                <ReborrowDisplay reborrow={reborrow.value} />
              </li>
            ))}
          </ul>
        </div>
      )}
      {!bridge.ug.empty && (
        <a
          href="#"
          onClick={(event) => {
            event.preventDefault();
            Viz.instance().then((viz) => {
              const svgElement = viz.renderSVGElement(bridge.ug.dot_graph);
              const popup = window.open(
                "",
                "Dot Graph",
                "width=800,height=600"
              );
              popup.document.body.appendChild(svgElement);
            });
          }}
        >
          View Dot Graph
        </a>
      )}
    </div>
  );
}

function BorrowActionDisplay({ action }: { action: BorrowAction }) {
  return (
    <div>
      <p>Action: {action.action}</p>
      <BorrowDisplay borrow={action.borrow} />
    </div>
  );
}

export default function PCSActions({ pathData }: { pathData: PathData }) {
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
      <h4>Reborrow Bridge (Start)</h4>
      <ReborrowBridgeDisplay bridge={pathData.reborrow_start} />
      {pathData.reborrow_middle && (
        <>
          <h4>Reborrow Bridge (Mid)</h4>
          <ReborrowBridgeDisplay bridge={pathData.reborrow_middle} />
        </>
      )}
      <h4>Repacks (Start)</h4>
      <ul>
        {pathData.repacks_start.map((repack, index) => (
          <li key={`start-${index}`}>{repack}</li>
        ))}
      </ul>
      <h4>Repacks (Middle)</h4>
      <ul>
        {pathData.repacks_middle.map((repack, index) => (
          <li key={`mid-${index}`}>{repack}</li>
        ))}
      </ul>
    </div>
  );
}
