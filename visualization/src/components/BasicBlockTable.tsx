import React from "react";
import { BasicBlockData, CurrentPoint } from "../types";
import ReactDOMServer from "react-dom/server";
import { MirStmt } from "../api";

interface BasicBlockTableProps {
  data: BasicBlockData;
  currentPoint: CurrentPoint;
  setCurrentPoint: (point: CurrentPoint) => void;
  isOnSelectedPath: boolean;
}

export function isStorageStmt(stmt: string) {
  return stmt.startsWith("StorageLive") || stmt.startsWith("StorageDead");
}

type TableRowProps = {
  index: number | "T"; // Either the index of the statement or "T" for the terminator
  stmt: MirStmt;
  selected: boolean;
  onClick: () => void;
};

function TableRow({ selected, onClick, stmt, index }: TableRowProps) {
  const tooltip = `Loans invalidated at start: ${stmt.loans_invalidated_start.join(", ")}\nLoans invalidated at mid: ${stmt.loans_invalidated_mid.join(", ")}\nBorrows in scope at start: ${stmt.borrows_in_scope_start.join(", ")}\nBorrows in scope at mid: ${stmt.borrows_in_scope_mid.join(", ")}`;
  return (
    <tr
      className={selected ? "highlight" : ""}
      onClick={onClick}
      title={tooltip}
    >
      <td>{index}</td>
      <td>
        <code>{stmt.stmt}</code>
      </td>
    </tr>
  );
}

export default function BasicBlockTable({
  data,
  currentPoint,
  setCurrentPoint,
  isOnSelectedPath,
}: BasicBlockTableProps) {
  return (
    <table
      cellSpacing={0}
      cellPadding={4}
      style={{
        borderCollapse: "collapse",
        width: "300px",
        border: isOnSelectedPath ? "5px solid red" : "1px solid black",
      }}
    >
      <tbody>
        <tr>
          <td>(on start)</td>
          <td>
            <b>bb{data.block}</b>
          </td>
        </tr>
        {data.stmts.map((stmt, i) => {
          return (
            <TableRow
              key={i}
              index={i}
              stmt={stmt}
              selected={
                currentPoint.type === "stmt" &&
                i === currentPoint.stmt &&
                data.block === currentPoint.block
              }
              onClick={() =>
                setCurrentPoint({
                  type: "stmt",
                  block: data.block,
                  stmt: i,
                  selectedAction: null,
                })
              }
            />
          );
        })}
        <TableRow
          index="T"
          stmt={data.terminator}
          selected={
            currentPoint.type === "stmt" &&
            currentPoint.stmt == data.stmts.length &&
            data.block === currentPoint.block
          }
          onClick={() =>
            setCurrentPoint({
              type: "stmt",
              block: data.block,
              stmt: data.stmts.length,
              selectedAction: null,
            })
          }
        />
      </tbody>
    </table>
  );
}

export function computeTableHeight(data: BasicBlockData): number {
  const container = document.createElement("div");
  container.innerHTML = ReactDOMServer.renderToString(
    BasicBlockTable({
      isOnSelectedPath: false,
      currentPoint: { type: "stmt", block: 0, stmt: 0, selectedAction: null },
      data: {
        block: data.block,
        stmts: data.stmts,
        terminator: data.terminator,
      },
      setCurrentPoint: () => {},
    })
  );
  document.body.appendChild(container);
  const height = container.offsetHeight;
  container.remove();
  return height;
}
