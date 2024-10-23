import React from "react";
import Table from "./Table";
export default function PathConditions({ pcs }: { pcs: string }) {
  return <Table columns={["Path Conditions"]} data={[[pcs]]} />;
}
