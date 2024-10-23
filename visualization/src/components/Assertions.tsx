import React from "react";
import Table from "./Table";

export type Assertion = {
  assertion: string;
};
export default function Assertions({
  assertions,
}: {
  assertions: Assertion[];
}) {
  return (
    <Table
      columns={["Assertions"]}
      data={assertions.map((assertion) => [assertion.assertion])}
    />
  );
}
