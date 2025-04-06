import React, {  } from "react";
import { createRoot } from "react-dom/client";
import * as Viz from "@viz-js/viz";

import {
  getAssertions,
  getFunctions,
  getPaths,
} from "./api";
import { App } from "./components/App";

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

  const rootElement = document.getElementById("root");
  if (rootElement) {
    const root = createRoot(rootElement);
    root.render(
      <App
        initialFunction={initialFunction}
        initialPaths={initialPaths}
        initialAssertions={initialAssertions}
        functions={functions}
        initialPath={initialPath}
      />
    );
  }
}

main();
