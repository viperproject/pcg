let currentRow;
let selectedFunction = "";

async function fetchJsonFile(filePath) {
  const response = await fetch(filePath);
  return await response.json();
}

async function fetchDotFile(filePath) {
  const response = await fetch(filePath);
  return await response.text();
}

async function populateFunctionDropdown() {
  const functions = await fetchJsonFile("data/functions.json");
  const select = document.getElementById("function-select");
  functions.forEach((func) => {
    const option = document.createElement("option");
    option.value = func;
    option.textContent = func;
    select.appendChild(option);
  });

  select.addEventListener("change", (event) => {
    selectedFunction = event.target.value;
    renderGraph();
  });

  // Set the initial selected function and render the graph
  if (functions.length > 0) {
    selectedFunction = functions[0];
    renderGraph();
  }
}

async function renderGraph() {
  if (!selectedFunction) return;

  const graphFilePath = `data/${selectedFunction}/mir.json`;
  const graph = await fetchJsonFile(graphFilePath);

  const g = new dagre.graphlib.Graph()
    .setGraph({})
    .setDefaultEdgeLabel(() => ({}));

  graph.nodes.forEach((node) => {
    g.setNode(node.id, { label: node.label });
  });

  graph.edges.forEach((edge) => {
    g.setEdge(edge.source, edge.target, { label: edge.label });
  });

  dagre.layout(g);

  document.getElementById("graph").innerHTML = "";
  const svg = d3.select("#graph").append("svg");

  const node = svg
    .append("g")
    .selectAll("g")
    .data(g.nodes())
    .enter()
    .append("g")
    .attr("class", "node")
    .attr("transform", (d) => {
      const node = g.node(d);
      return `translate(${node.x - node.width / 2},${node.y - node.height / 2})`;
    });

  node
    .append("foreignObject")
    .attr("width", 200)
    .attr("height", 600)
    .attr("class", "foreign-object")
    .html((d) => g.node(d).label);

  // Compute the actual height and width of each HTML table and update the corresponding node in dagre
  document.querySelectorAll("table[data-bb]").forEach((table) => {
    const bb = table.getAttribute("data-bb");
    const rect = table.getBoundingClientRect();
    const width = rect.width;
    const height = rect.height;

    // Update the node in dagre
    const node = g.node(bb);
    node.width = width;
    node.height = height;
  });

  // Recompute the layout with updated node dimensions
  dagre.layout(g);

  // Calculate width and height of the complete graph
  const graphWidth =
    Math.max(...g.nodes().map((d) => g.node(d).x + g.node(d).width / 2)) +
    20;
  const graphHeight =
    Math.max(
      ...g.nodes().map((d) => g.node(d).y + g.node(d).height / 2)
    ) + 20;

  // Update SVG dimensions based on calculated values
  svg.attr("width", graphWidth).attr("height", graphHeight);

  // Transform the nodes to their new positions
  node.attr("transform", (d) => {
    const node = g.node(d);
    return `translate(${node.x - node.width / 2},${node.y - node.height / 2})`;
  });

  // Draw edges
  const link = svg
    .append("g")
    .selectAll("path")
    .data(g.edges())
    .enter()
    .append("path")
    .attr("class", "link")
    .attr("id", (d, i) => `link${i}`)
    .attr("d", (d) => {
      const source = g.node(d.v);
      const target = g.node(d.w);
      const sourceX = source.x;
      const sourceY = source.y + source.height / 2;
      const targetX = target.x;
      const targetY = target.y - target.height / 2;
      return `M${sourceX},${sourceY}L${targetX},${targetY}`;
    });

  const edgeLabels = svg
    .append("g")
    .selectAll(".edge-label")
    .data(g.edges())
    .enter()
    .append("text")
    .attr("class", "link-label")
    .attr("dy", -5)
    .append("textPath")
    .attr("xlink:href", (d, i) => `#link${i}`)
    .attr("startOffset", "50%")
    .text((d) => g.edge(d).label);

  svg.on("click", async function (event) {
    const row = event.target.closest("tr");
    if (row) {
      highlightRow(row);
    }
  });

  // Initial highlight of the first row
  const initialRow = document.querySelector(
    "tr[data-bb='0'][data-statement='0']"
  );
  if (initialRow) {
    highlightRow(initialRow);
  }

  document.addEventListener("keydown", function (event) {
    if (
      event.key === "ArrowUp" ||
      event.key === "ArrowDown" ||
      event.key === "k" ||
      event.key === "j"
    ) {
      event.preventDefault();
      if (currentRow) {
        if (
          (event.key === "ArrowUp" || event.key === "k") &&
          currentRow.previousElementSibling
        ) {
          highlightRow(currentRow.previousElementSibling);
        } else if (
          (event.key === "ArrowDown" || event.key === "j") &&
          currentRow.nextElementSibling
        ) {
          highlightRow(currentRow.nextElementSibling);
        }
      }
    }
  });
}

// Highlights a row and renders the corresponding DOT graph
async function highlightRow(row) {
  const statement = row.getAttribute("data-statement");
  const bb = row.getAttribute("data-bb");
  console.log("Statement:", statement, "BB:", bb);

  d3.selectAll(".highlight").classed("highlight", false);

  d3.select(row).classed("highlight", true);
  currentRow = row;

  const dotFilePath = `data/${selectedFunction}/block_${bb}_stmt_${statement}.dot`;

  try {
    const dotData = await fetchDotFile(dotFilePath);
    Viz.instance().then(function (viz) {
      document.getElementById("dot-graph").innerHTML = "";
      document
        .getElementById("dot-graph")
        .appendChild(viz.renderSVGElement(dotData));
    });
  } catch (error) {
    console.error("Error fetching or rendering DOT file:", error);
  }
}

window.onload = populateFunctionDropdown;
