import React from "react";
import * as Viz from "@viz-js/viz";
import { fetchDotFile } from "../dot_graph";

interface LegendButtonProps {
  selectedFunction: string;
}

const LegendButton: React.FC<LegendButtonProps> = ({ selectedFunction }) => {
  const openLegendWindow = async () => {
    try {
      const edgeLegendPath = `data/${selectedFunction}/edge_legend.dot`;
      const nodeLegendPath = `data/${selectedFunction}/node_legend.dot`;
      const [edgeLegendData, nodeLegendData] = await Promise.all([
        fetchDotFile(edgeLegendPath),
        fetchDotFile(nodeLegendPath),
      ]);

      Viz.instance().then((viz) => {
        const edgeSvgElement = viz.renderSVGElement(edgeLegendData);
        const nodeSvgElement = viz.renderSVGElement(nodeLegendData);

        const popup = window.open(
          "",
          "Graph Legend",
          "width=800,height=1000"
        );
        popup.document.head.innerHTML = `
          <style>
            body {
              margin: 0;
              display: flex;
              flex-direction: column;
              align-items: center;
              min-height: 100vh;
              background: white;
              padding: 20px;
            }
            .legend-container {
              display: flex;
              flex-direction: column;
              gap: 20px;
              max-width: 100%;
            }
            svg {
              max-width: 100%;
              height: auto;
            }
          </style>
        `;
        popup.document.title = "Graph Legend";

        const container = popup.document.createElement("div");
        container.className = "legend-container";
        container.appendChild(edgeSvgElement);
        container.appendChild(nodeSvgElement);
        popup.document.body.appendChild(container);
      });
    } catch (error) {
      console.warn("Failed to load legend:", error);
    }
  };

  return (
    <button
      onClick={openLegendWindow}
      className="control-button"
      style={{ marginLeft: "10px" }}
    >
      Show Legend
    </button>
  );
};

export default LegendButton;
