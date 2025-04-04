import * as Viz from "@viz-js/viz";
export async function fetchDotFile(filePath: string) {
    const response = await fetch(filePath);
    return await response.text();
}

export async function openDotGraphInNewWindow(filename: string) {
    const dotData = await fetchDotFile(filename);
    Viz.instance().then((viz) => {
      const svgElement = viz.renderSVGElement(dotData);
      const popup = window.open(
        "",
        `Dot Graph - ${filename}`,
        "width=800,height=600"
      );
      popup.document.head.innerHTML = `
        <style>
          body { margin: 0; }
          svg {
            width: 100vw;
            height: 100vh;
            display: block;
          }
        </style>
      `;
      popup.document.body.appendChild(svgElement);
    });
}
