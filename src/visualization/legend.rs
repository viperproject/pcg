use super::dot_graph::{DotEdge, DotNode, EdgeDirection, EdgeOptions, DotLabel, DotStringAttr};
use std::io::{self, Write};

pub fn generate_legend() -> io::Result<String> {
    let mut buf = vec![];
    write_legend(&mut buf)?;
    Ok(String::from_utf8(buf).unwrap())
}

fn write_legend<T: Write>(out: &mut T) -> io::Result<()> {
    writeln!(out, "digraph legend {{")?;
    writeln!(out, "  node [shape=rect];")?;
    writeln!(out, "  rankdir=LR;")?;
    writeln!(out, "  label=\"Edge Types Legend\";")?;
    writeln!(out, "  labelloc=\"t\";")?;

    // Projection Edge
    write_edge(out, "proj_a", "proj_b", "Projection Edge",
        EdgeOptions::undirected())?;

    // Reborrow Edge
    write_edge(out, "reborrow_a", "reborrow_b", "Reborrow Edge",
        EdgeOptions::directed(EdgeDirection::Forward)
            .with_color("orange".to_string())
            .with_label("region - conditions".to_string()))?;

    // Deref Expansion Edge
    write_edge(out, "deref_a", "deref_b", "Deref Expansion Edge",
        EdgeOptions::undirected()
            .with_color("green".to_string())
            .with_label("path conditions".to_string()))?;

    // Abstract Edge
    write_edge(out, "abstract_a", "abstract_b", "Abstract Edge",
        EdgeOptions::directed(EdgeDirection::Forward))?;

    // Region Projection Member Edge
    write_edge(out, "region_a", "region_b", "Region Projection Edge",
        EdgeOptions::directed(EdgeDirection::Forward)
            .with_color("purple".to_string()))?;

    // Coupled Edge
    write_edge(out, "coupled_a", "coupled_b", "Coupled Edge",
        EdgeOptions::undirected()
            .with_color("red".to_string())
            .with_style("dashed".to_string()))?;

    writeln!(out, "}}")
}

fn write_edge<T: Write>(
    out: &mut T,
    from: &str,
    to: &str,
    label: &str,
    options: EdgeOptions,
) -> io::Result<()> {
    let node_a = DotNode {
        id: from.to_string(),
        label: DotLabel::Text("A".to_string()),
        color: DotStringAttr("black".to_string()),
        font_color: DotStringAttr("black".to_string()),
        shape: DotStringAttr("rect".to_string()),
        style: None,
        penwidth: None,
    };

    let node_b = DotNode {
        id: to.to_string(),
        label: DotLabel::Text("B".to_string()),
        color: DotStringAttr("black".to_string()),
        font_color: DotStringAttr("black".to_string()),
        shape: DotStringAttr("rect".to_string()),
        style: None,
        penwidth: None,
    };

    let edge = DotEdge {
        from: from.to_string(),
        to: to.to_string(),
        options,
    };

    writeln!(out, "  subgraph cluster_{} {{", from)?;
    writeln!(out, "    label=\"{}\"", label)?;
    writeln!(out, "    {}", node_a)?;
    writeln!(out, "    {}", node_b)?;
    writeln!(out, "    {}", edge)?;
    writeln!(out, "  }}")?;
    Ok(())
}
