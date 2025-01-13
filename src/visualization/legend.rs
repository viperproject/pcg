use super::dot_graph::{DotEdge, DotNode, EdgeDirection, EdgeOptions, DotLabel, DotStringAttr};
use std::io::{self, Write};

pub fn generate_edge_legend() -> io::Result<String> {
    let mut buf = vec![];
    write_edge_legend(&mut buf)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub fn generate_node_legend() -> io::Result<String> {
    let mut buf = vec![];
    write_node_legend(&mut buf)?;
    Ok(String::from_utf8(buf).unwrap())
}

fn write_edge_legend<T: Write>(out: &mut T) -> io::Result<()> {
    writeln!(out, "digraph edge_legend {{")?;
    writeln!(out, "  node [shape=rect];")?;
    writeln!(out, "  rankdir=LR;")?;
    writeln!(out, "  label=\"Edge Types\";")?;
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

fn write_node_legend<T: Write>(out: &mut T) -> io::Result<()> {
    writeln!(out, "digraph node_legend {{")?;
    writeln!(out, "  node [shape=rect];")?;
    writeln!(out, "  rankdir=LR;")?;
    writeln!(out, "  label=\"Node Types\";")?;
    writeln!(out, "  labelloc=\"t\";")?;

    // FPCS Node
    writeln!(out, "  fpcs_node [")?;
    writeln!(out, "    shape=rect,")?;
    writeln!(out, "    label=<<FONT FACE=\"courier\">place</FONT>&nbsp;Write&nbsp;at loc>,")?;
    writeln!(out, "    color=gray,")?;
    writeln!(out, "    fontcolor=gray")?;
    writeln!(out, "  ];")?;

    // Region Projection Node
    writeln!(out, "  region_node [")?;
    writeln!(out, "    shape=octagon,")?;
    writeln!(out, "    label=\"region\",")?;
    writeln!(out, "    color=blue,")?;
    writeln!(out, "    fontcolor=blue")?;
    writeln!(out, "  ];")?;

    // Reborrowing DAG Node
    writeln!(out, "  reborrow_node [")?;
    writeln!(out, "    shape=rect,")?;
    writeln!(out, "    style=rounded,")?;
    writeln!(out, "    label=<<FONT FACE=\"courier\">place</FONT>&nbsp;at loc>,")?;
    writeln!(out, "    color=darkgreen,")?;
    writeln!(out, "    fontcolor=darkgreen,")?;
    writeln!(out, "    penwidth=1.5")?;
    writeln!(out, "  ];")?;

    // Arrange nodes horizontally
    writeln!(out, "  {{ rank=same; fpcs_node; region_node; reborrow_node; }}")?;

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
