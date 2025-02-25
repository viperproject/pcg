use std::collections::BTreeSet;
use std::fmt::Display;
use std::io::Write;
use std::process::{Command, Stdio};

type NodeId = String;

pub struct DotGraph {
    pub name: String,
    pub nodes: Vec<DotNode>,
    pub edges: Vec<DotEdge>,
    pub subgraphs: Vec<DotSubgraph>,
}

impl DotGraph {
    pub fn write_to_file(&self, path: &str) -> std::io::Result<()> {
        std::fs::write(path, self.to_string())
    }

    pub fn render_with_imgcat(dot_str: &str, comment: &str) -> Result<(), std::io::Error> {
        tracing::info!("{}", comment);
        let mut dot_process = Command::new("dot")
            .args(&["-Tpng"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;

        let dot_stdin = dot_process
            .stdin
            .as_mut()
            .expect("Failed to open dot stdin");
        dot_stdin.write_all(dot_str.as_bytes())?;

        let dot_output = dot_process.wait_with_output()?;

        if !dot_output.status.success() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "dot command failed",
            ));
        }

        let mut imgcat_process = Command::new("imgcat")
            .stdin(Stdio::piped())
            .stdout(Stdio::inherit())
            .spawn()?;

        let imgcat_stdin = imgcat_process
            .stdin
            .as_mut()
            .expect("Failed to open imgcat stdin");
        imgcat_stdin.write_all(&dot_output.stdout)?;

        let imgcat_status = imgcat_process.wait()?;

        if !imgcat_status.success() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "imgcat command failed",
            ));
        }

        Ok(())
    }
}

pub struct DotSubgraph {
    pub id: String,
    pub label: String,
    pub nodes: Vec<DotNode>,
    pub rank_annotations: Vec<RankAnnotation>,
}

pub struct RankAnnotation {
    pub rank_type: String,
    pub nodes: BTreeSet<NodeId>,
}

impl Display for RankAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{ rank = {}; {}; }}",
            self.rank_type,
            self.nodes
                .iter()
                .map(|n| format!("{}", n))
                .collect::<Vec<_>>()
                .join("; ")
        )
    }
}

impl Display for DotSubgraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "subgraph {} {{", self.id)?;
        writeln!(f, "label=\"{}\";", self.label)?;
        for node in &self.nodes {
            writeln!(f, "{}", node)?;
        }
        for rank_annotation in &self.rank_annotations {
            writeln!(f, "{}", rank_annotation)?;
        }
        writeln!(f, "}}")
    }
}

impl Display for DotGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "digraph {} {{", self.name)?;
        writeln!(f, "node [shape=rect]")?;
        for node in &self.nodes {
            writeln!(f, "{}", node)?;
        }
        for edge in &self.edges {
            writeln!(f, "{}", edge)?;
        }
        for subgraph in &self.subgraphs {
            writeln!(f, "{}", subgraph)?;
        }
        writeln!(f, "}}")
    }
}

pub enum DotLabel {
    Text(String),
    Html(String),
}

impl Display for DotLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DotLabel::Text(text) => write!(f, "\"{}\"", text),
            DotLabel::Html(html) => write!(f, "<{}>", html),
        }
    }
}

impl DotAttr for DotLabel {}

pub struct DotNode {
    pub id: NodeId,
    pub label: DotLabel,
    pub font_color: DotStringAttr,
    pub color: DotStringAttr,
    pub shape: DotStringAttr,
    pub style: Option<DotStringAttr>,
    pub penwidth: Option<DotFloatAttr>,
    pub tooltip: Option<DotStringAttr>,
}

trait DotAttr: Display {}

pub struct DotStringAttr(pub String);

impl Display for DotStringAttr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
}

impl DotAttr for DotStringAttr {}

pub struct DotFloatAttr(pub f64);

impl Display for DotFloatAttr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl DotAttr for DotFloatAttr {}

fn format_attr<T: DotAttr>(name: &'static str, value: &T) -> String {
    format!("{}={}", name, value)
}

fn format_optional<T: DotAttr>(name: &'static str, value: &Option<T>) -> String {
    match value {
        Some(value) => format!("{}={}", name, value),
        None => "".to_string(),
    }
}

impl Display for DotNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let attrs = [
            format_attr("label", &self.label),
            format_attr("fontcolor", &self.font_color),
            format_attr("color", &self.color),
            format_attr("shape", &self.shape),
            format_optional("style", &self.style),
            format_optional("penwidth", &self.penwidth),
            format_optional("tooltip", &self.tooltip),
        ]
        .into_iter()
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>();
        write!(f, "\"{}\" [{}]", self.id, attrs.join(", "))
    }
}

#[derive(Eq, PartialEq, PartialOrd, Ord)]
pub enum EdgeDirection {
    Forward,
    Backward,
}

#[derive(Eq, PartialEq, PartialOrd, Ord)]
pub struct EdgeOptions {
    label: String,
    color: Option<String>,
    style: Option<String>,
    direction: Option<EdgeDirection>,
    tooltip: Option<String>,
}

impl EdgeOptions {
    pub fn directed(direction: EdgeDirection) -> Self {
        Self {
            label: "".to_string(),
            color: None,
            style: None,
            direction: Some(direction),
            tooltip: None,
        }
    }

    pub fn undirected() -> Self {
        Self {
            label: "".to_string(),
            color: None,
            style: None,
            direction: None,
            tooltip: None,
        }
    }

    pub fn with_label(mut self, label: String) -> Self {
        self.label = label;
        self
    }

    pub fn with_color(mut self, color: String) -> Self {
        self.color = Some(color);
        self
    }

    pub fn with_style(mut self, style: String) -> Self {
        self.style = Some(style);
        self
    }

    pub fn with_tooltip(mut self, tooltip: String) -> Self {
        self.tooltip = Some(tooltip);
        self
    }
}

#[derive(Eq, PartialEq, PartialOrd, Ord)]
pub struct DotEdge {
    pub from: NodeId,
    pub to: NodeId,
    pub options: EdgeOptions,
}

impl Display for DotEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let style_part = match &self.options.style {
            Some(style) => format!(", style=\"{}\"", style),
            None => "".to_string(),
        };
        let direction_part = match &self.options.direction {
            Some(EdgeDirection::Backward) => ", dir=\"back\"",
            Some(EdgeDirection::Forward) => "",
            None => ", arrowhead=\"none\"",
        };
        let color_part = match &self.options.color {
            Some(color) => format!(", color=\"{}\"", color),
            None => "".to_string(),
        };
        let tooltip_part = match &self.options.tooltip {
            Some(tooltip) => format!(", edgetooltip=\"{}\"", tooltip),
            None => "".to_string(),
        };
        write!(
            f,
            "    \"{}\" -> \"{}\" [label=\"{}\"{}{}{}{}]",
            self.from,
            self.to,
            self.options.label,
            style_part,
            direction_part,
            color_part,
            tooltip_part
        )
    }
}
