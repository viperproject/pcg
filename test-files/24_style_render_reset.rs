pub(crate) const RESET: &str = "\x1B[0m";

#[derive(PartialEq, Eq)]
pub enum Color {
    /// Available 4-bit ANSI color palette codes
    ///
    /// The user's terminal defines the meaning of the each palette code.
    Ansi(u32),
    /// 256 (8-bit) color support
    ///
    /// - `0..16` are [`AnsiColor`] palette codes
    /// - `0..232` map to [`RgbColor`] color values
    /// - `232..` map to [`RgbColor`] gray-scale values
    Ansi256(u8),
    /// 24-bit ANSI RGB color codes
    Rgb(u32),
}

#[derive(PartialEq, Eq)]
pub struct Style {
    fg: Option<Color>,
    bg: Option<Color>,
    underline: Option<Color>,
    // effects: crate::Effects,
}

impl Style {
    pub fn new() -> Self {
        Self {
            fg: None,
            bg: None,
            underline: None,
        }
    }
    pub fn render_reset(self) -> impl core::fmt::Display + Copy {
        if self != Self::new() {
            RESET
        } else {
            ""
        }
    }
}


fn main() {
}
