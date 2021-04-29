use crate::formatter::{SpanFormatter, SpanFormatterErr};

/// Cursor represents a position within a text source.
#[derive(Default, Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Cursor {
    /// The line number position (0-indexed).
    pub line: usize,
    /// The column number position (0-indexed) on a given line.
    pub column: usize,
}

impl Cursor {
    /// new instantiates a cursor with a give line and column.
    pub fn new(line: usize, column: usize) -> Self {
        Self { line, column }
    }
}

impl std::fmt::Display for Cursor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line:: {}, column: {}", self.line, self.column)
    }
}

impl From<Cursor> for (usize, usize) {
    fn from(src: Cursor) -> Self {
        (src.line, src.column)
    }
}

impl From<(usize, usize)> for Cursor {
    fn from(src: (usize, usize)) -> Self {
        Self::new(src.0, src.1)
    }
}

/// TextFormatter implements the span formatter for text inputs. This walks the
/// span assigning a line number and column number offset into the file based on
/// the returned span result.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::formatter::SpanFormatter;
/// use parcel::formatter::character::{TextFormatter, Cursor};
/// use parcel::Span;
/// let input: Vec<char> = "abcdef\nghijk\nlmnopqrstuvwxyz".chars().collect();
/// let ms = parcel::MatchStatus::Match{span: 15..16, remainder: &input[16..], inner: 'n'};
/// let span = ms.as_span().unwrap();
/// let text_formatter = TextFormatter::new('\n');
/// assert_eq!(
///   Ok(Cursor::new(2, 2)..Cursor::new(2, 3)),
///   text_formatter.format_from_span(span, &input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::formatter::{SpanFormatter, SpanFormatterErr};
/// use parcel::formatter::character::TextFormatter;
/// use parcel::Span;
/// let input: Vec<char> = "abcdef\nghijk\nlmnopqrstuvwxyz".chars().collect();
/// let ms = parcel::MatchStatus::Match{span: 100..101, remainder: &input[16..], inner: 'n'};
/// let span = ms.as_span().unwrap();
/// let text_formatter = TextFormatter::new('\n');
/// assert_eq!(
///   Err(SpanFormatterErr::OutOfBounds(100..101)),
///   text_formatter.format_from_span(span, &input)
/// );
/// ```
#[derive(Debug, Clone, Copy)]
pub struct TextFormatter {
    newline_delimiter: char,
}

impl TextFormatter {
    /// new takes a single newline_delimiting character and instantiates a
    /// text formatter.
    pub fn new(newline_delimiter: char) -> Self {
        Self { newline_delimiter }
    }
}

impl Default for TextFormatter {
    fn default() -> Self {
        Self {
            newline_delimiter: '\n',
        }
    }
}

impl<'a> SpanFormatter<&'a [char], std::ops::Range<Cursor>> for TextFormatter {
    fn format_from_span(
        &self,
        span: crate::Span,
        input: &'a [char],
    ) -> Result<std::ops::Range<Cursor>, SpanFormatterErr> {
        if input.len() < span.end {
            Err(SpanFormatterErr::OutOfBounds(span))
        } else {
            let start = (&input[0..span.start])
                .iter()
                .fold(Cursor::default(), |cursor, &c| {
                    increment_cursor_from_input_char(cursor, self.newline_delimiter, c)
                });
            let end = (&input[span.start..span.end])
                .iter()
                .fold(start, |cursor, &c| {
                    increment_cursor_from_input_char(cursor, self.newline_delimiter, c)
                });

            Ok(start..end)
        }
    }
}

fn increment_cursor_from_input_char(cursor: Cursor, newline_delimiter: char, c: char) -> Cursor {
    if c == newline_delimiter {
        Cursor::new(cursor.line + 1, 0)
    } else {
        Cursor::new(cursor.line, cursor.column + 1)
    }
}
