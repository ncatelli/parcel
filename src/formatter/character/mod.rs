use crate::formatter::{SpanFormatter, SpanFormatterErr};

/// TextFormatter implements the span formatter for text inputs. This walks the
/// span assigning a line number and column number offset into the file based on
/// the returned span result.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::formatter::SpanFormatter;
/// use parcel::formatter::character::TextFormatter;
/// use parcel::Span;
/// let input: Vec<char> = "abcdef\nghijk\nlmnopqrstuvwxyz".chars().collect();
/// let ms = parcel::MatchStatus::Match{span: 15..16, remainder: &input[16..], inner: 'n'};
/// let span = ms.as_span().unwrap();
/// let text_formatter = TextFormatter::new('\n');
/// assert_eq!(
///   Ok((2, 2)..(2, 3)),
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
///   Err(SpanFormatterErr::InputLengthExceeded(100..101)),
///   text_formatter.format_from_span(span, &input)
/// );
/// ```
#[derive(Debug, Clone, Copy)]
pub struct TextFormatter {
    newline_delimiter: char,
}

impl TextFormatter {
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

impl<'a> SpanFormatter<&'a [char], std::ops::Range<(usize, usize)>> for TextFormatter {
    fn format_from_span(
        &self,
        span: crate::Span,
        input: &'a [char],
    ) -> Result<std::ops::Range<(usize, usize)>, SpanFormatterErr> {
        if input.len() < span.end {
            Err(SpanFormatterErr::OutOfBounds(span))
        } else {
            let start = (&input[0..span.start])
                .iter()
                .fold((0, 0), |(line, column), &c| {
                    if c == self.newline_delimiter {
                        (line + 1, 0)
                    } else {
                        (line, column + 1)
                    }
                });
            let end = (&input[span.start..span.end]).iter().fold(
                (start.0, start.1),
                |(line, column), &c| {
                    if c == self.newline_delimiter {
                        (line + 1, 0)
                    } else {
                        (line, column + 1)
                    }
                },
            );

            Ok(start..end)
        }
    }
}
