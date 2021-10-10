/// SpanFormatterErr represents any errors that can happen while formatting
/// output from a span.
#[derive(Debug, Clone, PartialEq)]
pub enum SpanFormatterErr {
    /// OutOfBounds represents a case where a span extends over the bounds of an
    /// input.
    OutOfBounds(crate::Span),
}

impl core::fmt::Display for SpanFormatterErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SpanFormatterErr::OutOfBounds(span) => {
                write!(
                    f,
                    "span(start: {}, end: {}) overruns the input bounds",
                    span.start, span.end
                )
            }
        }
    }
}

/// SpanFormatter functions as a base trait for defining how span data can be
/// formatted into a corresponding output format. This can be useful for
/// things such as formatting text into cursor positions.
pub trait SpanFormatter<A, B> {
    /// format_from_span defines a method for generating any formatted
    /// representation of a span for a given input.
    fn format_from_span(&self, span: crate::Span, input: A) -> Result<B, SpanFormatterErr>;
}

// Character formatters
pub mod character;
