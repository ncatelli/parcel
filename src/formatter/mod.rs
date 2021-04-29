/// SpanFormatterErr represents any errors that can happen while formatting
/// output from a span.
#[derive(Debug, Clone, PartialEq)]
pub enum SpanFormatterErr {
    InputLengthExceeded(crate::Span),
}

impl std::fmt::Display for SpanFormatterErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpanFormatterErr::InputLengthExceeded(span) => {
                write!(
                    f,
                    "requested span(start: {}, end: {}) overruns the input length",
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
