#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SpanFormatterErr {
    InputLengthExceeded,
}

impl std::fmt::Display for SpanFormatterErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpanFormatterErr::InputLengthExceeded => {
                write!(f, "requested span overruns the input length")
            }
        }
    }
}

pub trait SpanFormatter<'a, A, B> {
    fn format_from_span(&self, span: crate::Span, input: A) -> Result<B, SpanFormatterErr>;
}

pub mod character;
