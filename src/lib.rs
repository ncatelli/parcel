//! This crate functions as a test/toy implementation of parser combinators in
//! rust, heavily inspired by the article by Bodil Stokke. While the goal of
//! this crate is to be functional for both text and binary grammars I'd highly
//! recommend against using it for anything other than experimentation.
//! Instead, recommending Geal/nom.

use std::sync::Arc;

#[cfg(test)]
mod tests;

/// MatchStatus represents a non-error parser result with two cases, signifying
/// where the parse returned a match or not.
#[derive(Debug, PartialEq, Clone)]
pub enum MatchStatus<U, T> {
    Match((U, T)),
    NoMatch(U),
}

/// Provides a map implementation to emulate the map functionality of Option or
/// Result.
impl<U, T> MatchStatus<U, T> {
    pub fn map<V, F>(self, op: Arc<F>) -> MatchStatus<U, V>
    where
        F: Fn(T) -> V,
    {
        match self {
            MatchStatus::Match((last_input, result)) => {
                MatchStatus::Match((last_input, op(result)))
            }
            MatchStatus::NoMatch(last_input) => MatchStatus::NoMatch(last_input),
        }
    }
}

/// Represents the state of parser execution, wrapping the above MatchStatus
/// and providing an Error string for any problems.
pub type ParseResult<'a, Input, Output> = Result<MatchStatus<Input, Output>, String>;

pub trait Parser<'a, Input, Output> {
    fn parse(&self, input: Input) -> ParseResult<'a, Input, Output>;
}

impl<'a, F, Input, Output> Parser<'a, Input, Output> for F
where
    Input: 'a,
    F: Fn(Input) -> ParseResult<'a, Input, Output>,
{
    fn parse(&self, input: Input) -> ParseResult<'a, Input, Output> {
        self(input)
    }
}

/// Map a Parser<A, B> to Parser<A, C>.
pub fn map<'a, P, F, A: 'a, B, C>(parser: P, map_fn: F) -> impl Parser<'a, A, C>
where
    P: Parser<'a, A, B>,
    F: Fn(B) -> C + 'a,
{
    // There has to be a better way to approach this other than using an Arc/Rc
    let op = Arc::new(map_fn);

    move |input| {
        parser
            .parse(input)
            .map(|match_status| match_status.map(op.clone()))
    }
}
