//! This crate functions as a test/toy implementation of parser combinators in
//! rust, heavily inspired by the article by Bodil Stokke. While the goal of
//! this crate is to be functional for both text and binary grammars I'd highly
//! recommend against using it for anything other than experimentation.
//! Instead, recommending Geal/nom.

pub mod parsers;
pub mod prelude;

#[cfg(test)]
mod tests;

use std::borrow::Borrow;

/// MatchStatus represents a non-error parser result with two cases, signifying
/// where the parse returned a match or not.
#[derive(Debug, PartialEq, Clone)]
pub enum MatchStatus<U, T> {
    Match((U, T)),
    NoMatch(U),
}

impl<U, T> MatchStatus<U, T> {
    /// Returns the contained `Match` value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value equals `NoMatch`
    ///
    /// # Examples
    ///
    /// ```
    /// let input = vec!['a'];
    /// let v = parcel::MatchStatus::Match((&input[1..], 'a'));
    /// assert_eq!(v.unwrap(), 'a');
    /// ```
    ///
    /// ```{.should_panic}
    /// let input = vec!['a'];
    /// let v = parcel::MatchStatus::<&[char], char>::NoMatch(&input);
    /// assert_eq!(v.unwrap(), 'a');
    /// ```
    pub fn unwrap(self) -> T {
        match self {
            Self::Match((_, t)) => t,
            _ => panic!("unable "),
        }
    }

    /// Returns the contained `Match` value, consuming the `self` value.
    ///
    /// Arguments passed to `unwrap_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use [`unwrap_or_else`],
    /// which is lazily evaluated.
    ///
    /// # Examples
    ///
    /// ```
    /// let input = vec!['a'];
    /// let v = parcel::MatchStatus::NoMatch(&input);
    /// assert_eq!(v.unwrap_or('b'), 'b');
    /// ```
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Self::Match((_, t)) => t,
            _ => default,
        }
    }

    /// Returns the contained `Match` value or computes it from a closure.
    ///
    /// # Examples
    ///
    /// ```
    /// let input = vec!['a'];
    /// let v = parcel::MatchStatus::NoMatch(&input);
    /// assert_eq!(v.unwrap_or_else(|| 'b'), 'b');
    /// ```
    pub fn unwrap_or_else<F>(self, f: F) -> T
    where
        F: FnOnce() -> T,
    {
        match self {
            Self::Match((_, t)) => t,
            _ => f(),
        }
    }
}

/// Represents the state of parser execution, wrapping the above MatchStatus
/// and providing an Error string for any problems.
pub type ParseResult<'a, Input, Output> = Result<MatchStatus<Input, Output>, String>;

/// Parser is the primary trait serving as the basis for all child combinators.
/// The most important function defined in this trait is parse, which defines
/// the function that will be called for all child parsers. As a convenience,
/// Boxed Implementations of Parser functions are included as trait defaults,
/// allowing chained parser calls to be made for the sake of code cleanliness.
pub trait Parser<'a, Input, Output> {
    fn parse(&self, input: Input) -> ParseResult<'a, Input, Output>;

    fn or<P>(self, thunk: impl Fn() -> P + 'a) -> BoxedParser<'a, Input, Output>
    where
        Self: Sized + 'a,
        Input: Copy + 'a,
        Output: 'a,
        P: Parser<'a, Input, Output> + 'a,
    {
        BoxedParser::new(or(self, thunk))
    }

    fn and_then<F, NextParser, NewOutput>(self, thunk: F) -> BoxedParser<'a, Input, NewOutput>
    where
        Self: Sized + 'a,
        Input: 'a,
        Output: 'a,
        NewOutput: 'a,
        NextParser: Parser<'a, Input, NewOutput> + 'a,
        F: Fn(Output) -> NextParser + 'a,
    {
        BoxedParser::new(and_then(self, thunk))
    }

    fn take_until_n(self, n: usize) -> BoxedParser<'a, Input, Vec<Output>>
    where
        Self: Sized + 'a,
        Input: Copy + 'a,
        Output: 'a,
    {
        BoxedParser::new(take_until_n(self, n))
    }

    fn take_n(self, n: usize) -> BoxedParser<'a, Input, Vec<Output>>
    where
        Self: Sized + 'a,
        Input: Copy + 'a,
        Output: 'a,
    {
        BoxedParser::new(take_n(self, n))
    }

    fn predicate<F>(self, predicate_case: F) -> BoxedParser<'a, Input, Output>
    where
        Self: Sized + 'a,
        Input: Copy + 'a,
        Output: 'a,
        F: Fn(&Output) -> bool + 'a,
    {
        BoxedParser::new(predicate(self, predicate_case))
    }

    fn zero_or_more(self) -> BoxedParser<'a, Input, Vec<Output>>
    where
        Self: Sized + 'a,
        Input: Copy + 'a,
        Output: 'a,
    {
        BoxedParser::new(zero_or_more(self))
    }

    fn one_or_more(self) -> BoxedParser<'a, Input, Vec<Output>>
    where
        Self: Sized + 'a,
        Input: Copy + 'a,
        Output: 'a,
    {
        BoxedParser::new(one_or_more(self))
    }

    fn map<F, NewOutput>(self, map_fn: F) -> BoxedParser<'a, Input, NewOutput>
    where
        Self: Sized + 'a,
        Input: 'a,
        Output: 'a,
        NewOutput: 'a,
        F: Fn(Output) -> NewOutput + 'a,
    {
        BoxedParser::new(map(self, map_fn))
    }

    fn skip(self) -> BoxedParser<'a, Input, Output>
    where
        Self: Sized + 'a,
        Input: 'a,
        Output: 'a,
    {
        BoxedParser::new(skip(self))
    }

    fn optional(self) -> BoxedParser<'a, Input, Option<Output>>
    where
        Self: Sized + 'a,
        Input: Copy + 'a,
        Output: 'a,
    {
        BoxedParser::new(optional(self))
    }
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

// Provides a boxed wrapper to any parser trait implementation.
pub struct BoxedParser<'a, Input, Output> {
    parser: Box<dyn Parser<'a, Input, Output> + 'a>,
}

impl<'a, Input, Output> BoxedParser<'a, Input, Output> {
    fn new<P>(parser: P) -> Self
    where
        P: Parser<'a, Input, Output> + 'a,
    {
        BoxedParser {
            parser: Box::new(parser),
        }
    }
}

impl<'a, Input, Output> Parser<'a, Input, Output> for BoxedParser<'a, Input, Output> {
    fn parse(&self, input: Input) -> ParseResult<'a, Input, Output> {
        self.parser.parse(input)
    }
}

/// Provides a short-circuiting or combinator taking a parser (P1) as an
/// argument and a second parser (P2), provided via a closure thunk to prevent
/// infinitely recursing.
///
/// The second parser passed to `or` is lazily evaluated, Only if the first case
/// fails. This functions as a way to work around instances of Opaque types that
/// that could lead to type issues when using an alternative, yet similar parser
/// like `one_of`.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], 'a'))),
///   parcel::or(expect_character('b'), || expect_character('a')).parse(&input)
/// );
/// ```
pub fn or<'a, P1, P2, A, B>(parser1: P1, thunk_to_parser: impl Fn() -> P2) -> impl Parser<'a, A, B>
where
    A: Copy + 'a + Borrow<A>,
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, B>,
{
    move |input| match parser1.parse(input) {
        Ok(match_status) => match match_status {
            m @ MatchStatus::Match(_) => Ok(m),
            MatchStatus::NoMatch(_) => thunk_to_parser().parse(input),
        },
        e @ Err(_) => e,
    }
}

/// Provides a convenient shortcut for the or combinator. allowing the passing
/// of an array of matching parsers, returning the result of the first matching
/// parser or a NoMatch if none match.
///
/// Types passed to `one_of` are expected to be of the same concrete type. For
/// cases where opaque or recursive types are used please the `or` combinator
/// should be used as this captures the `Parser<A, B> -> Parser<A, C>`
/// transition.
///
/// Arguments passed to `one_of` are eagerly evaluated; if you are passing
/// the result of a function call, it is recommended to use [`or`],
/// which is lazily evaluated.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input = vec!['a', 'b', 'c'];
/// let parsers = vec![expect_character('b'), expect_character('c'), expect_character('a')];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], 'a'))),
///   parcel::one_of(parsers).parse(&input)
/// );
/// ```
pub fn one_of<'a, P, A, B>(parsers: Vec<P>) -> impl Parser<'a, A, B>
where
    A: Copy + 'a + Borrow<A>,
    P: Parser<'a, A, B>,
{
    move |input| {
        for parser in parsers.iter() {
            match parser.parse(input) {
                Ok(match_status) => match match_status {
                    m @ MatchStatus::Match(_) => return Ok(m),
                    MatchStatus::NoMatch(_) => continue,
                },
                e @ Err(_) => return e,
            };
        }

        Ok(MatchStatus::NoMatch(input))
    }
}

/// Map a `Parser<A, B>` to `Parser<A, C>` via a closure, map_fn, allowing
/// transformation of the result `B -> C`.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], "the value: a".to_string()))),
///   parcel::map(
///       expect_character('a'),
///       |res| format!("the value: {}", res)
///   ).parse(&input)
/// );
/// ```
pub fn map<'a, P, F, A: 'a, B, C>(parser: P, map_fn: F) -> impl Parser<'a, A, C>
where
    P: Parser<'a, A, B>,
    F: Fn(B) -> C + 'a,
{
    move |input| {
        parser.parse(input).map(|match_status| match match_status {
            MatchStatus::Match((next_input, result)) => {
                MatchStatus::Match((next_input, map_fn(result)))
            }
            MatchStatus::NoMatch(last_input) => MatchStatus::NoMatch(last_input),
        })
    }
}

/// Attempts to match a parser, `P`, skipping the input if it matches. For cases
/// `P` doesn't match the previous input is returned.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[1..])),
///   parcel::skip(expect_character('a')).parse(&input)
/// );
/// ```
pub fn skip<'a, P, A, B>(parser: P) -> impl Parser<'a, A, B>
where
    A: 'a,
    P: Parser<'a, A, B>,
{
    move |input| match parser.parse(input) {
        Ok(MatchStatus::Match((next_input, _))) => Ok(MatchStatus::NoMatch(next_input)),
        Ok(MatchStatus::NoMatch(last_input)) => Ok(MatchStatus::NoMatch(last_input)),
        Err(e) => Err(e),
    }
}

/// Returns a match if Parser<A, B> matches and then Parser<A, C> matches,
/// returning the results of the second parser.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[2..], 'b'))),
///   parcel::and_then(
///       expect_character('a'),
///       |_| expect_character('b'),
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[2..], "ab".to_string()))),
///   parcel::and_then(
///       expect_character('a'),
///       |first_match| expect_character('b').map(move |second_match| {
///          format!("{}{}", first_match, second_match)
///       })).parse(&input)
/// );
/// ```
pub fn and_then<'a, P1, F, P2, A, B, C>(parser: P1, f: F) -> impl Parser<'a, A, C>
where
    A: 'a,
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, C>,
    F: Fn(B) -> P2 + 'a,
{
    move |input| match parser.parse(input) {
        Ok(ms) => match ms {
            MatchStatus::Match((next_input, result)) => f(result).parse(next_input),
            MatchStatus::NoMatch(last_input) => Ok(MatchStatus::NoMatch(last_input)),
        },
        Err(e) => Err(e),
    }
}

/// this attempts to consume until n matches have occured. A match is returned
/// if 1 < result count <= n. Functionally this behaves like a bounded version
/// of the `one_or_more` parser.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input = vec!['a', 'a', 'a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[2..], vec!['a', 'a']))),
///   parcel::take_until_n(expect_character('a'), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], vec!['a']))),
///   parcel::take_until_n(expect_character('a'), 2).parse(&input)
/// );
/// ```
pub fn take_until_n<'a, P, A, B>(parser: P, n: usize) -> impl Parser<'a, A, Vec<B>>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    move |mut input| {
        let mut res_cnt = 0;
        let mut result_acc: Vec<B> = Vec::new();
        while let Ok(MatchStatus::Match((next_input, result))) = parser.parse(input) {
            if res_cnt < n {
                input = next_input;
                result_acc.push(result);
                res_cnt += 1;
            } else {
                break;
            }
        }

        if res_cnt > 0 {
            Ok(MatchStatus::Match((input, result_acc)))
        } else {
            Ok(MatchStatus::NoMatch(input))
        }
    }
}

/// take_n must match exactly n sequential matches of parser: P otherwise
/// NoMatch is returned. On a match, a Vec of the results is returned.
pub fn take_n<'a, P, A, B>(parser: P, n: usize) -> impl Parser<'a, A, Vec<B>>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    move |input| {
        let mut ni: A = input;
        let mut res_cnt = 0;
        let mut result_acc: Vec<B> = Vec::new();

        while let Ok(MatchStatus::Match((next_input, result))) = parser.parse(ni) {
            if res_cnt < n {
                ni = next_input;
                result_acc.push(result);
                res_cnt += 1;
            } else {
                break;
            }
        }

        if res_cnt == n {
            Ok(MatchStatus::Match((ni, result_acc)))
        } else {
            Ok(MatchStatus::NoMatch(input))
        }
    }
}

/// Functions much like a peek combinator in that it takes a parser (P<A, B>)
/// and a closure that accepts &B. The Parser will only return a match if F
/// asserts a match. This is useful for cases of one_or_more or zero_or_more
/// where a match must terminate.
pub fn predicate<'a, P, A, B, F>(parser: P, pred_case: F) -> impl Parser<'a, A, B>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
    F: Fn(&B) -> bool,
{
    move |input| {
        if let Ok(MatchStatus::Match((next_input, value))) = parser.parse(input) {
            if pred_case(&value) {
                return Ok(MatchStatus::Match((next_input, value)));
            }
        }
        Ok(MatchStatus::NoMatch(input))
    }
}

/// Functions much like an optional parser, consuming between zero and n values
/// that match the specified parser P.
pub fn zero_or_more<'a, P, A, B>(parser: P) -> impl Parser<'a, A, Vec<B>>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    move |mut input| {
        let mut result_acc: Vec<B> = Vec::new();
        while let Ok(MatchStatus::Match((next_input, result))) = parser.parse(input) {
            input = next_input;
            result_acc.push(result);
        }

        Ok(MatchStatus::Match((input, result_acc)))
    }
}

/// Consumes values from the input while the parser continues to return a
/// MatchStatus::Match.
pub fn one_or_more<'a, P, A, B>(parser: P) -> impl Parser<'a, A, Vec<B>>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    move |mut input| {
        let mut result_acc: Vec<B> = Vec::new();
        while let Ok(MatchStatus::Match((next_input, result))) = parser.parse(input) {
            input = next_input;
            result_acc.push(result);
        }

        if result_acc.is_empty() {
            Ok(MatchStatus::NoMatch(input))
        } else {
            Ok(MatchStatus::Match((input, result_acc)))
        }
    }
}

/// Matches zero or one
pub fn optional<'a, P, A, B>(parser: P) -> impl Parser<'a, A, Option<B>>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    move |input| match parser.parse(input) {
        Ok(MatchStatus::Match((next_input, res))) => {
            Ok(MatchStatus::Match((next_input, Some(res))))
        }
        Ok(MatchStatus::NoMatch(last_input)) => Ok(MatchStatus::Match((last_input, None))),
        Err(e) => Err(e),
    }
}

// Applicatives

/// Join attempts to match Parser<A, B> and Parser<A, C> after which it merges
/// the results to Parser<A, (B, C)>.
pub fn join<'a, P1, P2, A, B, C>(parser1: P1, parser2: P2) -> impl Parser<'a, A, (B, C)>
where
    A: Copy + Borrow<A> + 'a,
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, C>,
{
    move |input| {
        parser1
            .parse(input)
            .and_then(|match_status| match match_status {
                MatchStatus::NoMatch(_) => Ok(MatchStatus::NoMatch(input)),
                MatchStatus::Match((p1_input, result1)) => {
                    parser2.parse(p1_input).map(|p2_ms| match p2_ms {
                        MatchStatus::NoMatch(_) => MatchStatus::NoMatch(input),
                        MatchStatus::Match((p2_input, result2)) => {
                            MatchStatus::Match((p2_input, (result1, result2)))
                        }
                    })
                }
            })
    }
}

/// Left expects to take the results of join, returning a Parser<A, (B, C)>
/// and then extrapolates the value left-hand value, returning a Parser<A, B>.
pub fn left<'a, P, A, B, C>(parser: P) -> impl Parser<'a, A, B>
where
    A: Copy + Borrow<A> + 'a,
    B: 'a,
    C: 'a,
    P: Parser<'a, A, (B, C)> + 'a,
{
    parser.map(|(b, _)| b)
}

/// Right expects to take the results of join, returning a Parser<A, (B, C)>
/// and then extrapolates the value right-hand value, returning a Parser<A, C>.
pub fn right<'a, P, A, B, C>(parser: P) -> impl Parser<'a, A, C>
where
    A: Copy + Borrow<A> + 'a,
    B: 'a,
    C: 'a,
    P: Parser<'a, A, (B, C)> + 'a,
{
    parser.map(|(_, c)| c)
}
