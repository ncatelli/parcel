//! This crate functions as an implementation of parser combinators in rust,
//! heavily inspired by the article by Bodil Stokke. While the goal of this
//! crate is to be functional for both text and binary grammars I'd highly
//! recommend against using it for anything other than experimentation.
//! Instead, recommending Geal/nom.

#![no_std]

#[cfg(feature = "std")]
extern crate std;

extern crate alloc;
use alloc::{boxed::Box, string::String, vec::Vec};

pub mod formatter;
pub mod parsers;
pub mod prelude;

#[cfg(test)]
mod tests;

use core::borrow::Borrow;
use core::marker::PhantomData;

/// Span defines represents a range that covers the indexes into an input that
/// a given pattern matches.
pub type Span = core::ops::Range<usize>;

/// MatchStatus represents a non-error parser result with two cases, signifying
/// whether the parse returned a match or not.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum MatchStatus<U, T> {
    Match { span: Span, remainder: U, inner: T },
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
    /// let v = parcel::MatchStatus::<&[char], char>::Match{span: 0..1, remainder: &input[1..], inner: 'a'};
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
            Self::Match {
                span: _,
                remainder: _,
                inner,
            } => inner,
            _ => panic!("unable to unwrap inner value: NoMatch"),
        }
    }

    /// Returns the contained `Match` value, consuming the `self` value.
    ///
    /// Arguments passed to `unwrap_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use `unwrap_or_else`,
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
            Self::Match {
                span: _,
                remainder: _,
                inner,
            } => inner,
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
            Self::Match {
                span: _,
                remainder: _,
                inner,
            } => inner,
            _ => f(),
        }
    }

    /// Returns the contained Span on a `Match` value.
    ///
    /// # Examples
    ///
    /// ```
    /// let input = vec!['a'];
    /// let v = parcel::MatchStatus::<&[char], char>::Match{span: 0..1, remainder: &input[1..], inner: 'a'};
    /// assert_eq!(v.as_span(), Some(0..1));
    /// ```
    pub fn as_span(&self) -> Option<Span> {
        match self {
            Self::Match {
                span,
                remainder: _,
                inner: _,
            } => Some(span.clone()),
            _ => None,
        }
    }

    /// This method transforms type `parcel::MatchStatus<U, T>` to type
    /// `Option<T>`. If the type is of the `Match` variant `Option::Some(T)` is
    /// returned otherwise `Option::None`. is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// let input = vec!['a'];
    /// assert_eq!(
    ///   Some('a'),
    ///   parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}.some()
    ///  );
    /// ```
    pub fn some(self) -> Option<T> {
        match self {
            MatchStatus::Match {
                span: _,
                remainder: _,
                inner,
            } => Some(inner),
            MatchStatus::NoMatch(_) => None,
        }
    }

    /// This method transforms type `parcel::MatchStatus<U, T>` to type
    /// `parcel::MatchStatus<U, V>` via a closure, map_fn, allowing
    /// transformation ofthe result from `T -> V`.
    ///
    /// # Examples
    ///
    /// ```
    /// let input = vec!['a'];
    /// assert_eq!(
    ///   parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: true},
    ///   parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}.map(|c| c.is_ascii())
    ///  );
    /// ```
    pub fn map<V, F>(self, map_fn: F) -> MatchStatus<U, V>
    where
        F: FnOnce(T) -> V,
    {
        match self {
            MatchStatus::Match {
                span,
                remainder,
                inner,
            } => MatchStatus::Match {
                span,
                remainder,
                inner: map_fn(inner),
            },
            MatchStatus::NoMatch(rem) => MatchStatus::NoMatch(rem),
        }
    }

    /// This method transforms type `parcel::MatchStatus<U, T>` to type
    /// `parcel::MatchStatus<U, V>` via a closure, map_fn, which is called only
    /// for cases of `Match`. Allowing for addition countrol of the match
    /// variant from within the closure.
    ///
    /// # Examples
    ///
    /// ```
    /// let input = vec!['a'];
    /// assert_eq!(
    ///   parcel::MatchStatus::Match{
    ///     span: 0..1,
    ///     remainder: &input[1..],
    ///     inner: true,
    ///   },
    ///   parcel::MatchStatus::Match{
    ///     span: 0..1,
    ///     remainder: &input[1..],
    ///     inner: 'a'
    ///   }.and_then(|ms| parcel::MatchStatus::Match{
    ///     span: 0..1,
    ///     remainder: &input[1..],
    ///     inner: true,
    ///   })
    ///  );
    /// ```
    pub fn and_then<V, F>(self, map_fn: F) -> MatchStatus<U, V>
    where
        F: FnOnce(Self) -> MatchStatus<U, V>,
    {
        match self {
            ms @ MatchStatus::Match { .. } => map_fn(ms),
            MatchStatus::NoMatch(rem) => MatchStatus::NoMatch(rem),
        }
    }
}

/// Spanning provides a methods for referencing span data on a type.
pub trait Spanning {
    fn start(&self) -> usize {
        0
    }
    fn end(&self) -> usize {
        0
    }
    fn span(&self) -> Span {
        self.start()..self.end()
    }
}

// Generic implementation for enumerated inputs.
impl<'a, T> Spanning for &'a [(usize, T)] {
    fn start(&self) -> usize {
        self.first().map(|first| first.0).unwrap_or(0)
    }

    fn end(&self) -> usize {
        self.last().map(|first| first.0).unwrap_or(0)
    }
}

/// Represents the state of parser execution, wrapping the above
/// MatchStatus and providing an Error string for any problems.
pub type ParseResult<'a, A, B> = Result<MatchStatus<A, B>, String>;

/// Parser is the primary trait serving as the basis for all child combinators.
/// The most important function defined in this trait is parse, which defines
/// the function that will be called for all child parsers. As a convenience,
/// Boxed Implementations of Parser functions are included as trait defaults,
/// allowing chained parser calls to be made for the sake of code cleanliness.
pub trait Parser<'a, A, B> {
    fn parse(&self, input: A) -> ParseResult<'a, A, B>;

    /// Provides a short-circuiting or combinator taking a parser (P), provided
    /// via a closure thunk to prevent infinitely recursing.
    ///
    /// The parser passed to `or` is lazily evaluated, Only if the first case
    /// fails. This functions as a way to work around instances of Opaque types
    /// that could lead to type issues when using an alternative, yet similar
    /// parser like `one_of`.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
    ///   expect_character('b').or(|| expect_character('a')).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
    ///   expect_byte(0x01).or(|| expect_byte(0x00)).parse(&input)
    /// );
    /// ```
    fn or<P, F>(self, thunk: F) -> BoxedParser<'a, A, B>
    where
        Self: Sized + 'a,
        A: Copy + 'a,
        B: 'a,
        P: Parser<'a, A, B> + 'a,
        F: Fn() -> P + 'a,
    {
        BoxedParser::new(or(self, thunk))
    }

    /// Returns a match if Parser<A, B> matches and then Parser<A, C> matches,
    /// returning the results of the second parser.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: 'b'}),
    ///   expect_character('a').and_then(|_| expect_character('b')).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: "ab".to_string()}),
    ///   expect_character('a').and_then(
    ///       |first_match| expect_character('b').map(move |second_match| {
    ///          format!("{}{}", first_match, second_match)
    ///       })).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: 0x01}),
    ///   expect_byte(0x00).and_then(|_| expect_byte(0x01)).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: "01".to_string()}),
    ///   expect_byte(0x00).and_then(
    ///       |first_match| expect_byte(0x01).map(move |second_match| {
    ///          format!("{}{}", first_match, second_match)
    ///       })).parse(&input)
    /// );
    /// ```
    fn and_then<F, NextParser, C>(self, thunk: F) -> BoxedParser<'a, A, C>
    where
        Self: Sized + 'a,
        A: 'a,
        B: 'a,
        C: 'a,
        NextParser: Parser<'a, A, C> + 'a,
        F: Fn(B) -> NextParser + 'a,
    {
        BoxedParser::new(and_then(self, thunk))
    }

    /// Returns a match if Parser<A, B> matches and then Parser<A, C> matches,
    /// returning the results of the first parser without consuming the second
    /// value.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
    ///     expect_character('a')
    ///         .peek_next(expect_character('b'))
    ///         .parse(&input[0..])
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///     Ok(MatchStatus::NoMatch(&input[0..])),
    ///     expect_character('a')
    ///         .peek_next(expect_character('c'))
    ///         .parse(&input[0..])
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
    ///     expect_byte(0x00)
    ///         .peek_next(expect_byte(0x01))
    ///         .parse(&input[0..])
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///     Ok(MatchStatus::NoMatch(&input[0..])),
    ///     expect_byte(0x00)
    ///         .peek_next(expect_byte(0x02))
    ///         .parse(&input[0..])
    /// );
    /// ```
    fn peek_next<NextParser, C>(self, second: NextParser) -> BoxedParser<'a, A, B>
    where
        Self: Sized + 'a,
        A: Copy + Borrow<A> + 'a,
        B: 'a,
        C: 'a,
        NextParser: Parser<'a, A, C> + 'a,
    {
        BoxedParser::new(peek_next(self, second))
    }

    /// Attempts to consume until n matches have occured. A match is returned
    /// if 1 < result count <= n. Functionally this behaves like a bounded
    /// version of the `one_or_more` parser.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'a', 'a'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
    ///   expect_character('a').take_until_n(2).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: vec!['a']}),
    ///   expect_character('a').take_until_n(2).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x00].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
    ///   expect_byte(0x00).take_until_n(2).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: vec![0x00]}),
    ///   expect_byte(0x00).take_until_n(2).parse(&input)
    /// );
    /// ```
    fn take_until_n(self, n: usize) -> BoxedParser<'a, A, Vec<B>>
    where
        Self: Sized + 'a,
        A: Copy + 'a,
        B: 'a,
    {
        BoxedParser::new(take_until_n(self, n))
    }

    /// `take_n` must match exactly n sequential matches of parser: `P`
    /// otherwise `NoMatch` is returned. On a match, a `Vec` of the results is
    /// returned. Functionally this behaves like the `take_until_n` parser with
    /// a single expected match count.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'a', 'a'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
    ///   expect_character('a').take_n(2).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
    ///   expect_character('a').take_n(2).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x00].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
    ///   expect_byte(0x00).take_n(2).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
    ///   expect_byte(0x00).take_n(2).parse(&input)
    /// );
    /// ```
    fn take_n(self, n: usize) -> BoxedParser<'a, A, Vec<B>>
    where
        Self: Sized + 'a,
        A: Copy + 'a,
        B: 'a,
    {
        BoxedParser::new(take_n(self, n))
    }

    /// Functions much like a peek combinator in that it takes a closure that
    /// accepts `&B`. The parser will only return a match if `F
    /// asserts a match. This is useful for cases of `one_or_more` or
    /// `zero_or_more` where a match must terminate.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::any_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
    ///   any_character().predicate(|&c| c != 'c').parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::any_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'b']}),
    ///   parcel::one_or_more(
    ///       any_character().predicate(|&c| c != 'c')
    ///   ).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::any_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
    ///   any_byte().predicate(|&b| b != 0x02).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::any_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x01]}),
    ///   parcel::one_or_more(
    ///       any_byte().predicate(|&b| b != 0x02)
    ///   ).parse(&input)
    /// );
    /// ```
    fn predicate<F>(self, predicate_case: F) -> BoxedParser<'a, A, B>
    where
        Self: Sized + 'a,
        A: Copy + 'a,
        B: 'a,
        F: Fn(&B) -> bool + 'a,
    {
        BoxedParser::new(predicate(self, predicate_case))
    }

    /// Functions much like an optional parser, consuming between zero and n
    /// values that match the specified parser `P`.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'a', 'b'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
    ///   expect_character('a').zero_or_more().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: vec![]}),
    ///   expect_character('c').zero_or_more().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 1..1, remainder: &input[1..], inner: vec![]}),
    ///   expect_character('a').and_then(|_| expect_character('c').zero_or_more()).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
    ///   expect_byte(0x00).zero_or_more().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: vec![]}),
    ///   expect_byte(0x02).zero_or_more().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 1..1, remainder: &input[1..], inner: vec![]}),
    ///   expect_byte(0x00).and_then(|_| expect_byte(0x02).zero_or_more()).parse(&input)
    /// );
    /// ```
    fn zero_or_more(self) -> BoxedParser<'a, A, Vec<B>>
    where
        Self: Sized + 'a,
        A: Copy + Spanning + 'a,
        B: 'a,
    {
        BoxedParser::new(zero_or_more(self))
    }

    /// Consumes values from the input while the parser continues to return a
    /// MatchStatus::Match.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'a', 'b'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
    ///   expect_character('a').one_or_more().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
    ///   expect_character('c').one_or_more().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
    ///   expect_byte(0x00).one_or_more().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
    ///   expect_byte(0x02).one_or_more().parse(&input)
    /// );
    /// ```
    fn one_or_more(self) -> BoxedParser<'a, A, Vec<B>>
    where
        Self: Sized + 'a,
        A: Copy + 'a,
        B: 'a,
    {
        BoxedParser::new(one_or_more(self))
    }

    /// Map transforms a `Parser<A, B>` to `Parser<A, C>` via a closure,
    /// map_fn, allowing transformation of the result `B -> C`.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'a', 'b'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: "a".to_string()}),
    ///   expect_character('a').map(
    ///       |res| format!("{}", res)
    ///   ).parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: "0".to_string()}),
    ///   expect_byte(0x00).map(
    ///       |res| format!("{}", res)
    ///   ).parse(&input)
    /// );
    /// ```
    fn map<F, C>(self, map_fn: F) -> BoxedParser<'a, A, C>
    where
        Self: Sized + 'a,
        A: 'a,
        B: 'a,
        C: 'a,
        F: Fn(B) -> C + 'a,
    {
        BoxedParser::new(map(self, map_fn))
    }

    /// Attempts to match preceeding parser `P`, skipping the input if it
    /// matches. For cases where `P` doesn't match the previous input is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::NoMatch(&input[1..])),
    ///   expect_character('a').skip().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::NoMatch(&input[1..])),
    ///   expect_byte(0x00).skip().parse(&input)
    /// );
    /// ```
    fn skip(self) -> BoxedParser<'a, A, B>
    where
        Self: Sized + 'a,
        A: 'a,
        B: 'a,
    {
        BoxedParser::new(skip(self))
    }

    /// Provides optional matching of a value, returning `Parser<A, Option<B>>`.
    /// For cases where the value is not present, a match with a `None` value is
    /// returned. Otherwise a match with a `Some<B>` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: Some('a')}),
    ///   expect_character('a').optional().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::character::expect_character;
    /// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: None}),
    ///   expect_character('c').optional().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: Some(0x00)}),
    ///   expect_byte(0x00).optional().parse(&input)
    /// );
    /// ```
    ///
    /// ```
    /// use parcel::prelude::v1::*;
    /// use parcel::parsers::byte::expect_byte;
    /// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
    /// assert_eq!(
    ///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: None}),
    ///   expect_byte(0x02).optional().parse(&input)
    /// );
    /// ```
    fn optional(self) -> BoxedParser<'a, A, Option<B>>
    where
        Self: Sized + 'a,
        A: Copy + Spanning + 'a,
        B: 'a,
    {
        BoxedParser::new(optional(self))
    }
}

impl<'a, F, A, B> Parser<'a, A, B> for F
where
    A: 'a,
    F: Fn(A) -> ParseResult<'a, A, B>,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, B> {
        self(input)
    }
}

/// Provides a boxed wrapper to any parser trait implementation. More or less,
/// this maps a `Parser<A, B>` -> `Box<dyn Parser<A, B>>`.
pub struct BoxedParser<'a, A, B> {
    parser: Box<dyn Parser<'a, A, B> + 'a>,
}

impl<'a, A, B> BoxedParser<'a, A, B> {
    pub fn new<P>(parser: P) -> Self
    where
        P: Parser<'a, A, B> + 'a,
    {
        BoxedParser {
            parser: Box::new(parser),
        }
    }
}

impl<'a, A, B> Parser<'a, A, B> for BoxedParser<'a, A, B> {
    fn parse(&self, input: A) -> ParseResult<'a, A, B> {
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
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
///
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
///   parcel::Or::new(expect_character('b'), expect_character('a')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
///
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::Or::new(expect_character('b'), expect_character('c')).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct Or<P1, P2> {
    p1: P1,
    p2: P2,
}

impl<P1, P2> Or<P1, P2> {
    pub fn new(p1: P1, p2: P2) -> Self {
        Self { p1, p2 }
    }
}

impl<'a, A, B, P1, P2> Parser<'a, A, B> for Or<P1, P2>
where
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, B>,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, B> {
        match self.p1.parse(input) {
            Ok(ms) => match ms {
                m @ MatchStatus::Match {
                    span: _,
                    remainder: _,
                    inner: _,
                } => Ok(m),
                MatchStatus::NoMatch(input) => self.p2.parse(input),
            },
            e @ Err(_) => e,
        }
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
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
///   parcel::or(expect_character('b'), || expect_character('a')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
///   parcel::or(expect_byte(0x01), || expect_byte(0x00)).parse(&input)
/// );
/// ```
pub fn or<'a, P1, P2, F, A, B>(parser1: P1, thunk_to_parser: F) -> impl Parser<'a, A, B>
where
    A: Copy + 'a + Borrow<A>,
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, B>,
    F: Fn() -> P2,
{
    Or::new(parser1, thunk_to_parser())
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
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// let parsers = vec![expect_character('b'), expect_character('c'), expect_character('a')];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
///   parcel::OneOf::new(parsers).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// let parsers = vec![expect_byte(0x01), expect_byte(0x02), expect_byte(0x00)];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
///   parcel::OneOf::new(parsers).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct OneOf<P> {
    parsers: Vec<P>,
}

impl<P> OneOf<P> {
    pub fn new(parsers: Vec<P>) -> Self {
        Self { parsers }
    }
}

impl<'a, A, B, P> Parser<'a, A, B> for OneOf<P>
where
    A: Copy + Borrow<A> + 'a,
    P: Parser<'a, A, B>,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, B> {
        for parser in self.parsers.iter() {
            match parser.parse(input) {
                Ok(ms) => match ms {
                    m @ MatchStatus::Match {
                        span: _,
                        remainder: _,
                        inner: _,
                    } => return Ok(m),
                    MatchStatus::NoMatch(_) => continue,
                },
                e @ Err(_) => return e,
            };
        }

        Ok(MatchStatus::NoMatch(input))
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
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// let parsers = vec![expect_character('b'), expect_character('c'), expect_character('a')];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
///   parcel::one_of(parsers).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// let parsers = vec![expect_byte(0x01), expect_byte(0x02), expect_byte(0x00)];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
///   parcel::one_of(parsers).parse(&input)
/// );
/// ```
pub fn one_of<'a, P, A, B>(parsers: Vec<P>) -> impl Parser<'a, A, B>
where
    A: Copy + Borrow<A> + 'a,
    P: Parser<'a, A, B>,
{
    OneOf::new(parsers)
}

/// Map transforms a `Parser<A, B>` to `Parser<A, C>` via a closure, map_fn,
/// allowing transformation of the result `B -> C`.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: "a".to_string()}),
///   parcel::Map::new(
///       expect_character('a'),
///       |res| format!("{}", res)
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::Map;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: "0".to_string()}),
///   parcel::Map::new(
///       expect_byte(0x00),
///       |res| format!("{}", res)
///   ).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct Map<P, F, A, B, C> {
    input: PhantomData<A>,
    output_one: PhantomData<B>,
    output_two: PhantomData<C>,
    parser: P,
    map_fn: F,
}

impl<P, F, A, B, C> Map<P, F, A, B, C> {
    pub fn new(parser: P, map_fn: F) -> Self {
        Self {
            input: PhantomData,
            output_one: PhantomData,
            output_two: PhantomData,
            parser,
            map_fn,
        }
    }
}

impl<'a, P, F, A, B, C> Parser<'a, A, C> for Map<P, F, A, B, C>
where
    P: Parser<'a, A, B>,
    F: Fn(B) -> C + 'a,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, C> {
        self.parser.parse(input).map(|ms| match ms {
            MatchStatus::Match {
                span,
                remainder,
                inner,
            } => MatchStatus::Match {
                span,
                remainder,
                inner: (self.map_fn)(inner),
            },
            MatchStatus::NoMatch(last_input) => MatchStatus::NoMatch(last_input),
        })
    }
}

/// Map transforms a `Parser<A, B>` to `Parser<A, C>` via a closure, map_fn,
/// allowing transformation of the result `B -> C`.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: "a".to_string()}),
///   parcel::map(
///       expect_character('a'),
///       |res| format!("{}", res)
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: "0".to_string()}),
///   parcel::map(
///       expect_byte(0x00),
///       |res| format!("{}", res)
///   ).parse(&input)
/// );
/// ```
pub fn map<'a, P, F, A: 'a, B, C>(parser: P, map_fn: F) -> impl Parser<'a, A, C>
where
    P: Parser<'a, A, B>,
    F: Fn(B) -> C + 'a,
{
    Map::new(parser, map_fn)
}

/// Attempts to match a parser, `P`, skipping the input if it matches. For cases
/// `P` doesn't match the previous input is returned.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[1..])),
///   parcel::Skip::new(expect_character('a')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[1..])),
///   parcel::Skip::new(expect_byte(0x00)).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct Skip<P> {
    parser: P,
}

impl<P> Skip<P> {
    pub fn new(parser: P) -> Self {
        Self { parser }
    }
}

impl<'a, A, B, P> Parser<'a, A, B> for Skip<P>
where
    A: 'a,
    P: Parser<'a, A, B>,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, B> {
        match self.parser.parse(input) {
            Ok(MatchStatus::Match {
                span: _,
                remainder,
                inner: _,
            }) => Ok(MatchStatus::NoMatch(remainder)),
            Ok(MatchStatus::NoMatch(last_input)) => Ok(MatchStatus::NoMatch(last_input)),
            Err(e) => Err(e),
        }
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
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[1..])),
///   parcel::skip(expect_character('a')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[1..])),
///   parcel::skip(expect_byte(0x00)).parse(&input)
/// );
/// ```
pub fn skip<'a, P, A, B>(parser: P) -> impl Parser<'a, A, B>
where
    A: 'a,
    P: Parser<'a, A, B>,
{
    Skip::new(parser)
}

/// Returns a match if Parser<A, B> matches and then Parser<A, C> matches,
/// returning the results of the second parser.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: 'b'}),
///   parcel::AndThen::new(
///       expect_character('a'),
///       |_| expect_character('b'),
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: "ab".to_string()}),
///   parcel::AndThen::new(
///       expect_character('a'),
///       |first_match| expect_character('b').map(move |second_match| {
///          format!("{}{}", first_match, second_match)
///       })).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: 0x01}),
///   parcel::AndThen::new(
///       expect_byte(0x00),
///       |_| expect_byte(0x01),
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: "01".to_string()}),
///   parcel::AndThen::new(
///       expect_byte(0x00),
///       |first_match| expect_byte(0x01).map(move |second_match| {
///          format!("{}{}", first_match, second_match)
///       })).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct AndThen<P1, P2, F, A, B, C> {
    input: PhantomData<A>,
    output_one: PhantomData<B>,
    output_two: PhantomData<C>,
    parser1: P1,
    parser2: PhantomData<P2>,
    f: F,
}

impl<P1, P2, F, A, B, C> AndThen<P1, P2, F, A, B, C> {
    pub fn new(parser1: P1, f: F) -> Self {
        Self {
            input: PhantomData,
            output_one: PhantomData,
            output_two: PhantomData,
            parser1,
            parser2: PhantomData,
            f,
        }
    }
}

impl<'a, P1, P2, F, A, B, C> Parser<'a, A, C> for AndThen<P1, P2, F, A, B, C>
where
    A: 'a,
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, C>,
    F: Fn(B) -> P2 + 'a,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, C> {
        match self.parser1.parse(input) {
            Ok(ms) => match ms {
                MatchStatus::Match {
                    span: _,
                    remainder,
                    inner,
                } => (self.f)(inner).parse(remainder),

                MatchStatus::NoMatch(last_input) => Ok(MatchStatus::NoMatch(last_input)),
            },
            Err(e) => Err(e),
        }
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
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: 'b'}),
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
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: "ab".to_string()}),
///   parcel::and_then(
///       expect_character('a'),
///       |first_match| expect_character('b').map(move |second_match| {
///          format!("{}{}", first_match, second_match)
///       })).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: 0x01}),
///   parcel::and_then(
///       expect_byte(0x00),
///       |_| expect_byte(0x01),
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..2, remainder: &input[2..], inner: "01".to_string()}),
///   parcel::and_then(
///       expect_byte(0x00),
///       |first_match| expect_byte(0x01).map(move |second_match| {
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
    AndThen::new(parser, f)
}

/// Returns a match if Parser<A, B> matches and then Parser<A, C> matches,
/// returning the results of the first parser without consuming the second
/// value.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
///   parcel::PeekNext::new(
///       expect_character('a'),
///       expect_character('b'),
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::PeekNext::new(
///       expect_character('a'),
///       expect_character('c'),
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
///   parcel::PeekNext::new(
///       expect_byte(0x00),
///       expect_byte(0x01),
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::PeekNext::new(
///       expect_byte(0x00),
///       expect_byte(0x02),
///   ).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct PeekNext<P1, P2, A, B, C> {
    input: PhantomData<A>,
    output_one: PhantomData<B>,
    output_two: PhantomData<C>,
    parser1: P1,
    parser2: P2,
}

impl<P1, P2, A, B, C> PeekNext<P1, P2, A, B, C> {
    pub fn new(parser1: P1, parser2: P2) -> Self {
        Self {
            input: PhantomData,
            output_one: PhantomData,
            output_two: PhantomData,
            parser1,
            parser2,
        }
    }
}

impl<'a, P1, P2, A, B, C> Parser<'a, A, B> for PeekNext<P1, P2, A, B, C>
where
    A: Copy + Borrow<A> + 'a,
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, C>,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, B> {
        match self.parser1.parse(input) {
            Ok(ms) => match ms {
                MatchStatus::Match {
                    span,
                    remainder,
                    inner,
                } => {
                    let initial_input = remainder;
                    if let Ok(MatchStatus::Match {
                        span: _,
                        remainder: _,
                        inner: _,
                    }) = self.parser2.parse(initial_input)
                    {
                        Ok(MatchStatus::Match {
                            span,
                            remainder,
                            inner,
                        })
                    } else {
                        Ok(MatchStatus::NoMatch(input))
                    }
                }
                MatchStatus::NoMatch(last_input) => Ok(MatchStatus::NoMatch(last_input)),
            },
            Err(e) => Err(e),
        }
    }
}

/// Returns a match if Parser<A, B> matches and then Parser<A, C> matches,
/// returning the results of the first parser without consuming the second
/// value.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
///   parcel::peek_next(
///       expect_character('a'),
///       expect_character('b'),
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::peek_next(
///       expect_character('a'),
///       expect_character('c'),
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
///   parcel::peek_next(
///       expect_byte(0x00),
///       expect_byte(0x01),
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::peek_next(
///       expect_byte(0x00),
///       expect_byte(0x02),
///   ).parse(&input)
/// );
/// ```
pub fn peek_next<'a, P1, P2, A, B, C>(first: P1, second: P2) -> impl Parser<'a, A, B>
where
    A: Copy + Borrow<A> + 'a,
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, C>,
{
    PeekNext::new(first, second)
}

/// This attempts to consume until n matches have occured. A match is returned
/// if 1 < result count <= n. Functionally this behaves like a bounded version
/// of the `one_or_more` parser.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'a', 'a'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
///   parcel::TakeUntilN::new(expect_character('a'), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: vec!['a']}),
///   parcel::TakeUntilN::new(expect_character('a'), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x00].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
///   parcel::TakeUntilN::new(expect_byte(0x00), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input = vec![0x00, 0x01, 0x02];
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: vec![0x00]}),
///   parcel::TakeUntilN::new(expect_byte(0x00), 2).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct TakeUntilN<P> {
    parser: P,
    n: usize,
}

impl<P> TakeUntilN<P> {
    pub fn new(parser: P, n: usize) -> Self {
        Self { parser, n }
    }
}

impl<'a, P, A, B> Parser<'a, A, Vec<B>> for TakeUntilN<P>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    fn parse(&self, mut input: A) -> ParseResult<'a, A, Vec<B>> {
        let mut res_cnt = 0;
        let mut span_acc: Vec<Span> = Vec::new();
        let mut result_acc: Vec<B> = Vec::new();
        while let Ok(MatchStatus::Match {
            span,
            remainder,
            inner,
        }) = self.parser.parse(input)
        {
            if res_cnt < self.n {
                input = remainder;
                span_acc.push(span);
                result_acc.push(inner);
                res_cnt += 1;
            } else {
                break;
            }
        }

        if res_cnt > 0 {
            // these are safe to unwrap due to the res_cnt gate.
            let start = span_acc.first().unwrap().start;
            let end = span_acc.last().unwrap().end;

            Ok(MatchStatus::Match {
                span: start..end,
                remainder: input,
                inner: result_acc,
            })
        } else {
            Ok(MatchStatus::NoMatch(input))
        }
    }
}

/// This attempts to consume until n matches have occured. A match is returned
/// if 1 < result count <= n. Functionally this behaves like a bounded version
/// of the `one_or_more` parser.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'a', 'a'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
///   parcel::take_until_n(expect_character('a'), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: vec!['a']}),
///   parcel::take_until_n(expect_character('a'), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x00].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
///   parcel::take_until_n(expect_byte(0x00), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input = vec![0x00, 0x01, 0x02];
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: vec![0x00]}),
///   parcel::take_until_n(expect_byte(0x00), 2).parse(&input)
/// );
/// ```
pub fn take_until_n<'a, P, A, B>(parser: P, n: usize) -> impl Parser<'a, A, Vec<B>>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    TakeUntilN::new(parser, n)
}

/// `take_n` must match exactly n sequential matches of parser: `P` otherwise
/// `NoMatch` is returned. On a match, a `Vec` of the results is returned.
/// Functionally this behaves like the `take_until_n` parser with a single
/// expected match count.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'a', 'a'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
///   parcel::TakeN::new(expect_character('a'), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::TakeN::new(expect_character('a'), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x00].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
///   parcel::TakeN::new(expect_byte(0x00), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::TakeN::new(expect_byte(0x00), 2).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct TakeN<P> {
    parser: P,
    n: usize,
}

impl<P> TakeN<P> {
    pub fn new(parser: P, n: usize) -> Self {
        Self { parser, n }
    }
}

impl<'a, P, A, B> Parser<'a, A, Vec<B>> for TakeN<P>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, Vec<B>> {
        let mut ni = input;

        let mut res_cnt = 0;
        let mut span_acc: Vec<Span> = Vec::new();
        let mut result_acc: Vec<B> = Vec::new();
        while let Ok(MatchStatus::Match {
            span,
            remainder,
            inner,
        }) = self.parser.parse(ni)
        {
            if res_cnt < self.n {
                ni = remainder;
                span_acc.push(span);
                result_acc.push(inner);
                res_cnt += 1;
            } else {
                break;
            }
        }

        if res_cnt == self.n {
            // these are safe to unwrap due to the res_cnt gate.
            let start = span_acc.first().unwrap().start;
            let end = span_acc.last().unwrap().end;

            Ok(MatchStatus::Match {
                span: start..end,
                remainder: ni,
                inner: result_acc,
            })
        } else {
            Ok(MatchStatus::NoMatch(input))
        }
    }
}

/// `take_n` must match exactly n sequential matches of parser: `P` otherwise
/// `NoMatch` is returned. On a match, a `Vec` of the results is returned.
/// Functionally this behaves like the `take_until_n` parser with a single
/// expected match count.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'a', 'a'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
///   parcel::take_n(expect_character('a'), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::take_n(expect_character('a'), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x00].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
///   parcel::take_n(expect_byte(0x00), 2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::take_n(expect_byte(0x00), 2).parse(&input)
/// );
/// ```
pub fn take_n<'a, P, A, B>(parser: P, n: usize) -> impl Parser<'a, A, Vec<B>>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    TakeN::new(parser, n)
}

/// Functions much like a peek combinator in that it takes a parser `P<A, B>`
/// and a closure that accepts `&B`. The parser will only return a match if `F
/// asserts a match. This is useful for cases of `one_or_more` or
/// `zero_or_more` where a match must terminate.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::any_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
///   parcel::Predicate::new(any_character(), |&c| c != 'c').parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::any_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'b']}),
///   parcel::one_or_more(
///       parcel::Predicate::new(any_character(), |&c| c != 'c')
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::any_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
///   parcel::predicate(any_byte(), |&b| b != 0x02).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::any_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x01]}),
///   parcel::one_or_more(
///       parcel::Predicate::new(any_byte(), |&b| b != 0x02)
///   ).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct Predicate<P, F, A, B>
where
    F: Fn(&B) -> bool,
{
    input: PhantomData<A>,
    output: PhantomData<B>,
    parser: P,
    pred_case: F,
}

impl<P, F, A, B> Predicate<P, F, A, B>
where
    F: Fn(&B) -> bool,
{
    pub fn new(parser: P, pred_case: F) -> Self {
        Self {
            input: PhantomData,
            output: PhantomData,
            parser,
            pred_case,
        }
    }
}

impl<'a, P, F, A, B> Parser<'a, A, B> for Predicate<P, F, A, B>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
    F: Fn(&B) -> bool,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, B> {
        if let Ok(MatchStatus::Match {
            span,
            remainder,
            inner,
        }) = self.parser.parse(input)
        {
            if (self.pred_case)(&inner) {
                return Ok(MatchStatus::Match {
                    span,
                    remainder,
                    inner,
                });
            }
        }

        Ok(MatchStatus::NoMatch(input))
    }
}

/// Functions much like a peek combinator in that it takes a parser `P<A, B>`
/// and a closure that accepts `&B`. The parser will only return a match if `F
/// asserts a match. This is useful for cases of `one_or_more` or
/// `zero_or_more` where a match must terminate.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::any_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 'a'}),
///   parcel::predicate(any_character(), |&c| c != 'c').parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::any_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'b']}),
///   parcel::one_or_more(
///       parcel::predicate(any_character(), |&c| c != 'c')
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::any_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
///   parcel::predicate(any_byte(), |&b| b != 0x02).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::any_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x01]}),
///   parcel::one_or_more(
///       parcel::predicate(any_byte(), |&b| b != 0x02)
///   ).parse(&input)
/// );
/// ```
pub fn predicate<'a, P, F, A, B>(parser: P, pred_case: F) -> impl Parser<'a, A, B>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
    F: Fn(&B) -> bool,
{
    Predicate::new(parser, pred_case)
}

/// Functions much like an optional parser, consuming between zero and n values
/// that match the specified parser `P`.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'a', 'b'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
///   parcel::ZeroOrMore::new(expect_character('a')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: vec![]}),
///   parcel::ZeroOrMore::new(expect_character('c')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..1, remainder: &input[1..], inner: vec![]}),
///   parcel::AndThen::new(
///     expect_character('a'),
///     |_| parcel::ZeroOrMore::new(expect_character('c'))
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
///   parcel::ZeroOrMore::new(expect_byte(0x00)).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: vec![]}),
///   parcel::ZeroOrMore::new(expect_byte(0x02)).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..1, remainder: &input[1..], inner: vec![]}),
///   parcel::AndThen::new(
///     expect_byte(0x00),
///     |_| parcel::ZeroOrMore::new(expect_byte(0x02)),
///   ).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct ZeroOrMore<P> {
    parser: P,
}

impl<P> ZeroOrMore<P> {
    pub fn new(parser: P) -> Self {
        Self { parser }
    }
}

impl<'a, P, A, B> Parser<'a, A, Vec<B>> for ZeroOrMore<P>
where
    A: Copy + Spanning + 'a,
    P: Parser<'a, A, B>,
{
    fn parse(&self, mut input: A) -> ParseResult<'a, A, Vec<B>> {
        let mut span_acc: Vec<Span> = Vec::new();
        let mut result_acc: Vec<B> = Vec::new();

        while let Ok(MatchStatus::Match {
            span,
            remainder,
            inner,
        }) = self.parser.parse(input)
        {
            input = remainder;
            span_acc.push(span);
            result_acc.push(inner);
        }

        if !result_acc.is_empty() {
            let start = span_acc.first().unwrap().start;
            let end = span_acc.last().unwrap().end;

            Ok(MatchStatus::Match {
                span: start..end,
                remainder: input,
                inner: result_acc,
            })
        } else {
            let span = input.start()..input.start();
            Ok(MatchStatus::Match {
                span,
                remainder: input,
                inner: result_acc,
            })
        }
    }
}

/// Functions much like an optional parser, consuming between zero and n values
/// that match the specified parser `P`.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'a', 'b'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
///   parcel::zero_or_more(expect_character('a')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: vec![]}),
///   parcel::zero_or_more(expect_character('c')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
///   parcel::zero_or_more(expect_byte(0x00)).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: vec![]}),
///   parcel::zero_or_more(expect_byte(0x02)).parse(&input)
/// );
/// ```
pub fn zero_or_more<'a, P, A, B>(parser: P) -> impl Parser<'a, A, Vec<B>>
where
    A: Copy + Spanning + 'a,
    P: Parser<'a, A, B>,
{
    ZeroOrMore::new(parser)
}

/// Consumes values from the input while the parser continues to return a
/// MatchStatus::Match.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'a', 'b'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
///   parcel::OneOrMore::new(expect_character('a')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::OneOrMore::new(expect_character('c')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
///   parcel::OneOrMore::new(expect_byte(0x00)).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::OneOrMore::new(expect_byte(0x02)).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct OneOrMore<P> {
    parser: P,
}

impl<P> OneOrMore<P> {
    pub fn new(parser: P) -> Self {
        Self { parser }
    }
}

impl<'a, P, A, B> Parser<'a, A, Vec<B>> for OneOrMore<P>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    fn parse(&self, mut input: A) -> ParseResult<'a, A, Vec<B>> {
        let mut span_acc: Vec<Span> = Vec::new();
        let mut result_acc: Vec<B> = Vec::new();

        while let Ok(MatchStatus::Match {
            span,
            remainder,
            inner,
        }) = self.parser.parse(input)
        {
            input = remainder;
            span_acc.push(span);
            result_acc.push(inner);
        }

        if !result_acc.is_empty() {
            let start = span_acc.first().unwrap().start;
            let end = span_acc.last().unwrap().end;

            Ok(MatchStatus::Match {
                span: start..end,
                remainder: input,
                inner: result_acc,
            })
        } else {
            Ok(MatchStatus::NoMatch(input))
        }
    }
}

/// Consumes values from the input while the parser continues to return a
/// MatchStatus::Match.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'a', 'b'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec!['a', 'a']}),
///   parcel::one_or_more(expect_character('a')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::one_or_more(expect_character('c')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
///   parcel::one_or_more(expect_byte(0x00)).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   parcel::one_or_more(expect_byte(0x02)).parse(&input)
/// );
/// ```
pub fn one_or_more<'a, P, A, B>(parser: P) -> impl Parser<'a, A, Vec<B>>
where
    A: Copy + 'a,
    P: Parser<'a, A, B>,
{
    OneOrMore::new(parser)
}

/// Provides optional matching of a value, returning `Parser<A, Option<B>>`.
/// For cases where the value is not present, a match with a `None` value is
/// returned. Otherwise a match with a `Some<B>` is returned.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: Some('a')}),
///   parcel::Optional::new(expect_character('a')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: None}),
///   parcel::Optional::new(expect_character('c')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..1, remainder: &input[1..], inner: None}),
///   parcel::AndThen::new(
///     expect_character('a'),
///     |_| parcel::Optional::new(expect_character('c'))
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: Some(0x00)}),
///   parcel::Optional::new(expect_byte(0x00)).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: None}),
///   parcel::Optional::new(expect_byte(0x02)).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 1..1, remainder: &input[1..], inner: None}),
///   parcel::AndThen::new(
///     expect_byte(0x00),
///     |_| parcel::Optional::new(expect_byte(0x02))
///   ).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct Optional<P> {
    parser: P,
}

impl<P> Optional<P> {
    pub fn new(parser: P) -> Self {
        Self { parser }
    }
}

impl<'a, P, A, B> Parser<'a, A, Option<B>> for Optional<P>
where
    A: Copy + Spanning + 'a,
    P: Parser<'a, A, B>,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, Option<B>> {
        match self.parser.parse(input) {
            Ok(MatchStatus::Match {
                span,
                remainder,
                inner,
            }) => Ok(MatchStatus::Match {
                span,
                remainder,
                inner: Some(inner),
            }),
            Ok(MatchStatus::NoMatch(last_input)) => {
                let span = input.start()..input.start();
                Ok(MatchStatus::Match {
                    span,
                    remainder: last_input,
                    inner: None,
                })
            }
            Err(e) => Err(e),
        }
    }
}

/// Provides optional matching of a value, returning `Parser<A, Option<B>>`.
/// For cases where the value is not present, a match with a `None` value is
/// returned. Otherwise a match with a `Some<B>` is returned.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: Some('a')}),
///   parcel::optional(expect_character('a')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: None}),
///   parcel::optional(expect_character('c')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: Some(0x00)}),
///   parcel::optional(expect_byte(0x00)).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..0, remainder: &input[0..], inner: None}),
///   parcel::optional(expect_byte(0x02)).parse(&input)
/// );
/// ```
pub fn optional<'a, P, A, B>(parser: P) -> impl Parser<'a, A, Option<B>>
where
    A: Copy + Spanning + 'a,
    P: Parser<'a, A, B>,
{
    Optional::new(parser)
}

// Applicatives

/// Join attempts to match `Parser<A, B>` and `Parser<A, C>` after which it merges
/// the results to `Parser<A, (B, C)>`.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: ('a', 'b')}),
///   parcel::Join::new(expect_character('a'), expect_character('b')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: (0x00, 0x01)}),
///   parcel::Join::new(expect_byte(0x00), expect_byte(0x01)).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct Join<P1, P2> {
    parser1: P1,
    parser2: P2,
}

impl<P1, P2> Join<P1, P2> {
    pub fn new(parser1: P1, parser2: P2) -> Self {
        Self { parser1, parser2 }
    }
}

impl<'a, P1, P2, A, B, C> Parser<'a, A, (B, C)> for Join<P1, P2>
where
    A: Copy + Borrow<A> + 'a,
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, C>,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, (B, C)> {
        self.parser1.parse(input).and_then(|p1_ms| match p1_ms {
            MatchStatus::NoMatch(rem) => Ok(MatchStatus::NoMatch(rem)),
            MatchStatus::Match {
                span: p1_span,
                remainder: p1_remainder,
                inner: p1_inner,
            } => self.parser2.parse(p1_remainder).map(|p2_ms| match p2_ms {
                MatchStatus::NoMatch(_) => MatchStatus::NoMatch(input),
                MatchStatus::Match {
                    span: p2_span,
                    remainder: p2_remainder,
                    inner: p2_inner,
                } => MatchStatus::Match {
                    span: p1_span.start..p2_span.end,
                    remainder: p2_remainder,
                    inner: (p1_inner, p2_inner),
                },
            }),
        })
    }
}

/// Join attempts to match `Parser<A, B>` and `Parser<A, C>` after which it merges
/// the results to `Parser<A, (B, C)>`.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: ('a', 'b')}),
///   parcel::join(expect_character('a'), expect_character('b')).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: (0x00, 0x01)}),
///   parcel::join(expect_byte(0x00), expect_byte(0x01)).parse(&input)
/// );
/// ```
pub fn join<'a, P1, P2, A, B, C>(parser1: P1, parser2: P2) -> impl Parser<'a, A, (B, C)>
where
    A: Copy + Borrow<A> + 'a,
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, C>,
{
    Join::new(parser1, parser2)
}

/// Left expects to take the results of join, returning a Parser<A, (B, C)>
/// and then extrapolates the left-hand value, returning a Parser<A, B>.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: 'a'}),
///   parcel::Left::new(
///       parcel::join(
///           expect_character('a'),
///           expect_character('b')
///       )
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: 0x00}),
///   parcel::Left::new(
///       parcel::join(
///           expect_byte(0x00),
///           expect_byte(0x01)
///       )
///   ).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct Left<P, A, B, C> {
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    parser: P,
}

impl<P, A, B, C> Left<P, A, B, C> {
    pub fn new(parser: P) -> Self {
        Self {
            a: PhantomData,
            b: PhantomData,
            c: PhantomData,
            parser,
        }
    }
}

impl<'a, P, A, B, C> Parser<'a, A, B> for Left<P, A, B, C>
where
    A: Copy + Borrow<A> + 'a,
    B: 'a,
    C: 'a,
    P: Parser<'a, A, (B, C)> + 'a,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, B> {
        self.parser.parse(input).map(|ms| match ms {
            MatchStatus::NoMatch(rem) => MatchStatus::NoMatch(rem),
            MatchStatus::Match {
                span,
                remainder,
                inner,
            } => MatchStatus::Match {
                span,
                remainder,
                inner: inner.0,
            },
        })
    }
}

/// Left expects to take the results of join, returning a Parser<A, (B, C)>
/// and then extrapolates the left-hand value, returning a Parser<A, B>.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: 'a'}),
///   parcel::left(
///       parcel::join(
///           expect_character('a'),
///           expect_character('b')
///       )
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: 0x00}),
///   parcel::left(
///       parcel::join(
///           expect_byte(0x00),
///           expect_byte(0x01)
///       )
///   ).parse(&input)
/// );
/// ```
pub fn left<'a, P, A, B, C>(parser: P) -> impl Parser<'a, A, B>
where
    A: Copy + Borrow<A> + 'a,
    B: 'a,
    C: 'a,
    P: Parser<'a, A, (B, C)> + 'a,
{
    Left::new(parser)
}

/// Right expects to take the results of join, returning a Parser<A, (B, C)>
/// and then extrapolates the value right-hand value, returning a Parser<A, C>.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: 'b'}),
///   parcel::Right::new(
///       parcel::join(
///           expect_character('a'),
///           expect_character('b')
///       )
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: 0x01}),
///   parcel::Right::new(
///       parcel::join(
///           expect_byte(0x00),
///           expect_byte(0x01)
///       )
///   ).parse(&input)
/// );
/// ```
#[derive(Debug)]
pub struct Right<P, A, B, C> {
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    parser: P,
}

impl<P, A, B, C> Right<P, A, B, C> {
    pub fn new(parser: P) -> Self {
        Self {
            a: PhantomData,
            b: PhantomData,
            c: PhantomData,
            parser,
        }
    }
}

impl<'a, P, A, B, C> Parser<'a, A, C> for Right<P, A, B, C>
where
    A: Copy + Borrow<A> + 'a,
    B: 'a,
    C: 'a,
    P: Parser<'a, A, (B, C)> + 'a,
{
    fn parse(&self, input: A) -> ParseResult<'a, A, C> {
        self.parser.parse(input).map(|ms| match ms {
            MatchStatus::NoMatch(rem) => MatchStatus::NoMatch(rem),
            MatchStatus::Match {
                span,
                remainder,
                inner,
            } => MatchStatus::Match {
                span,
                remainder,
                inner: inner.1,
            },
        })
    }
}

/// Right expects to take the results of join, returning a Parser<A, (B, C)>
/// and then extrapolates the value right-hand value, returning a Parser<A, C>.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: 'b'}),
///   parcel::right(
///       parcel::join(
///           expect_character('a'),
///           expect_character('b')
///       )
///   ).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: 0x01}),
///   parcel::right(
///       parcel::join(
///           expect_byte(0x00),
///           expect_byte(0x01)
///       )
///   ).parse(&input)
/// );
/// ```
pub fn right<'a, P, A, B, C>(parser: P) -> impl Parser<'a, A, C>
where
    A: Copy + Borrow<A> + 'a,
    B: 'a,
    C: 'a,
    P: Parser<'a, A, (B, C)> + 'a,
{
    Right::new(parser)
}
