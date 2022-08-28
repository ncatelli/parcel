extern crate alloc;
use alloc::vec::Vec;

use crate::prelude::v1::*;

/// Matches a single provided `u8`, returning match if the next `u8` in the
/// array matches the expected value. Otherwise, a `NoMatch` is returned.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01, 0x02]
///     .into_iter()
///     .enumerate()
///     .collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
///   expect_byte(0x00).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01, 0x02]
///     .into_iter()
///     .enumerate()
///     .collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   expect_byte(0x02).parse(&input)
/// );
/// ```
pub fn expect_byte<'a>(expected: u8) -> impl Parser<'a, &'a [(usize, u8)], u8> {
    move |input: &'a [(usize, u8)]| match input.first() {
        Some(&(pos, next)) if next == expected => Ok(MatchStatus::Match {
            span: pos..pos + 1,
            remainder: &input[1..],
            inner: next,
        }),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

/// Matches a sequence of bytes, returning match if the next sequence in the
/// input matches the expected sequence exactly.  Otherwise, a `NoMatch` is
/// returned.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_bytes;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01, 0x02]
///     .into_iter()
///     .enumerate()
///     .collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..2, remainder: &input[2..], inner: vec![0x00, 0x00]}),
///   expect_bytes(&[0x00, 0x00]).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::expect_bytes;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01, 0x02]
///     .into_iter()
///     .enumerate()
///     .collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   expect_bytes(&[0x02]).parse(&input)
/// );
/// ```
pub fn expect_bytes<'a>(expected: &'static [u8]) -> impl Parser<'a, &'a [(usize, u8)], Vec<u8>> {
    move |input: &'a [(usize, u8)]| {
        let preparse_input = input;
        let expected_len = expected.len();
        let start_pos = preparse_input.first().map(|elem| elem.0).unwrap_or(0);
        let expected_end = start_pos + expected_len;
        let next: Vec<u8> = input
            .iter()
            .take(expected_len)
            .copied()
            .map(|i| i.1)
            .collect();
        if next == expected {
            Ok(MatchStatus::Match {
                span: start_pos..expected_end,
                remainder: &input[expected_len..],
                inner: next,
            })
        } else {
            Ok(MatchStatus::NoMatch(preparse_input))
        }
    }
}

/// Matches any single `u8` byte regardless of value. Returning a `Match` result
/// containing the next `u8` byte in the stream if there is one available to
/// consume.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::any_byte;
/// let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01, 0x02]
///     .into_iter()
///     .enumerate()
///     .collect();
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match{span: 0..1, remainder: &input[1..], inner: 0x00}),
///   any_byte().parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::byte::any_byte;
/// let input = vec![];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   any_byte().parse(&input[0..])
/// );
/// ```
pub fn any_byte<'a>() -> impl Parser<'a, &'a [(usize, u8)], u8> {
    move |input: &'a [(usize, u8)]| match input.first() {
        Some(&(pos, next)) => Ok(MatchStatus::Match {
            span: pos..pos + 1,
            remainder: &input[1..],
            inner: next,
        }),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}
