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
    move |input: &'a [(usize, u8)]| match input.get(0) {
        Some(&(pos, next)) if next == expected => Ok(MatchStatus::Match {
            span: pos..pos + 1,
            remainder: &input[1..],
            inner: next,
        }),
        _ => Ok(MatchStatus::NoMatch(input)),
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
    move |input: &'a [(usize, u8)]| match input.get(0) {
        Some(&(pos, next)) => Ok(MatchStatus::Match {
            span: pos..pos + 1,
            remainder: &input[1..],
            inner: next,
        }),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}
