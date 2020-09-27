use crate::prelude::v1::*;
/// Matches a single provided character, returning match if the next character
/// in the array matches the expected value. Otherwise, a `NoMatch` is
/// returned.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], 'a'))),
///   expect_character('a').parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_character;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   expect_character('b').parse(&input)
/// );
/// ```
pub fn expect_character<'a>(expected: char) -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next == expected => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

/// Matches any single character regardless of value. Returning a `Match`
/// result containing the next character in the stream if there is one
/// available to consume.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::any_character;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], 'a'))),
///   any_character().parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::any_character;
/// let input = vec![];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   any_character().parse(&input[0..])
/// );
/// ```
pub fn any_character<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

/// Matches a single provided &str, returning match if the next characters in
/// the array matches the expected str. Otherwise, a `NoMatch` is returned.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_str;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[2..], "ab".to_string()))),
///   expect_str("ab").parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::expect_str;
/// let input = vec!['a', 'b', 'c'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   expect_str("b").parse(&input)
/// );
/// ```
pub fn expect_str<'a>(expected: &'static str) -> impl Parser<'a, &'a [char], String> {
    move |input: &'a [char]| {
        let preparse_input = input;
        let expected_len = expected.len();
        let next: String = input.iter().take(expected_len).collect();
        if &next == expected {
            Ok(MatchStatus::Match((&input[expected_len..], next)))
        } else {
            Ok(MatchStatus::NoMatch(preparse_input))
        }
    }
}
/// Matches any single whitespace char, excluding newlines.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::non_newline_whitespace;
/// let input = vec![' ', '\t', 'a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[2..], '\t'))),
///   non_newline_whitespace().and_then(|_| non_newline_whitespace()).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::non_newline_whitespace;
/// let input = vec!['\n'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   non_newline_whitespace().parse(&input)
/// );
/// ```
pub fn non_newline_whitespace<'a>() -> impl Parser<'a, &'a [char], char> {
    expect_character(' ').or(|| expect_character('\t'))
}

/// Matches any single space char.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::space;
/// let input = vec![' ', 'a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], ' '))),
///   space().parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::space;
/// let input = vec!['a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   space().parse(&input)
/// );
/// ```
pub fn space<'a>() -> impl Parser<'a, &'a [char], char> {
    expect_character(' ')
}

/// Matches any single tab char.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::tab;
/// let input = vec!['\t', 'a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], '\t'))),
///   tab().parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::tab;
/// let input = vec!['a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   tab().parse(&input)
/// );
/// ```
pub fn tab<'a>() -> impl Parser<'a, &'a [char], char> {
    expect_character('\t')
}

/// Matches any single whitespace char including newlines that matches the
/// whitespace definitions defined in the
/// [Unicode Character Database](https://www.unicode.org/reports/tr44/).
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::whitespace;
/// let input = vec![' ', '\n', '\t', 'a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[3..], '\t'))),
///   whitespace()
///     .and_then(|_| whitespace())
///     .and_then(|_| whitespace())
///     .parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::whitespace;
/// let input = vec!['a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   whitespace().parse(&input)
/// );
/// ```
pub fn whitespace<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next.is_whitespace() => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

/// Matches if the end of the input array/file has been reached. Returning a
/// `Match` containing a ' ' character as a placeholder.
///
/// Special care should be taken when this is used with conjunction with other
/// parsers that may yield a similar match case.
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::eof;
/// let input = vec![];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[0..], ' '))),
///   eof().parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::eof;
/// let input = vec!['a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   eof().parse(&input)
/// );
/// ```
pub fn eof<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(_) => Ok(MatchStatus::NoMatch(input)),
        None => Ok(MatchStatus::Match((&input[0..], ' '))),
    }
}

/// Matches any single newline character
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::newline;
/// let input = vec!['\n'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], '\n'))),
///   newline().parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::newline;
/// let input = vec!['a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   newline().parse(&input)
/// );
/// ```
pub fn newline<'a>() -> impl Parser<'a, &'a [char], char> {
    expect_character('\n')
}

/// Matches any single alphabetic char as described in the
/// [Unicode Character Database](https://www.unicode.org/reports/tr44/).
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::alphabetic;
/// let input = vec!['a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], 'a'))),
///   alphabetic().parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::alphabetic;
/// let input = vec!['\n'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   alphabetic().parse(&input)
/// );
/// ```
pub fn alphabetic<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next.is_alphabetic() => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

/// Matches any single digit character, taking a radix for the base encoding.
///
/// - hex: 16
/// - dec: 10
/// - oct: 8
/// - bin: 2
///
/// # Examples
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::digit;
/// let input = vec!['a'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], 'a'))),
///   digit(16).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::digit;
/// let input = vec!['9'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], '9'))),
///   digit(10).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::digit;
/// let input = vec!['7'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], '7'))),
///   digit(8).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::digit;
/// let input = vec!['1'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::Match((&input[1..], '1'))),
///   digit(2).parse(&input)
/// );
/// ```
///
/// ```
/// use parcel::prelude::v1::*;
/// use parcel::parsers::character::digit;
/// let input = vec!['\n'];
/// assert_eq!(
///   Ok(parcel::MatchStatus::NoMatch(&input[0..])),
///   digit(16).parse(&input)
/// );
/// ```
pub fn digit<'a>(radix: u32) -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next.is_digit(radix) => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}
