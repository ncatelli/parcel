use crate::prelude::v1::*;
use crate::{join, one_or_more, optional, right, take_n};

macro_rules! char_vec_to_u16_from_radix {
    ($chars:expr, $radix:expr) => {
        u16::from_le(u16::from_str_radix(&$chars.into_iter().collect::<String>(), $radix).unwrap())
    };
}

macro_rules! char_vec_to_u8_from_radix {
    ($chars:expr, $radix:expr) => {
        u8::from_le(u8::from_str_radix(&$chars.into_iter().collect::<String>(), $radix).unwrap())
    };
}

macro_rules! char_vec_to_i8_from_radix {
    ($chars:expr, $radix:expr) => {
        i8::from_le(i8::from_str_radix(&$chars.into_iter().collect::<String>(), $radix).unwrap())
    };
}

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

#[derive(Clone, Copy, PartialEq)]
enum Sign {
    Positive,
    Negative,
}

impl PartialEq<char> for Sign {
    fn eq(&self, other: &char) -> bool {
        match self {
            &Self::Positive if *other == '+' => true,
            &Self::Negative if *other == '-' => true,
            _ => false,
        }
    }
}

pub fn non_newline_whitespace<'a>() -> impl Parser<'a, &'a [char], char> {
    expect_character(' ').or(|| expect_character('\t'))
}

pub fn space<'a>() -> impl Parser<'a, &'a [char], char> {
    expect_character(' ')
}

pub fn tab<'a>() -> impl Parser<'a, &'a [char], char> {
    expect_character('\t')
}

pub fn whitespace<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next.is_whitespace() => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

pub fn alphabetic<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next.is_alphabetic() => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

pub fn eof<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(_) => Ok(MatchStatus::NoMatch(input)),
        None => Ok(MatchStatus::Match((&input[0..], ' '))),
    }
}

pub fn newline<'a>() -> impl Parser<'a, &'a [char], char> {
    expect_character('\n')
}

pub fn character<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if !next.is_whitespace() => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

pub fn unsigned16<'a>() -> impl Parser<'a, &'a [char], u16> {
    hex_u16().or(|| binary_u16()).or(|| dec_u16())
}

pub fn unsigned8<'a>() -> impl Parser<'a, &'a [char], u8> {
    hex_u8().or(|| binary_u8()).or(|| dec_u8())
}

pub fn signed8<'a>() -> impl Parser<'a, &'a [char], i8> {
    hex_i8().or(|| binary_i8()).or(|| dec_i8())
}

fn sign<'a>() -> impl Parser<'a, &'a [char], Sign> {
    expect_character('+')
        .or(|| expect_character('-'))
        .map(|c| match c {
            '-' => Sign::Negative,
            _ => Sign::Positive,
        })
}

fn hex_u16<'a>() -> impl Parser<'a, &'a [char], u16> {
    right(join(expect_character('$'), hex_bytes(2))).map(|hex| char_vec_to_u16_from_radix!(hex, 16))
}

fn hex_u8<'a>() -> impl Parser<'a, &'a [char], u8> {
    right(join(expect_character('$'), hex_bytes(1))).map(|hex| char_vec_to_u8_from_radix!(hex, 16))
}

fn hex_i8<'a>() -> impl Parser<'a, &'a [char], i8> {
    right(join(expect_character('$'), hex_bytes(1))).map(|hex| char_vec_to_i8_from_radix!(hex, 16))
}

pub fn hex_bytes<'a>(bytes: usize) -> impl Parser<'a, &'a [char], Vec<char>> {
    take_n(hex_digit(), bytes * 2)
}

pub fn hex_digit<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next.is_digit(16) => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

fn binary_u16<'a>() -> impl Parser<'a, &'a [char], u16> {
    right(join(expect_character('%'), binary_bytes(2)))
        .map(|bin| char_vec_to_u16_from_radix!(bin, 2))
}

fn binary_u8<'a>() -> impl Parser<'a, &'a [char], u8> {
    right(join(expect_character('%'), binary_bytes(1)))
        .map(|bin| char_vec_to_u8_from_radix!(bin, 2))
}

fn binary_i8<'a>() -> impl Parser<'a, &'a [char], i8> {
    right(join(expect_character('%'), binary_bytes(1)))
        .map(|bin| char_vec_to_i8_from_radix!(bin, 2))
}

pub fn binary_bytes<'a>(bytes: usize) -> impl Parser<'a, &'a [char], Vec<char>> {
    take_n(binary(), bytes * 8)
}

pub fn binary<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next.is_digit(2) => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

fn dec_u16<'a>() -> impl Parser<'a, &'a [char], u16> {
    move |input: &'a [char]| {
        let preparsed_input = input;
        let res = one_or_more(decimal())
            .map(|digits| {
                let vd: String = digits.into_iter().collect();
                u16::from_str_radix(&vd, 10)
            })
            .parse(input);

        match res {
            Ok(MatchStatus::Match((rem, Ok(u)))) => Ok(MatchStatus::Match((rem, u))),
            Ok(MatchStatus::Match((_, Err(_)))) => Ok(MatchStatus::NoMatch(preparsed_input)),
            Ok(MatchStatus::NoMatch(rem)) => Ok(MatchStatus::NoMatch(rem)),
            Err(e) => Err(e),
        }
    }
}

fn dec_u8<'a>() -> impl Parser<'a, &'a [char], u8> {
    move |input: &'a [char]| {
        let preparsed_input = input;
        let res = one_or_more(decimal())
            .map(|digits| {
                let vd: String = digits.into_iter().collect();
                u8::from_str_radix(&vd, 10)
            })
            .parse(input);

        match res {
            Ok(MatchStatus::Match((rem, Ok(u)))) => Ok(MatchStatus::Match((rem, u))),
            Ok(MatchStatus::Match((_, Err(_)))) => Ok(MatchStatus::NoMatch(preparsed_input)),
            Ok(MatchStatus::NoMatch(rem)) => Ok(MatchStatus::NoMatch(rem)),
            Err(e) => Err(e),
        }
    }
}

fn dec_i8<'a>() -> impl Parser<'a, &'a [char], i8> {
    move |input: &'a [char]| {
        let preparsed_input = input;
        let res = join(optional(sign()), one_or_more(decimal()))
            .map(|(sign, digits)| {
                let pos_or_neg = match sign {
                    Some(Sign::Negative) => '-',
                    _ => '+',
                };

                let vd: String = vec![pos_or_neg]
                    .into_iter()
                    .chain(digits.into_iter())
                    .collect();
                i8::from_str_radix(&vd, 10)
            })
            .parse(input);

        match res {
            Ok(MatchStatus::Match((rem, Ok(u)))) => Ok(MatchStatus::Match((rem, u))),
            Ok(MatchStatus::Match((_, Err(_)))) => Ok(MatchStatus::NoMatch(preparsed_input)),
            Ok(MatchStatus::NoMatch(rem)) => Ok(MatchStatus::NoMatch(rem)),
            Err(e) => Err(e),
        }
    }
}

#[allow(dead_code)]
pub fn decimal<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next.is_digit(10) => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}
