use crate::prelude::v1::*;

pub fn match_byte<'a>(expected: u8) -> impl Parser<'a, &'a [u8], u8> {
    move |input: &'a [u8]| match input.get(0) {
        Some(&next) if next == expected => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

pub fn any_byte<'a>() -> impl Parser<'a, &'a [u8], u8> {
    move |input: &'a [u8]| match input.get(0) {
        Some(&next) => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}
