use crate::prelude::v1::*;
use crate::{
    join, left, one_or_more, optional, predicate, right, take_until_n, zero_or_more, MatchStatus,
};

fn match_byte<'a>(expected: u8) -> impl Parser<'a, &'a [u8], u8> {
    move |input: &'a [u8]| match input.get(0) {
        Some(&next) if next == expected => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

fn any_byte<'a>() -> impl Parser<'a, &'a [u8], u8> {
    move |input: &'a [u8]| match input.get(0) {
        Some(&next) => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

#[test]
fn parser_should_parse_byte_match() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 0x00))),
        match_byte(0x00).parse(&input)
    );
}

#[test]
fn parser_can_map_a_result() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 0x00))),
        match_byte(0x00).map(|result| result).parse(&input)
    );
}

#[test]
fn parser_should_skip_a_result() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[1..])),
        match_byte(0x00).skip().parse(&input)
    );
}

#[test]
fn parser_should_not_skip_input_if_parser_does_not_match() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        match_byte(0xFF).skip().parse(&input)
    );
}

#[test]
fn parser_can_match_with_or() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 0x00))),
        match_byte(0x03).or(|| match_byte(0x00)).parse(&input)
    );
}

#[test]
fn parser_can_match_with_one_of() {
    let input = vec![0x00, 0x01, 0x02];
    let parsers = vec![match_byte(0x01), match_byte(0x02), match_byte(0x00)];
    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 0x00))),
        crate::one_of(parsers).parse(&input)
    );
}

#[test]
fn parser_can_match_with_and_then() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], 0x01))),
        match_byte(0x00)
            .and_then(|_| match_byte(0x01))
            .parse(&input)
    );
}

#[test]
fn parser_can_match_with_take_until_n() {
    let input = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((
            &input[4..],
            vec![0x00, 0x00, 0x00, 0x00]
        ))),
        take_until_n(match_byte(0x00), 4).parse(&input)
    );
}

#[test]
fn parser_can_match_with_boxed_take_until_n() {
    let input = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((
            &input[4..],
            vec![0x00, 0x00, 0x00, 0x00]
        ))),
        match_byte(0x00).take_until_n(4).parse(&input)
    );
}

#[test]
fn take_until_n_will_match_only_up_to_specified_limit() {
    let input = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[3..], vec![0x00, 0x00, 0x00]))),
        match_byte(0x00).take_until_n(3).parse(&input)
    );
}

#[test]
fn take_until_n_will_return_as_many_matches_as_possible() {
    let input = vec![0x00, 0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], vec![0x00, 0x00]))),
        match_byte(0x00).take_until_n(3).parse(&input)
    );
}

#[test]
fn take_until_n_returns_a_no_match_on_no_match() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        match_byte(0x03).take_until_n(2).parse(&input)
    );
}

#[test]
fn parser_joins_values_on_match_with_join_combinator() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], (0x00, 0x01)))),
        join(match_byte(0x00), match_byte(0x01)).parse(&input)
    );
}

#[test]
fn applicatives_can_retrieve_each_independent_value() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], 0x00))),
        left(join(match_byte(0x00), match_byte(0x01))).parse(&input)
    );

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], 0x01))),
        right(join(match_byte(0x00), match_byte(0x01))).parse(&input)
    );
}

#[test]
fn predicate_should_match_if_case_fail() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 0x00))),
        predicate(any_byte(), |&b| b != 0x02).parse(&input)
    );
}

#[test]
fn predicate_should_not_match_if_case_is_true() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        predicate(any_byte(), |&c| c != 0x00).parse(&input)
    );
}

#[test]
fn predicate_should_match_until_case_fails() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], vec![0x00, 0x01]))),
        zero_or_more(predicate(any_byte(), |&c| c != 0x02)).parse(&input)
    );
}

#[test]
fn one_or_more_returns_no_match_when_no_matches_exist() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        one_or_more(match_byte(0x01)).parse(&input)
    );
}

#[test]
fn zero_or_more_returns_match_when_matches_exist() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], vec![0x00]))),
        zero_or_more(match_byte(0x00)).parse(&input)
    );
}

#[test]
fn zero_or_more_returns_match_when_no_matches_exist() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[0..], Vec::new()))),
        zero_or_more(match_byte(0x01)).parse(&input)
    );
}

#[test]
fn optional_matches_on_zero() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[0..], None))),
        optional(match_byte(0x01)).parse(&input)
    );
}

#[test]
fn optional_matches_on_one() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], Some(0x00)))),
        optional(match_byte(0x00)).parse(&input)
    );
}
