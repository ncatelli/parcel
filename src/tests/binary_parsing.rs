use crate::parsers::byte::{any_byte, expect_byte};
use crate::prelude::v1::*;
use crate::{
    join, left, one_or_more, optional, predicate, right, take_n, take_until_n, zero_or_more,
    MatchStatus,
};

#[test]
fn parser_should_parse_byte_match() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 0x00))),
        expect_byte(0x00).parse(&input)
    );
}

#[test]
fn parser_can_map_a_result() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 0x00))),
        expect_byte(0x00).map(|result| result).parse(&input)
    );
}

#[test]
fn parser_should_skip_a_result() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[1..])),
        expect_byte(0x00).skip().parse(&input)
    );
}

#[test]
fn parser_should_not_skip_input_if_parser_does_not_match() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        expect_byte(0xFF).skip().parse(&input)
    );
}

#[test]
fn parser_can_match_with_or() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 0x00))),
        expect_byte(0x03).or(|| expect_byte(0x00)).parse(&input)
    );
}

#[test]
fn parser_can_match_with_one_of() {
    let input = vec![0x00, 0x01, 0x02];
    let parsers = vec![expect_byte(0x01), expect_byte(0x02), expect_byte(0x00)];
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
        expect_byte(0x00)
            .and_then(|_| expect_byte(0x01))
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
        take_until_n(expect_byte(0x00), 4).parse(&input)
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
        expect_byte(0x00).take_until_n(4).parse(&input)
    );
}

#[test]
fn take_until_n_will_match_only_up_to_specified_limit() {
    let input = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[3..], vec![0x00, 0x00, 0x00]))),
        expect_byte(0x00).take_until_n(3).parse(&input)
    );
}

#[test]
fn take_until_n_will_return_as_many_matches_as_possible() {
    let input = vec![0x00, 0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], vec![0x00, 0x00]))),
        expect_byte(0x00).take_until_n(3).parse(&input)
    );
}

#[test]
fn take_until_n_returns_a_no_match_on_no_match() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        expect_byte(0x03).take_until_n(2).parse(&input)
    );
}

#[test]
fn parser_can_match_with_take_n() {
    let input = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((
            &input[4..],
            vec![0x00, 0x00, 0x00, 0x00]
        ))),
        take_n(expect_byte(0x00), 4).parse(&input)
    );
}

#[test]
fn parser_can_match_with_boxed_take_n() {
    let input = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((
            &input[4..],
            vec![0x00, 0x00, 0x00, 0x00]
        ))),
        expect_byte(0x00).take_n(4).parse(&input)
    );
}

#[test]
fn take_n_will_match_only_up_to_specified_limit() {
    let input = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[3..], vec![0x00, 0x00, 0x00]))),
        expect_byte(0x00).take_n(3).parse(&input)
    );
}

#[test]
fn take_n_will_not_match_if_unable_to_match_n_results() {
    let input = vec![0x00, 0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        expect_byte(0x00).take_n(3).parse(&input)
    );
}

#[test]
fn take_n_returns_a_no_match_on_no_match() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        expect_byte(0x03).take_n(2).parse(&input)
    );
}

#[test]
fn parser_joins_values_on_match_with_join_combinator() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], (0x00, 0x01)))),
        join(expect_byte(0x00), expect_byte(0x01)).parse(&input)
    );
}

#[test]
fn applicatives_can_retrieve_each_independent_value() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], 0x00))),
        left(join(expect_byte(0x00), expect_byte(0x01))).parse(&input)
    );

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], 0x01))),
        right(join(expect_byte(0x00), expect_byte(0x01))).parse(&input)
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
        one_or_more(expect_byte(0x01)).parse(&input)
    );
}

#[test]
fn zero_or_more_returns_match_when_matches_exist() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], vec![0x00]))),
        zero_or_more(expect_byte(0x00)).parse(&input)
    );
}

#[test]
fn zero_or_more_returns_match_when_no_matches_exist() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[0..], Vec::new()))),
        zero_or_more(expect_byte(0x01)).parse(&input)
    );
}

#[test]
fn optional_matches_on_zero() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[0..], None))),
        optional(expect_byte(0x01)).parse(&input)
    );
}

#[test]
fn optional_matches_on_one() {
    let input = vec![0x00, 0x01, 0x02];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], Some(0x00)))),
        optional(expect_byte(0x00)).parse(&input)
    );
}
