use crate::parsers::character::{any_character, expect_character};
use crate::prelude::v1::*;
use crate::{
    join, left, one_or_more, optional, predicate, right, take_n, take_until_n, zero_or_more,
    MatchStatus,
};

#[test]
fn parser_should_parse_char_match() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'))),
        expect_character('a').parse(&input[0..])
    );
}

#[test]
fn parser_can_map_a_result() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'.to_string()))),
        expect_character('a')
            .map(|result| { result.to_string() })
            .parse(&input[0..])
    );
}

#[test]
fn parser_should_skip_a_result() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[1..])),
        expect_character('a').skip().parse(&input[0..])
    );
}

#[test]
fn parser_should_not_skip_input_if_parser_does_not_match() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        expect_character('x').skip().parse(&input[0..])
    );
}

#[test]
fn parser_can_match_with_one_of() {
    let input = vec!['a', 'b', 'c'];
    let parsers = vec![
        expect_character('b'),
        expect_character('c'),
        expect_character('a'),
    ];
    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'))),
        crate::one_of(parsers).parse(&input[0..])
    );
}

#[test]
fn parser_can_match_with_peek_next() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'))),
        expect_character('a')
            .peek_next(expect_character('b'))
            .parse(&input[0..])
    );
}

#[test]
fn parser_can_match_with_take_until_n() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[4..], vec!['a', 'a', 'a', 'a']))),
        take_until_n(expect_character('a'), 4).parse(&input[0..])
    );
}

#[test]
fn parser_can_match_with_boxed_take_until_n() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[4..], vec!['a', 'a', 'a', 'a']))),
        expect_character('a').take_until_n(4).parse(&input[0..])
    );
}

#[test]
fn take_until_n_will_match_only_up_to_specified_limit() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[3..], vec!['a', 'a', 'a']))),
        expect_character('a').take_until_n(3).parse(&input[0..])
    );
}

#[test]
fn take_until_n_will_return_as_many_matches_as_possible() {
    let input = vec!['a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], vec!['a', 'a']))),
        expect_character('a').take_until_n(3).parse(&input[0..])
    );
}

#[test]
fn take_until_n_returns_a_no_match_on_no_match() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        expect_character('d').take_until_n(2).parse(&input[0..])
    );
}

#[test]
fn parser_can_match_with_take_n() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[4..], vec!['a', 'a', 'a', 'a']))),
        take_n(expect_character('a'), 4).parse(&input[0..])
    );
}

#[test]
fn parser_can_match_with_boxed_take_n() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[4..], vec!['a', 'a', 'a', 'a']))),
        expect_character('a').take_n(4).parse(&input[0..])
    );
}

#[test]
fn take_n_will_match_only_up_to_specified_limit() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[3..], vec!['a', 'a', 'a']))),
        expect_character('a').take_n(3).parse(&input[0..])
    );
}

#[test]
fn take_n_will_not_match_if_unable_to_match_n_results() {
    let input = vec!['a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        expect_character('a').take_n(3).parse(&input[0..])
    );
}

#[test]
fn take_n_returns_a_no_match_on_no_match() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        expect_character('d').take_n(2).parse(&input[0..])
    );
}

#[test]
fn parser_joins_values_on_match_with_join_combinator() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], ('a', 'b')))),
        join(expect_character('a'), expect_character('b')).parse(&input[0..])
    );
}

#[test]
fn applicatives_can_retrieve_each_independent_value() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], 'a'))),
        left(join(expect_character('a'), expect_character('b'))).parse(&input[0..])
    );

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], 'b'))),
        right(join(expect_character('a'), expect_character('b'))).parse(&input[0..])
    );
}

#[test]
fn predicate_should_match_if_case_fail() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'))),
        predicate(any_character(), |&c| c != 'c').parse(&input[0..])
    );
}

#[test]
fn predicate_should_not_match_if_case_is_true() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        predicate(any_character(), |&c| c != 'a').parse(&input[0..])
    );
}

#[test]
fn predicate_should_match_until_case_fails() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], vec!['a', 'b']))),
        zero_or_more(predicate(any_character(), |&c| c != 'c')).parse(&input[0..])
    );
}

#[test]
fn one_or_more_returns_no_match_when_no_matches_exist() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        one_or_more(expect_character('b')).parse(&input[0..])
    );
}

#[test]
fn zero_or_more_returns_match_when_matches_exist() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], vec!['a']))),
        zero_or_more(expect_character('a')).parse(&input[0..])
    );
}

#[test]
fn zero_or_more_returns_match_when_no_matches_exist() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[0..], Vec::new()))),
        zero_or_more(expect_character('b')).parse(&input[0..])
    );
}

#[test]
fn optional_matches_on_zero() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[0..], None))),
        optional(expect_character('b')).parse(&input[0..])
    );
}

#[test]
fn optional_matches_on_one() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], Some('a')))),
        optional(expect_character('a')).parse(&input[0..])
    );
}
