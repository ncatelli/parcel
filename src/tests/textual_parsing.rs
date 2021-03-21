use crate::parsers::character::{any_character, expect_character};
use crate::prelude::v1::*;
use crate::{predicate, take_until_n};

#[test]
fn parser_should_parse_char_match() {
    let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: Some(0..1),
            match_status: MatchStatus::Match((&input[1..], 'a'))
        }),
        expect_character('a').parse(&input[0..])
    );
}

#[test]
fn parser_should_not_skip_input_if_parser_does_not_match() {
    let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: None,
            match_status: MatchStatus::NoMatch(&input[0..])
        }),
        expect_character('x').skip().parse(&input[0..])
    );
}

#[test]
fn parser_can_match_with_one_of() {
    let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    let parsers = vec![
        expect_character('b'),
        expect_character('c'),
        expect_character('a'),
    ];

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: Some(0..1),
            match_status: MatchStatus::Match((&input[1..], 'a'))
        }),
        crate::one_of(parsers).parse(&input[0..])
    );
}

#[test]
fn parser_can_match_with_take_until_n() {
    let input: Vec<(usize, char)> = vec!['a', 'a', 'a', 'a', 'b', 'c']
        .into_iter()
        .enumerate()
        .collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: Some(0..4),
            match_status: MatchStatus::Match((&input[4..], vec!['a', 'a', 'a', 'a']))
        }),
        take_until_n(expect_character('a'), 4).parse(&input[0..])
    );
}

#[test]
fn take_until_n_will_match_only_up_to_specified_limit() {
    let input: Vec<(usize, char)> = vec!['a', 'a', 'a', 'a', 'b', 'c']
        .into_iter()
        .enumerate()
        .collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: Some(0..3),
            match_status: MatchStatus::Match((&input[3..], vec!['a', 'a', 'a']))
        }),
        expect_character('a').take_until_n(3).parse(&input[0..])
    );
}

#[test]
fn take_until_n_will_return_as_many_matches_as_possible() {
    let input: Vec<(usize, char)> = vec!['a', 'a', 'b', 'c'].into_iter().enumerate().collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: Some(0..2),
            match_status: MatchStatus::Match((&input[2..], vec!['a', 'a']))
        }),
        expect_character('a').take_until_n(3).parse(&input[0..])
    );
}

#[test]
fn take_until_n_returns_a_no_match_on_no_match() {
    let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: None,
            match_status: MatchStatus::NoMatch(&input[0..])
        }),
        expect_character('d').take_until_n(2).parse(&input[0..])
    );
}

#[test]
fn take_n_will_match_only_up_to_specified_limit() {
    let input: Vec<(usize, char)> = vec!['a', 'a', 'a', 'a', 'b', 'c']
        .into_iter()
        .enumerate()
        .collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: Some(0..3),
            match_status: MatchStatus::Match((&input[3..], vec!['a', 'a', 'a']))
        }),
        expect_character('a').take_n(3).parse(&input[0..])
    );
}

#[test]
fn take_n_returns_a_no_match_on_no_match() {
    let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: None,
            match_status: MatchStatus::NoMatch(&input[0..])
        }),
        expect_character('d').take_n(2).parse(&input[0..])
    );
}

#[test]
fn predicate_should_not_match_if_case_is_true() {
    let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    assert_eq!(
        Ok(SpannedMatchStatus {
            span: None,
            match_status: MatchStatus::NoMatch(&input[0..])
        }),
        predicate(any_character(), |&c| c != 'a').parse(&input[0..])
    );
}
