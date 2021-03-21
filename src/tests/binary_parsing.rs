use crate::parsers::byte::{any_byte, expect_byte};
use crate::prelude::v1::*;
use crate::{predicate, take_until_n};

#[test]
fn parser_should_parse_byte_match() {
    let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: Some(0..1),
            match_status: MatchStatus::Match((&input[1..], 0x00))
        }),
        expect_byte(0x00).parse(&input)
    );
}

#[test]
fn parser_should_not_skip_input_if_parser_does_not_match() {
    let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: None,
            match_status: MatchStatus::NoMatch(&input[0..])
        }),
        expect_byte(0xFF).skip().parse(&input)
    );
}

#[test]
fn parser_can_match_with_take_until_n() {
    let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02]
        .into_iter()
        .enumerate()
        .collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: Some(0..4),
            match_status: MatchStatus::Match((&input[4..], vec![0x00, 0x00, 0x00, 0x00]))
        }),
        take_until_n(expect_byte(0x00), 4).parse(&input)
    );
}

#[test]
fn take_until_n_will_match_only_up_to_specified_limit() {
    let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02]
        .into_iter()
        .enumerate()
        .collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: Some(0..3),
            match_status: MatchStatus::Match((&input[3..], vec![0x00, 0x00, 0x00]))
        }),
        expect_byte(0x00).take_until_n(3).parse(&input)
    );
}

#[test]
fn take_until_n_will_return_as_many_matches_as_possible() {
    let input: Vec<(usize, u8)> = vec![0x00, 0x00, 0x01, 0x02]
        .into_iter()
        .enumerate()
        .collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: Some(0..2),
            match_status: MatchStatus::Match((&input[2..], vec![0x00, 0x00]))
        }),
        expect_byte(0x00).take_until_n(3).parse(&input)
    );
}

#[test]
fn take_until_n_returns_a_no_match_on_no_match() {
    let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: None,
            match_status: MatchStatus::NoMatch(&input[0..])
        }),
        expect_byte(0x03).take_until_n(2).parse(&input)
    );
}

#[test]
fn take_n_returns_a_no_match_on_no_match() {
    let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: None,
            match_status: MatchStatus::NoMatch(&input[0..])
        }),
        expect_byte(0x03).take_n(2).parse(&input)
    );
}

#[test]
fn predicate_should_not_match_if_case_is_true() {
    let input: Vec<(usize, u8)> = vec![0x00, 0x01, 0x02].into_iter().enumerate().collect();

    assert_eq!(
        Ok(SpannedMatchStatus {
            span: None,
            match_status: MatchStatus::NoMatch(&input[0..])
        }),
        predicate(any_byte(), |&c| c != 0x00).parse(&input)
    );
}
