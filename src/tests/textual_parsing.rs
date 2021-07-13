use crate::parsers::character::{any_character, expect_character};
use crate::prelude::v1::*;
use crate::{predicate, take_until_n};

macro_rules! assert_parser {
    {should parse $input:literal using $parser:expr => $output:expr} => {
        let input_vec: Vec<(usize, char)> = $input.chars().enumerate.collect();
        let input_len = input_vec.len();

        assert_eq!(
            Ok(MatchStatus::Match {
                span: 0..input_len,
                remainder: &input_vec[input_len..],
                inner: $output
            }),
            $parser.parse(&input_vec[..])
        );
    };
    {should parse $elements:literal elements from $input:literal using $parser:expr => $output:expr} => {
        let input_vec: Vec<(usize, char)> = $input.chars().enumerate().collect();

        assert_eq!(
            Ok(MatchStatus::Match {
                span: 0..$elements,
                remainder: &input_vec[$elements..],
                inner: $output
            }),
            $parser.parse(&input_vec[..])
        );
    };
    {should parse $elements:literal element from $input:literal using $parser:expr => $output:expr} => {
        assert_parser!(should parse $elements elements from $input using $parser => $output);
    };

    // No Match
    {should not parse $input:literal using $parser:expr} => {
        let input_vec: Vec<(usize, char)> = $input.chars().enumerate().collect();

        assert_eq!(
            Ok(MatchStatus::NoMatch(&input_vec[..])),
            $parser.parse(&input_vec[..])
        );
    };
}

#[test]
fn parser_should_parse_char_match() {
    assert_parser!(should parse 1 element from "abc" using expect_character('a') => 'a');
}

#[test]
fn parser_should_not_skip_input_if_parser_does_not_match() {
    assert_parser!(should not parse "abc" using expect_character('x'));
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
        Ok(MatchStatus::Match {
            span: 0..1,
            remainder: &input[1..],
            inner: 'a'
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
        Ok(MatchStatus::Match {
            span: 0..4,
            remainder: &input[4..],
            inner: vec!['a', 'a', 'a', 'a']
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
        Ok(MatchStatus::Match {
            span: 0..3,
            remainder: &input[3..],
            inner: vec!['a', 'a', 'a']
        }),
        expect_character('a').take_until_n(3).parse(&input[0..])
    );
}

#[test]
fn take_until_n_will_return_as_many_matches_as_possible() {
    let input: Vec<(usize, char)> = vec!['a', 'a', 'b', 'c'].into_iter().enumerate().collect();

    assert_eq!(
        Ok(MatchStatus::Match {
            span: 0..2,
            remainder: &input[2..],
            inner: vec!['a', 'a']
        }),
        expect_character('a').take_until_n(3).parse(&input[0..])
    );
}

#[test]
fn take_until_n_returns_a_no_match_on_no_match() {
    let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
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
        Ok(MatchStatus::Match {
            span: 0..3,
            remainder: &input[3..],
            inner: vec!['a', 'a', 'a']
        }),
        expect_character('a').take_n(3).parse(&input[0..])
    );
}

#[test]
fn take_n_returns_a_no_match_on_no_match() {
    let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        expect_character('d').take_n(2).parse(&input[0..])
    );
}

#[test]
fn predicate_should_not_match_if_case_is_true() {
    let input: Vec<(usize, char)> = vec!['a', 'b', 'c'].into_iter().enumerate().collect();
    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        predicate(any_character(), |&c| c != 'a').parse(&input[0..])
    );
}
