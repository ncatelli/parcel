use crate::parsers::character::{any_character, expect_character};
use crate::prelude::v1::*;

macro_rules! assert_parser {
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
    let parsers = vec![
        expect_character('b'),
        expect_character('c'),
        expect_character('a'),
    ];
    assert_parser!(should parse 1 element from "abc" using crate::one_of(parsers) => 'a');
}

#[test]
fn parser_can_match_with_take_until_n() {
    assert_parser!(should parse 4 elements from "aaaabc" using expect_character('a').take_until_n(4) => vec!['a', 'a', 'a', 'a']);
}

#[test]
fn take_until_n_will_match_only_up_to_specified_limit() {
    assert_parser!(should parse 3 elements from "aaaabc" using expect_character('a').take_until_n(3) => vec!['a', 'a', 'a' ]);
}

#[test]
fn take_until_n_will_return_as_many_matches_as_possible() {
    assert_parser!(should parse 2 elements from "aabc" using expect_character('a').take_until_n(3) => vec!['a', 'a']);
}

#[test]
fn take_until_n_returns_a_no_match_on_no_match() {
    assert_parser!(should not parse "abc" using expect_character('d').take_until_n(2));
}

#[test]
fn take_n_will_match_only_up_to_specified_limit() {
    assert_parser!(should parse 3 elements from "aaaabc" using expect_character('a').take_n(3) => vec!['a', 'a', 'a']);
}

#[test]
fn take_n_returns_a_no_match_on_no_match() {
    assert_parser!(should not parse "abc" using expect_character('d').take_n(2));
}

#[test]
fn predicate_should_not_match_if_case_is_true() {
    assert_parser!(should not parse "abc" using any_character().predicate(|&c| c != 'a'));
}
