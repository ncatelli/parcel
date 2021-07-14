use crate::parsers::byte::{any_byte, expect_byte};
use crate::prelude::v1::*;

macro_rules! assert_parser {
    {$parser:expr, should parse $elements:literal elements from $input:expr => $output:expr} => {
        let input_vec: Vec<(usize, u8)> = $input.iter().copied().enumerate().collect();

        assert_eq!(
            Ok(MatchStatus::Match {
                span: 0..$elements,
                remainder: &input_vec[$elements..],
                inner: $output
            }),
            $parser.parse(&input_vec[..])
        );
    };
    {$parser:expr, should parse $elements:literal element from $input:expr => $output:expr} => {
        assert_parser!($parser, should parse $elements elements from $input => $output);
    };

    // No Match
    {$parser:expr, should not parse $input:expr} => {
        let input_vec: Vec<(usize, u8)> = $input.iter().copied().enumerate().collect();

        assert_eq!(
            Ok(MatchStatus::NoMatch(&input_vec[..])),
            $parser.parse(&input_vec[..])
        );
    };
}

#[test]
fn parser_should_parse_byte_match() {
    assert_parser!(expect_byte(0x00), should parse 1 element from [0x00, 0x01, 0x02] => 0x00);
}

#[test]
fn parser_should_not_skip_input_if_parser_does_not_match() {
    assert_parser!(expect_byte(0xFF).skip(), should not parse [0x00, 0x01, 0x02]);
}

#[test]
fn parser_can_match_with_take_until_n() {
    assert_parser!(expect_byte(0x00).take_until_n(4), should parse 4 elements from [0x00, 0x00, 0x00, 0x00, 0x01, 0x02] => vec![0x00, 0x00, 0x00, 0x00]);
}

#[test]
fn take_until_n_will_match_only_up_to_specified_limit() {
    assert_parser!(expect_byte(0x00).take_until_n(3), should parse 3 elements from [0x00, 0x00, 0x00, 0x00, 0x01, 0x02] => vec![0x00, 0x00, 0x00]);
}

#[test]
fn take_until_n_will_return_as_many_matches_as_possible() {
    assert_parser!(expect_byte(0x00).take_until_n(3), should parse 2 elements from [0x00, 0x00, 0x01, 0x02] => vec![0x00, 0x00]);
}

#[test]
fn take_until_n_returns_a_no_match_on_no_match() {
    assert_parser!(expect_byte(0x03).take_until_n(2), should not parse [0x00, 0x01, 0x02]);
}

#[test]
fn take_n_returns_a_no_match_on_no_match() {
    assert_parser!(expect_byte(0x03).take_n(2), should not parse [0x00, 0x01, 0x02]);
}

#[test]
fn predicate_should_not_match_if_case_is_true() {
    assert_parser!(any_byte().predicate(|&c| c != 0x00), should not parse [0x00, 0x01, 0x02]);
}
