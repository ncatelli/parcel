use crate::prelude::v1::*;
use crate::{
    join, left, one_or_more, optional, predicate, right, take_n, take_until_n, zero_or_more,
    MatchStatus,
};

fn match_char<'a>(expected: char) -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next == expected => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

fn any_char<'a>() -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) => Ok(MatchStatus::Match((&input[1..], next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

#[test]
fn parser_should_parse_char_match() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'))),
        match_char('a').parse(&input)
    );
}

#[test]
fn parser_can_map_a_result() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'.to_string()))),
        match_char('a')
            .map(|result| { result.to_string() })
            .parse(&input)
    );
}

#[test]
fn parser_should_skip_a_result() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[1..])),
        match_char('a').skip().parse(&input)
    );
}

#[test]
fn parser_should_not_skip_input_if_parser_does_not_match() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        match_char('x').skip().parse(&input)
    );
}

#[test]
fn parser_can_match_with_or() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'))),
        match_char('d').or(|| match_char('a')).parse(&input)
    );
}

#[test]
fn parser_can_match_with_one_of() {
    let input = vec!['a', 'b', 'c'];
    let parsers = vec![match_char('b'), match_char('c'), match_char('a')];
    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'))),
        crate::one_of(parsers).parse(&input)
    );
}

#[test]
fn parser_can_match_with_and_then() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], 'b'))),
        match_char('a').and_then(|_| match_char('b')).parse(&input)
    );
}

#[test]
fn parser_can_match_with_take_until_n() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[4..], vec!['a', 'a', 'a', 'a']))),
        take_until_n(match_char('a'), 4).parse(&input)
    );
}

#[test]
fn parser_can_match_with_boxed_take_until_n() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[4..], vec!['a', 'a', 'a', 'a']))),
        match_char('a').take_until_n(4).parse(&input)
    );
}

#[test]
fn take_until_n_will_match_only_up_to_specified_limit() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[3..], vec!['a', 'a', 'a']))),
        match_char('a').take_until_n(3).parse(&input)
    );
}

#[test]
fn take_until_n_will_return_as_many_matches_as_possible() {
    let input = vec!['a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], vec!['a', 'a']))),
        match_char('a').take_until_n(3).parse(&input)
    );
}

#[test]
fn take_until_n_returns_a_no_match_on_no_match() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        match_char('d').take_until_n(2).parse(&input)
    );
}

#[test]
fn parser_can_match_with_take_n() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[4..], vec!['a', 'a', 'a', 'a']))),
        take_n(match_char('a'), 4).parse(&input)
    );
}

#[test]
fn parser_can_match_with_boxed_take_n() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[4..], vec!['a', 'a', 'a', 'a']))),
        match_char('a').take_n(4).parse(&input)
    );
}

#[test]
fn take_n_will_match_only_up_to_specified_limit() {
    let input = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[3..], vec!['a', 'a', 'a']))),
        match_char('a').take_n(3).parse(&input)
    );
}

#[test]
fn take_n_will_not_match_if_unable_to_match_n_results() {
    let input = vec!['a', 'a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        match_char('a').take_n(3).parse(&input)
    );
}

#[test]
fn take_n_returns_a_no_match_on_no_match() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        match_char('d').take_n(2).parse(&input)
    );
}

#[test]
fn parser_joins_values_on_match_with_join_combinator() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], ('a', 'b')))),
        join(match_char('a'), match_char('b')).parse(&input)
    );
}

#[test]
fn applicatives_can_retrieve_each_independent_value() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], 'a'))),
        left(join(match_char('a'), match_char('b'))).parse(&input)
    );

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], 'b'))),
        right(join(match_char('a'), match_char('b'))).parse(&input)
    );
}

#[test]
fn predicate_should_match_if_case_fail() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'))),
        predicate(any_char(), |&c| c != 'c').parse(&input)
    );
}

#[test]
fn predicate_should_not_match_if_case_is_true() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        predicate(any_char(), |&c| c != 'a').parse(&input)
    );
}

#[test]
fn predicate_should_match_until_case_fails() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[2..], vec!['a', 'b']))),
        zero_or_more(predicate(any_char(), |&c| c != 'c')).parse(&input)
    );
}

#[test]
fn one_or_more_returns_no_match_when_no_matches_exist() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::NoMatch(&input[0..])),
        one_or_more(match_char('b')).parse(&input)
    );
}

#[test]
fn zero_or_more_returns_match_when_matches_exist() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], vec!['a']))),
        zero_or_more(match_char('a')).parse(&input)
    );
}

#[test]
fn zero_or_more_returns_match_when_no_matches_exist() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[0..], Vec::new()))),
        zero_or_more(match_char('b')).parse(&input)
    );
}

#[test]
fn optional_matches_on_zero() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[0..], None))),
        optional(match_char('b')).parse(&input)
    );
}

#[test]
fn optional_matches_on_one() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], Some('a')))),
        optional(match_char('a')).parse(&input)
    );
}
