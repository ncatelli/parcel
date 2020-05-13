use crate::prelude::v1::*;
use crate::{join, left, one_or_more, predicate, right, zero_or_more, MatchStatus};

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
fn parser_can_match_with_or() {
    let input = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&input[1..], 'a'))),
        match_char('d').or(|| match_char('a')).parse(&input)
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
