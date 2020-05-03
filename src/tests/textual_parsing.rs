use crate::{join, left, right, MatchStatus, Parser};

fn match_char<'a>(expected: char) -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(next) if *next == expected => Ok(MatchStatus::Match((&input[1..], *next))),
        _ => Ok(MatchStatus::NoMatch(input)),
    }
}

#[test]
fn validate_parser_should_parse_char_match() {
    let seed_vec = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&seed_vec[1..], 'a'))),
        match_char('a').parse(&seed_vec)
    );
}

#[test]
fn validate_parser_can_map_a_result() {
    let seed_vec = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&seed_vec[1..], 'a'.to_string()))),
        match_char('a')
            .map(|result| { result.to_string() })
            .parse(&seed_vec)
    );
}

#[test]
fn validate_parser_can_match_with_or() {
    let seed_vec = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&seed_vec[1..], 'a'))),
        match_char('d').or(|| match_char('a')).parse(&seed_vec)
    );
}

#[test]
fn validate_parser_can_match_with_and_then() {
    let seed_vec = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&seed_vec[2..], 'b'))),
        match_char('a')
            .and_then(|_| match_char('b'))
            .parse(&seed_vec)
    );
}

#[test]
fn validate_parser_joins_values_on_match_with_join_combinator() {
    let seed_vec = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&seed_vec[2..], ('a', 'b')))),
        join(match_char('a'), match_char('b')).parse(&seed_vec)
    );
}

#[test]
fn validate_applicatives_can_retrieve_each_independent_value() {
    let seed_vec = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok(MatchStatus::Match((&seed_vec[2..], 'a'))),
        left(join(match_char('a'), match_char('b'))).parse(&seed_vec)
    );

    assert_eq!(
        Ok(MatchStatus::Match((&seed_vec[2..], 'b'))),
        right(join(match_char('a'), match_char('b'))).parse(&seed_vec)
    );
}
