use crate::{map, Parser};

fn match_char<'a>(expected: char) -> impl Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(next) if *next == expected => Ok((&input[1..], next.clone())),
        _ => Err(input),
    }
}

#[test]
fn validate_parser_should_parse_char_match() {
    let seed_vec = vec!['a', 'b', 'c'];

    assert_eq!(Ok((&seed_vec[1..], 'a')), match_char('a').parse(&seed_vec));
}

#[test]
fn validate_parser_can_map_a_result() {
    let seed_vec = vec!['a', 'b', 'c'];

    assert_eq!(
        Ok((&seed_vec[1..], 'a'.to_string())),
        map(match_char('a'), |result| { result.to_string() }).parse(&seed_vec)
    );
}
