use criterion::{criterion_group, criterion_main, Criterion};
extern crate parcel;
use parcel::Parser;

fn match_char<'a>(expected: char) -> impl parcel::Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(next) if *next == expected => {
            Ok(parcel::MatchStatus::Match((&input[1..], next.clone())))
        }
        _ => Ok(parcel::MatchStatus::NoMatch(input)),
    }
}

fn parse_map(c: &mut Criterion) {
    let seed_vec = vec!['a', 'b', 'c'];

    c.bench_function("parse expressions", |b| {
        b.iter(|| {
            let _expr = parcel::map(match_char('a'), |result| result.to_string()).parse(&seed_vec);
        });
    });
}

criterion_group!(benches, parse_map);
criterion_main!(benches);