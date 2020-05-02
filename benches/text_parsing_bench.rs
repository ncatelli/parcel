use criterion::{black_box, criterion_group, criterion_main, Criterion};
extern crate parcel;
use parcel::Parser;

fn match_char<'a>(expected: char) -> impl parcel::Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(next) if *next == expected => Ok(parcel::MatchStatus::Match((&input[1..], *next))),
        _ => Ok(parcel::MatchStatus::NoMatch(input)),
    }
}

fn parse_map(c: &mut Criterion) {
    let mut group = c.benchmark_group("map combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::map(match_char('a'), |result| result.to_string())
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = match_char('a')
                .map(|result| result.to_string())
                .parse(black_box(&seed_vec));
        });
    });
}

fn parse_or(c: &mut Criterion) {
    let mut group = c.benchmark_group("or combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::or(match_char('c'), || match_char('a')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = match_char('c')
                .or(|| match_char('a'))
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

criterion_group!(benches, parse_map, parse_or);
criterion_main!(benches);
