use criterion::{black_box, criterion_group, criterion_main, Criterion};
extern crate parcel;
use parcel::Parser;

fn match_char<'a>(expected: char) -> impl parcel::Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) if next == expected => Ok(parcel::MatchStatus::Match((&input[1..], next))),
        _ => Ok(parcel::MatchStatus::NoMatch(input)),
    }
}

fn any_char<'a>() -> impl parcel::Parser<'a, &'a [char], char> {
    move |input: &'a [char]| match input.get(0) {
        Some(&next) => Ok(parcel::MatchStatus::Match((&input[1..], next))),
        _ => Ok(parcel::MatchStatus::NoMatch(input)),
    }
}

fn parse_map(c: &mut Criterion) {
    let mut group = c.benchmark_group("map combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::map(match_char('a'), |result| result).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = match_char('a')
                .map(|result| result)
                .parse(black_box(&seed_vec));
        });
    });
}

fn parse_skip(c: &mut Criterion) {
    let mut group = c.benchmark_group("skip combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::skip(match_char('a')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = match_char('a').skip().parse(black_box(&seed_vec));
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

fn parse_one_of(c: &mut Criterion) {
    let mut group = c.benchmark_group("one_of combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::one_of(vec![match_char('c'), match_char('b'), match_char('a')])
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_and_then(c: &mut Criterion) {
    let mut group = c.benchmark_group("and_then combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr =
                parcel::and_then(match_char('a'), |_| match_char('b')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = match_char('a')
                .and_then(|_| match_char('b'))
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_take_until_n(c: &mut Criterion) {
    let mut group = c.benchmark_group("take_until_n combinator");
    let seed_vec = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::take_until_n(match_char('a'), 4).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = match_char('a').take_until_n(4).parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_take_n(c: &mut Criterion) {
    let mut group = c.benchmark_group("take_n combinator");
    let seed_vec = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::take_n(match_char('a'), 4).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = match_char('a').take_n(4).parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_predicate(c: &mut Criterion) {
    let mut group = c.benchmark_group("predicate combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::predicate(any_char(), |&c| c != 'b').parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = any_char()
                .predicate(|&c| c != 'b')
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_zero_or_more(c: &mut Criterion) {
    let mut group = c.benchmark_group("zero_or_more combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::zero_or_more(match_char('a')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = match_char('a').zero_or_more().parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_one_or_more(c: &mut Criterion) {
    let mut group = c.benchmark_group("one_or_more combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::one_or_more(match_char('a')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = match_char('a').one_or_more().parse(black_box(&seed_vec));
        });
    });
    group.finish()
}

fn parse_optional(c: &mut Criterion) {
    let mut group = c.benchmark_group("optional combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::optional(match_char('a')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = match_char('a').optional().parse(black_box(&seed_vec));
        });
    });
    group.finish()
}

fn parse_applicatives(c: &mut Criterion) {
    let mut group = c.benchmark_group("applicatives combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("join combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::join(match_char('a'), match_char('b')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("left combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::left(parcel::join(match_char('a'), match_char('b')))
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("right combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::right(parcel::join(match_char('a'), match_char('b')))
                .parse(black_box(&seed_vec));
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    parse_map,
    parse_skip,
    parse_or,
    parse_one_of,
    parse_and_then,
    parse_take_n,
    parse_take_until_n,
    parse_predicate,
    parse_zero_or_more,
    parse_one_or_more,
    parse_optional,
    parse_applicatives
);
criterion_main!(benches);
