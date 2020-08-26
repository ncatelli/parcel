use criterion::{black_box, criterion_group, criterion_main, Criterion};
extern crate parcel;
use parcel::Parser;

fn match_byte<'a>(expected: u8) -> impl parcel::Parser<'a, &'a [u8], u8> {
    move |input: &'a [u8]| match input.get(0) {
        Some(&next) if next == expected => Ok(parcel::MatchStatus::Match((&input[1..], next))),
        _ => Ok(parcel::MatchStatus::NoMatch(input)),
    }
}

fn any_byte<'a>() -> impl parcel::Parser<'a, &'a [u8], u8> {
    move |input: &'a [u8]| match input.get(0) {
        Some(&next) => Ok(parcel::MatchStatus::Match((&input[1..], next))),
        _ => Ok(parcel::MatchStatus::NoMatch(input)),
    }
}

fn parse_map(c: &mut Criterion) {
    let mut group = c.benchmark_group("map combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::map(match_byte(0x00), |result| result).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = match_byte(0x00)
                .map(|result| result)
                .parse(black_box(&seed_vec));
        });
    });
}

fn parse_skip(c: &mut Criterion) {
    let mut group = c.benchmark_group("skip combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::skip(match_byte(0x00)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = match_byte(0x00).skip().parse(black_box(&seed_vec));
        });
    });
}

fn parse_or(c: &mut Criterion) {
    let mut group = c.benchmark_group("or combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr =
                parcel::or(match_byte(0x02), || match_byte(0x00)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = match_byte(0x02)
                .or(|| match_byte(0x00))
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_one_of(c: &mut Criterion) {
    let mut group = c.benchmark_group("one_of combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::one_of(vec![match_byte(0x02), match_byte(0x01), match_byte(0x00)])
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_and_then(c: &mut Criterion) {
    let mut group = c.benchmark_group("and_then combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with u8 vec", |b| {
        b.iter(|| {
            let _expr = parcel::and_then(match_byte(0x00), |_| match_byte(0x01))
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = match_byte(0x00)
                .and_then(|_| match_byte(0x01))
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_take_until_n(c: &mut Criterion) {
    let mut group = c.benchmark_group("take_until_n combinator");
    let seed_vec = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::take_until_n(match_byte(0x00), 4).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = match_byte(0x00).take_until_n(4).parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_predicate(c: &mut Criterion) {
    let mut group = c.benchmark_group("predicate combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::predicate(any_byte(), |&b| b != 0x01).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with u8 vec", |b| {
        b.iter(|| {
            let _expr = any_byte()
                .predicate(|&b| b != 0x01)
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_zero_or_more(c: &mut Criterion) {
    let mut group = c.benchmark_group("zero_or_more combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::zero_or_more(match_byte(0x00)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = match_byte(0x00).zero_or_more().parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_one_or_more(c: &mut Criterion) {
    let mut group = c.benchmark_group("one_or_more combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::one_or_more(match_byte(0x00)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = match_byte(0x00).one_or_more().parse(black_box(&seed_vec));
        });
    });
    group.finish()
}

fn parse_optional(c: &mut Criterion) {
    let mut group = c.benchmark_group("optional combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::optional(match_byte(0x00)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = match_byte(0x00).optional().parse(black_box(&seed_vec));
        });
    });
    group.finish()
}

fn parse_applicatives(c: &mut Criterion) {
    let mut group = c.benchmark_group("applicatives combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("join combinator with byte vec", |b| {
        b.iter(|| {
            let _expr =
                parcel::join(match_byte(0x00), match_byte(0x01)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("left combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::left(parcel::join(match_byte(0x00), match_byte(0x01)))
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("right combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::right(parcel::join(match_byte(0x00), match_byte(0x01)))
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
    parse_take_until_n,
    parse_predicate,
    parse_zero_or_more,
    parse_one_or_more,
    parse_optional,
    parse_applicatives
);
criterion_main!(benches);
