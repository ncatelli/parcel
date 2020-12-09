use criterion::{black_box, criterion_group, criterion_main, Criterion};
extern crate parcel;
use parcel::parsers::character::{any_character, expect_character};
use parcel::Parser;

fn parse_map(c: &mut Criterion) {
    let mut group = c.benchmark_group("map combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr =
                parcel::map(expect_character('a'), |result| result).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = expect_character('a')
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
            let _expr = parcel::skip(expect_character('a')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = expect_character('a').skip().parse(black_box(&seed_vec));
        });
    });
}

fn parse_or(c: &mut Criterion) {
    let mut group = c.benchmark_group("or combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::or(expect_character('c'), || expect_character('a'))
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = expect_character('c')
                .or(|| expect_character('a'))
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
            let _expr = parcel::one_of(vec![
                expect_character('c'),
                expect_character('b'),
                expect_character('a'),
            ])
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
            let _expr = parcel::and_then(expect_character('a'), |_| expect_character('b'))
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = expect_character('a')
                .and_then(|_| expect_character('b'))
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_peek_next(c: &mut Criterion) {
    let mut group = c.benchmark_group("peek_next combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::peek_next(expect_character('a'), expect_character('b'))
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = expect_character('a')
                .peek_next(expect_character('b'))
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
            let _expr = parcel::take_until_n(expect_character('a'), 4).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = expect_character('a')
                .take_until_n(4)
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_take_n(c: &mut Criterion) {
    let mut group = c.benchmark_group("take_n combinator");
    let seed_vec = vec!['a', 'a', 'a', 'a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::take_n(expect_character('a'), 4).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = expect_character('a').take_n(4).parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_predicate(c: &mut Criterion) {
    let mut group = c.benchmark_group("predicate combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr =
                parcel::predicate(any_character(), |&c| c != 'b').parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = any_character()
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
            let _expr = parcel::zero_or_more(expect_character('a')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = expect_character('a')
                .zero_or_more()
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_one_or_more(c: &mut Criterion) {
    let mut group = c.benchmark_group("one_or_more combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::one_or_more(expect_character('a')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = expect_character('a')
                .one_or_more()
                .parse(black_box(&seed_vec));
        });
    });
    group.finish()
}

fn parse_optional(c: &mut Criterion) {
    let mut group = c.benchmark_group("optional combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::optional(expect_character('a')).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with char vec", |b| {
        b.iter(|| {
            let _expr = expect_character('a').optional().parse(black_box(&seed_vec));
        });
    });
    group.finish()
}

fn parse_applicatives(c: &mut Criterion) {
    let mut group = c.benchmark_group("applicatives combinator");
    let seed_vec = vec!['a', 'b', 'c'];

    group.bench_function("join combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::join(expect_character('a'), expect_character('b'))
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("left combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::left(parcel::join(expect_character('a'), expect_character('b')))
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("right combinator with char vec", |b| {
        b.iter(|| {
            let _expr = parcel::right(parcel::join(expect_character('a'), expect_character('b')))
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
    parse_peek_next,
    parse_take_n,
    parse_take_until_n,
    parse_predicate,
    parse_zero_or_more,
    parse_one_or_more,
    parse_optional,
    parse_applicatives
);
criterion_main!(benches);
