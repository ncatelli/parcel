use criterion::{black_box, criterion_group, criterion_main, Criterion};
extern crate parcel;
use parcel::parsers::byte::{any_byte, expect_byte};
use parcel::Parser;

fn parse_map(c: &mut Criterion) {
    let mut group = c.benchmark_group("map combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::map(expect_byte(0x00), |result| result).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = expect_byte(0x00)
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
            let _expr = parcel::skip(expect_byte(0x00)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = expect_byte(0x00).skip().parse(black_box(&seed_vec));
        });
    });
}

fn parse_or(c: &mut Criterion) {
    let mut group = c.benchmark_group("or combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr =
                parcel::or(expect_byte(0x02), || expect_byte(0x00)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = expect_byte(0x02)
                .or(|| expect_byte(0x00))
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
            let _expr = parcel::one_of(vec![
                expect_byte(0x02),
                expect_byte(0x01),
                expect_byte(0x00),
            ])
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
            let _expr = parcel::and_then(expect_byte(0x00), |_| expect_byte(0x01))
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = expect_byte(0x00)
                .and_then(|_| expect_byte(0x01))
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
            let _expr = parcel::take_until_n(expect_byte(0x00), 4).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = expect_byte(0x00)
                .take_until_n(4)
                .parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_take_n(c: &mut Criterion) {
    let mut group = c.benchmark_group("take_n combinator");
    let seed_vec = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::take_n(expect_byte(0x00), 4).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = expect_byte(0x00).take_n(4).parse(black_box(&seed_vec));
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
            let _expr = parcel::zero_or_more(expect_byte(0x00)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = expect_byte(0x00).zero_or_more().parse(black_box(&seed_vec));
        });
    });
    group.finish();
}

fn parse_one_or_more(c: &mut Criterion) {
    let mut group = c.benchmark_group("one_or_more combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::one_or_more(expect_byte(0x00)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = expect_byte(0x00).one_or_more().parse(black_box(&seed_vec));
        });
    });
    group.finish()
}

fn parse_optional(c: &mut Criterion) {
    let mut group = c.benchmark_group("optional combinator");
    let seed_vec = vec![0x00, 0x01, 0x02];

    group.bench_function("combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::optional(expect_byte(0x00)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("boxed combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = expect_byte(0x00).optional().parse(black_box(&seed_vec));
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
                parcel::join(expect_byte(0x00), expect_byte(0x01)).parse(black_box(&seed_vec));
        });
    });

    group.bench_function("left combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::left(parcel::join(expect_byte(0x00), expect_byte(0x01)))
                .parse(black_box(&seed_vec));
        });
    });

    group.bench_function("right combinator with byte vec", |b| {
        b.iter(|| {
            let _expr = parcel::right(parcel::join(expect_byte(0x00), expect_byte(0x01)))
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
