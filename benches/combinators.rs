#![feature(test)]
extern crate test;
#[macro_use]
extern crate chomp;

use test::Bencher;

use std::iter;

use chomp::prelude::*;
use chomp::buffer::InputBuf;

#[bench]
fn count_vec_1k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(1024).collect::<Vec<u8>>();

    fn count_vec<I: Input>(i: I) -> ParseResult<I, Vec<I::Token>, Error<I::Token>> {
        count(i, 1024, any)
    }

    b.iter(|| {
        parse_only(count_vec, &data)
    })
}

#[bench]
fn count_vec_10k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10240).collect::<Vec<u8>>();

    fn count_vec<I: Input>(i: I) -> ParseResult<I, Vec<I::Token>, Error<I::Token>> {
        count(i, 10240, any)
    }

    b.iter(|| {
        parse_only(count_vec, &data)
    })
}

#[bench]
fn many_vec_1k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(1024).collect::<Vec<u8>>();

    fn many_vec<I: Input>(i: I) -> ParseResult<I, Vec<I::Token>, Error<I::Token>> {
        many(i, any)
    }

    b.iter(|| {
        parse_only(many_vec, &data)
    })
}

#[bench]
fn many_vec_10k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn many_vec<I: Input>(i: I) -> ParseResult<I, Vec<I::Token>, Error<I::Token>> {
        many(i, any)
    }

    b.iter(|| {
        parse_only(many_vec, &data)
    })
}

#[bench]
fn many1_vec_1k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(1024).collect::<Vec<u8>>();

    fn many1_vec<I: Input>(i: I) -> ParseResult<I, Vec<I::Token>, Error<I::Token>> {
        many1(i, any)
    }

    b.iter(|| {
        parse_only(many1_vec, &data)
    })
}

#[bench]
fn many1_vec_10k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn many1_vec<I: Input>(i: I) -> ParseResult<I, Vec<I::Token>, Error<I::Token>> {
        many1(i, any)
    }

    b.iter(|| {
        parse_only(many1_vec, &data)
    })
}

#[bench]
fn count_vec_10k_maybe_incomplete(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn count_vec<I: Input>(i: I) -> ParseResult<I, Vec<I::Token>, Error<I::Token>> {
        count(i, 10024, any)
    }

    b.iter(|| {
        count_vec(InputBuf::new(&data))
    })
}

#[bench]
fn many_vec_10k_maybe_incomplete(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn many_vec<I: Input>(i: I) -> ParseResult<I, Vec<I::Token>, Error<I::Token>> {
        many(i, any)
    }

    b.iter(|| {
        many_vec(InputBuf::new(&data))
    })
}

#[bench]
fn many1_vec_10k_maybe_incomplete(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn many1_vec<I: Input>(i: I) -> ParseResult<I, Vec<I::Token>, Error<I::Token>> {
        many1(i, any)
    }

    b.iter(|| {
        many1_vec(InputBuf::new(&data))
    })
}
