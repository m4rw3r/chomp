#![feature(conservative_impl_trait)]
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

    fn count_vec<I: Input>() -> impl Parser<I, Output=Vec<I::Token>, Error=Error<I::Token>> {
        count(1024, any)
    }

    b.iter(|| {
        count_vec().parse(&data[..])
    })
}

#[bench]
fn count_vec_10k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn count_vec<I: Input>() -> impl Parser<I, Output=Vec<I::Token>, Error=Error<I::Token>> {
        count(10024, any)
    }

    b.iter(|| {
        count_vec().parse(&data[..])
    })
}

#[bench]
fn many_vec_1k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(1024).collect::<Vec<u8>>();

    fn many_vec<I: Input>() -> impl Parser<I, Output=Vec<I::Token>, Error=Error<I::Token>> {
        many(any)
    }

    b.iter(|| {
        many_vec().parse(&data[..])
    })
}

#[bench]
fn many_vec_10k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn many_vec<I: Input>() -> impl Parser<I, Output=Vec<I::Token>, Error=Error<I::Token>> {
        many(any)
    }

    b.iter(|| {
        many_vec().parse(&data[..])
    })
}

#[bench]
fn many1_vec_1k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(1024).collect::<Vec<u8>>();

    fn many1_vec<I: Input>() -> impl Parser<I, Output=Vec<I::Token>, Error=Error<I::Token>> {
        many1(any)
    }

    b.iter(|| {
        many1_vec().parse(&data[..])
    })
}

#[bench]
fn many1_vec_10k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn many1_vec<I: Input>() -> impl Parser<I, Output=Vec<I::Token>, Error=Error<I::Token>> {
        many1(any)
    }

    b.iter(|| {
        many1_vec().parse(&data[..])
    })
}

#[bench]
fn count_vec_10k_maybe_incomplete(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn count_vec<I: Input>() -> impl Parser<I, Output=Vec<I::Token>, Error=Error<I::Token>> {
        count(10024, any)
    }

    b.iter(|| {
        count_vec().parse(InputBuf::new(&data))
    })
}

#[bench]
fn many_vec_10k_maybe_incomplete(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn many_vec<I: Input>() -> impl Parser<I, Output=Vec<I::Token>, Error=Error<I::Token>> {
        many(any)
    }

    b.iter(|| {
        many_vec().parse(InputBuf::new(&data))
    })
}

#[bench]
fn many1_vec_10k_maybe_incomplete(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn many1_vec<I: Input>() -> impl Parser<I, Output=Vec<I::Token>, Error=Error<I::Token>> {
        many1(any)
    }

    b.iter(|| {
        many1_vec().parse(InputBuf::new(&data))
    })
}
