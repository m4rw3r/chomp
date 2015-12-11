#![feature(test)]
extern crate test;
#[macro_use]
extern crate chomp;

use test::Bencher;

use std::iter;

use chomp::*;
use chomp::buffer::{Stream, IntoStream};

#[bench]
fn many_vec_1k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(1024).collect::<Vec<u8>>();

    fn many_vec<I: Copy>(i: Input<I>) -> ParseResult<I, Vec<I>, Error<I>> {
        many(i, any)
    }

    b.iter(|| {
        data.into_stream().parse(many_vec)
    })
}

#[bench]
fn many_vec_10k(b: &mut Bencher) {
    let data = iter::repeat(b'a').take(10024).collect::<Vec<u8>>();

    fn many_vec<I: Copy>(i: Input<I>) -> ParseResult<I, Vec<I>, Error<I>> {
        many(i, any)
    }

    b.iter(|| {
        data.into_stream().parse(many_vec)
    })
}
