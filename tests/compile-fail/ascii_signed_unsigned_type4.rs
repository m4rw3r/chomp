// error-pattern:error[E0271]: type mismatch resolving `<i8 as conv::ValueFrom<u8>>::Err == conv::errors::NoError`

#![feature(conservative_impl_trait)]
extern crate chomp;

use chomp::prelude::{U8Input, Parser, Error, parse_only};
use chomp::ascii::{signed, decimal};

// Should not be possible to use unsigned integers with signed equal or smaller
fn parser<I: U8Input>() -> impl Parser<I, Output=i8, Error=Error<u8>> {
    signed(decimal())
}

fn main() {
    let r = parse_only(parser, b"-123");
}
