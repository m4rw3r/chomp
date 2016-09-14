// error-pattern:error[E0271]: type mismatch resolving `<u64 as conv::ValueFrom<i8>>::Err == conv::errors::NoError`

#![feature(conservative_impl_trait)]
extern crate chomp;

use chomp::prelude::{U8Input, Parser, Error, parse_only};
use chomp::ascii::{signed, decimal};

// Should not be possible to use unsigned integers with signed
fn parser<I: U8Input>() -> impl Parser<I, Output=u64, Error=Error<u8>> {
    signed(decimal())
}

fn main() {
    let r = parse_only(parser, b"-123");
}
