// error-pattern:error[E0271]: type mismatch resolving `<u64 as conv::ValueFrom<i8>>::Err == conv::errors::NoError`

extern crate chomp;

use chomp::prelude::{U8Input, SimpleResult, parse_only};
use chomp::ascii::{signed, decimal};

// Should not be possible to use unsigned integers with signed
fn parser<I: U8Input>(i: I) -> SimpleResult<I, u64> {
    signed(i, decimal)
}

fn main() {
    let r = parse_only(parser, b"-123");
}
