// error-pattern:error[E0271]: type mismatch resolving `<u32 as conv::ValueFrom<i8>>::Err == conv::errors::NoError`

extern crate chomp;

use chomp::{Input, U8Result, parse_only};
use chomp::ascii::{signed, decimal};

// Should not be possible to use unsigned integers with signed
fn parser(i: Input<u8>) -> U8Result<u32> {
    signed(i, decimal)
}

fn main() {
    let r = parse_only(parser, b"-123");
}
