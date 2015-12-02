// error-pattern:error: type mismatch resolving `<u8 as conv::ValueFrom<i8>>::Err == conv::errors::NoError`

extern crate chomp;

use chomp::{Input, U8Result};
use chomp::ascii::{signed, decimal};

// Should not be possible to use unsigned integers with signed
fn parser(i: Input<u8>) -> U8Result<u8> {
    signed(i, decimal)
}

fn main() {
    let r = parser(Input::new(b"-123"));
}
