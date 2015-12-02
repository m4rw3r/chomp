// error-pattern:error: type mismatch resolving `<i8 as conv::ValueFrom<u8>>::Err == conv::errors::NoError`

extern crate chomp;

use chomp::{Input, U8Result};
use chomp::ascii::{signed, decimal};

// Should not be possible to use unsigned integers with signed
fn parser(i: Input<u8>) -> U8Result<i8> {
    signed(i, decimal)
}

fn main() {
    let r = parser(Input::new(b"-123"));
}
