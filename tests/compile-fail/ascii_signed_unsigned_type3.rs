// error-pattern:error: type mismatch resolving `<u64 as conv::ValueFrom<i8>>::Err == conv::errors::NoError`

extern crate chomp;

use chomp::{Input, U8Result};
use chomp::ascii::{signed, decimal};

// Should not be possible to use unsigned integers with signed
fn parser(i: Input<u8>) -> U8Result<u64> {
    signed(i, decimal)
}

fn main() {
    let r = parser(Input::new(b"-123"));
}
