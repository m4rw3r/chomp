#![feature(test)]
extern crate test;
#[macro_use]
extern crate chomp;

use std::str::FromStr;
use std::mem::transmute;

use test::Bencher;

use chomp::types::Buffer;
use chomp::ascii;
use chomp::primitives::IntoInner;

const PI_SLICE: &'static [u8] = b"3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798";
const PI_F64: f64             = 3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798;
const PI_F32: f32             = 3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798;

#[bench]
fn match_float(b: &mut Bencher) {
    b.iter(|| {
        ascii::match_float(&PI_SLICE[..])
    })
}

#[bench]
fn float_f64(b: &mut Bencher) {
    assert_eq!(ascii::float::<_, f64>(&PI_SLICE[..]).into_inner(), (&b""[..], Ok(PI_F64)));

    b.iter(|| {
        ascii::float::<_, f64>(&PI_SLICE[..])
    })
}

#[bench]
fn float_f32(b: &mut Bencher) {
    assert_eq!(ascii::float::<_, f32>(&PI_SLICE[..]).into_inner(), (&b""[..], Ok(PI_F32)));

    b.iter(|| {
        ascii::float::<_, f32>(&PI_SLICE[..])
    })
}

/// The purpose of this test is to measure the time Chomp uses to parse and allocate the vector
/// required to pass the data on to Rust's `FromStr` implementation for `f32` and `f64`.
#[bench]
fn float_no_conversion(b: &mut Bencher) {
    b.iter(|| {
        ascii::match_float(&PI_SLICE[..]).map(|b| b.into_vec())
    })
}

/// Reference, 32-bit
#[bench]
fn from_str_f32(b: &mut Bencher) {
    assert_eq!(FromStr::from_str(unsafe { transmute(&PI_SLICE[..]) }), Ok(PI_F32));

    b.iter(|| {
        let f: Result<f32, _> = FromStr::from_str(unsafe { transmute(&PI_SLICE[..]) });

        f
    })
}

/// Reference, 64-bit
#[bench]
fn from_str_f64(b: &mut Bencher) {
    assert_eq!(FromStr::from_str(unsafe { transmute(&PI_SLICE[..]) }), Ok(PI_F64));

    b.iter(|| {
        let f: Result<f64, _> = FromStr::from_str(unsafe { transmute(&PI_SLICE[..]) });

        f
    })
}
