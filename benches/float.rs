#![feature(test)]
extern crate test;
#[macro_use]
extern crate chomp;

use std::str;
use std::str::FromStr;

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

#[bench]
fn float_small_f64(b: &mut Bencher) {
    assert_eq!(ascii::float::<_, f64>(&b"1"[..]).into_inner(), (&b""[..], Ok(1.0)));

    b.iter(|| {
        ascii::float::<_, f64>(&b"1"[..])
    })
}

#[bench]
fn float_small_f32(b: &mut Bencher) {
    assert_eq!(ascii::float::<_, f32>(&b"1"[..]).into_inner(), (&b""[..], Ok(1.0)));

    b.iter(|| {
        ascii::float::<_, f32>(&b"1"[..])
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

#[bench]
fn float_small_no_conversion(b: &mut Bencher) {
    b.iter(|| {
        ascii::match_float(&b"1"[..]).map(|b| b.into_vec())
    })
}

/// Reference, 32-bit
#[bench]
fn from_str_f32(b: &mut Bencher) {
    assert_eq!(FromStr::from_str(unsafe { str::from_utf8_unchecked(&PI_SLICE[..]) }), Ok(PI_F32));

    b.iter(|| {
        let f: Result<f32, _> = FromStr::from_str(unsafe { str::from_utf8_unchecked(&PI_SLICE[..]) });

        f
    })
}

/// Reference, 64-bit
#[bench]
fn from_str_f64(b: &mut Bencher) {
    assert_eq!(FromStr::from_str(unsafe { str::from_utf8_unchecked(&PI_SLICE[..]) }), Ok(PI_F64));

    b.iter(|| {
        let f: Result<f64, _> = FromStr::from_str(unsafe { str::from_utf8_unchecked(&PI_SLICE[..]) });

        f
    })
}


/// Reference, 32-bit, small
#[bench]
fn from_str_small_f32(b: &mut Bencher) {
    assert_eq!(FromStr::from_str(unsafe { str::from_utf8_unchecked(&b"1"[..]) }), Ok(1.0f32));

    b.iter(|| {
        let f: Result<f32, _> = FromStr::from_str(unsafe { str::from_utf8_unchecked(&b"1"[..]) });

        f
    })
}

/// Reference, 64-bit
#[bench]
fn from_str_small_f64(b: &mut Bencher) {
    assert_eq!(FromStr::from_str(unsafe { str::from_utf8_unchecked(&b"1"[..]) }), Ok(1.0f64));

    b.iter(|| {
        let f: Result<f64, _> = FromStr::from_str(unsafe { str::from_utf8_unchecked(&b"1"[..]) });

        f
    })
}
