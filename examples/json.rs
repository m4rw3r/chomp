extern crate chomp;

use std::collections::HashMap;
use std::mem::transmute;

use chomp::ascii::{is_digit, is_whitespace};
use chomp::combinators::{matched_by, or, option, sep_by};
use chomp::parsers::{SimpleResult, any, token, scan, skip_while, skip_while1, string};
use chomp::parsers::Error as ChompError;
use chomp::types::{Buffer, Input, ParseResult};

pub type Error = ChompError<u8>;

/// A JSON Value
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Array(Vec<Value>),
    Number(f64),
    Object(HashMap<String, Value>),
    String(String),
    True,
    False,
    Null,
}

/// Parses a `Value` from the supplied input.
pub fn parse<I: Input<Token=u8>>(i: I) -> ParseResult<I, Value, Error> {
    skip_while(i, is_whitespace).then(|i|
    or(i, |i|
        parse_object(i).map(Value::Object),        |i| or(i, |i|
        parse_array(i).map(Value::Array),          |i| or(i, |i|
        parse_string(i).map(Value::String),        |i| or(i, |i|
        parse_number(i).map(Value::Number),        |i| or(i, |i|
        string(i, b"true").map(|_|  Value::True),  |i| or(i, |i|
        string(i, b"false").map(|_| Value::False), |i| or(i, |i|
        string(i, b"null").map(|_|  Value::Null),  |i|
        i.err(Error::unexpected())))))))))
}

// AKA match_float + FromStr
//
// TODO: Move to ascii module with proper tests
/// Parses a floating point number from the input
fn parse_number<I: Input<Token=u8>>(i: I) -> ParseResult<I, f64, Error> {
    fn sign<I: Input<Token=u8>>(i: I) -> SimpleResult<I, u8> {
        or(i, |i| token(i, b'+'), |i| token(i, b'-'))
    }
    fn signed_decimal<I: Input<Token=u8>>(i: I) -> SimpleResult<I, ()> {
        option(i, sign, b'+').then(|i| skip_while1(i, is_digit))
    }
    fn e<I: Input<Token=u8>>(i: I) -> SimpleResult<I, u8> {
        or(i, |i| token(i, b'e'), |i| token(i, b'E'))
    }
    fn make_num<B: Buffer<Token=u8>>(b: B) -> f64 {
        // If we add a restriction that Input<Buffer=&[u8]> then we can skip this allocation,
        // or if we reimplement float-parsing properly (or find a library where we can supply
        // numbers instead of a string-slice.
        let v = b.to_vec();

        // v only contains [-+0-9.eE], utf-8 safe
        let s: &str = unsafe { transmute(&v[..]) };

        s.parse().expect("Invalid floating number")
    }

    matched_by(i, |i|
        signed_decimal(i).then(|i|
        option(i, |i| token(i, b'.').then(|i| skip_while1(i, is_digit)), ()).then(|i|
        option(i, |i| e(i).then(signed_decimal), ())))).map(|(b, _)| make_num(b))
}

/// Parse a quoted string
fn parse_string<I: Input<Token=u8>>(i: I) -> ParseResult<I, String, Error> {
    token(i, b'"').then(|i| scan(i, b'\0', |s, c| match (s, c) {
        (b'\\', b'"')  => Some(c),
        (b'\\', b'\\') => Some(b'\0'), // null here because we need \\" to end
        (_,     b'"')  => None,
        (_,     _)     => Some(c),
    }).bind(|i, b| any(i).map(|_| unescape(b))))
}

/// Unescape the contents of a quoted string.
fn unescape<B: Buffer<Token=u8>>(b: B) -> String {
    // FIXME: Implement escape sequence parsing
    unsafe { String::from_utf8_unchecked(b.to_vec()) }
}

/// Parses a JSON Object
fn parse_object<I: Input<Token=u8>>(i: I) -> ParseResult<I, HashMap<String, Value>, Error> {
    token(i, b'{').then(|i|
    skip_while(i, is_whitespace).then(|i|
    sep_by(i, parse_key_value, separator).bind(|i, m|
    skip_while(i, is_whitespace).then(|i|
    token(i, b'}').map(|_| m)))))
}

/// Whitespace + comma, separates key-value pairs in objects and values in arrays
fn separator<I: Input<Token=u8>>(i: I) -> ParseResult<I, (), Error> {
    skip_while(i, is_whitespace).then(|i|
    token(i, b',').then(|i|
    skip_while(i, is_whitespace))).map_err(From::from)
}

/// Parses string-key: value
fn parse_key_value<I: Input<Token=u8>>(i: I) -> ParseResult<I, (String, Value), Error> {
    parse_string(i).bind(|i, s|
    skip_while(i, is_whitespace).then(|i|
    token(i, b':').then(|i|
    skip_while(i, is_whitespace).then(|i|
    parse(i).map(|v| (s, v))))))
}

/// Parses a JSON array
fn parse_array<I: Input<Token=u8>>(i: I) -> ParseResult<I, Vec<Value>, Error> {
    token(i, b'[').then(|i|
    sep_by(i, parse, separator).bind(|i, v|
    token(i, b']').map(|_| v)))
}

use chomp::parse_only;
use chomp::combinators::many;

fn main() {
    let t: Vec<_> = parse_only(|i| many(i, parse), &b"{\"foo\": 1.23, \"some_more\": [1, 2, 3, \"lol\"]}"[..]).unwrap();

    println!("{:?}", t);
}
