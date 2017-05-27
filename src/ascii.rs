//! Utilities and parsers for dealing with ASCII data in `u8` format.

use std::ops::{Add, Mul};

use conv::{
    NoError,
    ValueFrom,
};
use conv::errors::UnwrapOk;

use types::{Buffer, Input};
use combinators::{matched_by, option, or};
use parsers::{SimpleResult, Error, satisfy, skip_while, skip_while1, take_while1, token};

/// Lowercase ASCII predicate.
#[inline]
pub fn is_lowercase(c: u8) -> bool {
    b'a' <= c && c <= b'z'
}

/// Uppercase ASCII character predicate.
#[inline]
pub fn is_uppercase(c: u8) -> bool {
    b'A' <= c && c <= b'Z'
}

/// ASCII whitespace predicate.
///
/// Includes:
///
/// * Horizontal tab (TAB)
/// * Line feed (LF)
/// * Vertical tab (VT)
/// * Form feed (FF)
/// * Carriage return (CR)
/// * Space
#[inline]
pub fn is_whitespace(c: u8) -> bool {
    9 <= c && c <= 13 || c == b' '
}

/// A predicate which matches either space (' ') or horizontal tab ('\t').
#[inline]
pub fn is_horizontal_space(c: u8) -> bool {
    c == b'\t' || c == b' '
}

/// A predicate matching eithr a newline ('\n') or a carriage return ('\r').
#[inline]
pub fn is_end_of_line(c: u8) -> bool {
    c == b'\n' || c == b'\r'
}

/// ASCII digit predicate.
#[inline]
pub fn is_digit(c: u8) -> bool {
    b'0' <= c && c <= b'9'
}

/// ASCII alphabetic predicate.
#[inline]
pub fn is_alpha(c: u8) -> bool {
    is_lowercase(c) || is_uppercase(c)
}

/// ASCII alphanumeric predicate.
#[inline]
pub fn is_alphanumeric(c: u8) -> bool {
    is_alpha(c) || is_digit(c)
}

/// Skips over whitespace.
///
/// Matches zero-length.
///
/// # Example
///
/// ```
/// use chomp::parse_only;
/// use chomp::ascii::skip_whitespace;
///
/// assert_eq!(parse_only(skip_whitespace, b" \t "), Ok(()));
/// ```
#[inline]
pub fn skip_whitespace<I: Input<Token=u8>>(i: I) -> SimpleResult<I, ()> {
    skip_while(i, is_whitespace)
}

/// Parses a single digit.
///
/// # Note
///
/// The result is the code of the digit, no conversion takes place.
///
/// # Example
///
/// ```
/// use chomp::parse_only;
/// use chomp::ascii::digit;
///
/// assert_eq!(parse_only(digit, b"1"), Ok(b'1'));
/// ```
#[inline]
pub fn digit<I: Input<Token=u8>>(i: I) -> SimpleResult<I, u8> {
    satisfy(i, is_digit)
}

/// Parses a number with an optional leading '+' or '-'.
///
/// # Note
///
/// The from `i8` bound here is usually smaller than the number parser requirement for signed
/// integers (usually the smallest possible signed is `i16`).
///
/// # Example
///
/// ```
/// use chomp::parse_only;
/// use chomp::ascii::{decimal, signed};
///
/// let r: Result<i16, _> = parse_only(|i| signed(i, decimal), b"-123");
///
/// assert_eq!(r, Ok(-123i16));
/// ```
#[inline]
pub fn signed<I: Input<Token=u8>, T, F>(i: I, f: F) -> SimpleResult<I, T>
  where T: Copy + ValueFrom<i8, Err=NoError> + Add<Output=T> + Mul<Output=T>,
        F: FnOnce(I) -> SimpleResult<I, T> {
    option(i,
           |i| satisfy(i, |c| c == b'-' || c == b'+')
               .map(|s| T::value_from(if s == b'+' { 1 } else { -1 }).unwrap_ok()),
           T::value_from(1).unwrap_ok())
        .bind(|i, sign| f(i).map(|num| sign * num))
}

/// Parses a series of digits and converts them to an integer.
///
/// # Note
///
/// The `T` type must be larger than `u8` if it is signed.
///
/// # Example
///
/// ```
/// use chomp::parse_only;
/// use chomp::ascii::decimal;
///
/// let r = parse_only(decimal::<_, u8>, b"123");
///
/// assert_eq!(r, Ok(123u8));
/// ```
#[inline]
pub fn decimal<I: Input<Token=u8>, T: Copy + ValueFrom<u8, Err=NoError> + Add<Output=T> + Mul<Output=T>>(i: I) -> SimpleResult<I, T> {
    take_while1(i, is_digit).map(to_decimal)
}

/// Internal function converting a `[u8]` to the given integer type `T`.
///
/// # Notes
///
/// * The slice must not contain any other characters besides 0 to 9.
/// * The `T` type must be larger than `u8` if it is signed.
#[inline]
fn to_decimal<T: Copy + ValueFrom<u8, Err=NoError> + Add<Output=T> + Mul<Output=T>, I: Buffer<Token=u8>>(iter: I) -> T {
    iter.fold(T::value_from(0).unwrap_ok(), |a, n| a * T::value_from(10).unwrap_ok() + T::value_from(n - b'0').unwrap_ok())
}

/// Trait enabling the conversion from a matched `Buffer` to a float of the correct type.
pub trait Float<B: Buffer<Token=u8>>: Sized {
    /// Given an input and a buffer matching `/[+-]?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)/`,
    /// convert this buffer into the proper float-representation, error if it is not possible
    /// to determine the correct representation.
    ///
    /// NOTES:
    ///
    /// * Unsafe because the `parse_buffer` implementation should be able to rely on the format of
    ///   the incoming buffer (including well-formed UTF-8).
    unsafe fn parse_buffer<I: Input<Token=u8, Buffer=B>>(i: I, b: B) -> SimpleResult<I, Self>;
}

/// Only use the generic `Float` impl if we can rely on `Vec`.
#[cfg(feature="std")]
mod float_impl {
    use std::str;

    use types::{Buffer, Input};
    use parsers::{Error, SimpleResult};

    use super::Float;

    /// The macro here is to provide the default keyword in case we support specialization
    #[cfg(has_specialization)]
    macro_rules! parse_buffer {
        ( $i:ident, $b:ident: $b_ty:ty, $content:block ) => {
            default unsafe fn parse_buffer<I: Input<Token=u8>>($i: I, $b: $b_ty) -> SimpleResult<I, Self> $content
        }
    }

    #[cfg(not(has_specialization))]
    macro_rules! parse_buffer {
        ( $i:ident, $b:ident: $b_ty:ty, $content:block ) => {
            unsafe fn parse_buffer<I: Input<Token=u8>>($i: I, $b: $b_ty) -> SimpleResult<I, Self> $content
        }
    }

    impl<B> Float<B> for f64
      where B: Buffer<Token=u8> {
        parse_buffer!(i, b: B, {
            let v = b.into_vec();

            // v only contains [-+0-9.eE], UTF-8 safe
            let s: &str = str::from_utf8_unchecked(&v[..]);

            // We can skip this Result if we can guarantee that: a) the float is well-formatted, and b) the
            // float is not too large (ie. larger than what Rust's FromStr implementation can support).
            //
            // In this case we cannot wholly guarantee the size, so in that case we error (note that
            // the error is placed after the float in this case).
            if let Ok(f) = s.parse() {
                i.ret(f)
            } else {
                // TODO: Add FloatParseError to Error type?
                i.err(Error::unexpected())
            }
        });
    }

    impl<B> Float<B> for f32
      where B: Buffer<Token=u8> {
        parse_buffer!(i, b: B, {
            let v       = b.into_vec();
            let s: &str = str::from_utf8_unchecked(&v[..]);

            if let Ok(f) = s.parse() {
                i.ret(f)
            } else {
                // TODO: Add FloatParseError to Error type?
                i.err(Error::unexpected())
            }
        });
    }
}

/// Internal module containing specialized implementations of `Float` for `&[u8]`-buffers, used
/// when `has_specialization` is on since we can enable the unstable `specialization` feature.
/// We also use this when not using `std` since the default implementation is not provided since it
/// relies on `Vec`.
#[cfg(any(has_specialization, not(feature="std")))]
mod float_impl_specialized {
    use std::str;

    use types::Input;
    use parsers::{Error, SimpleResult};

    use super::Float;

    impl<'a> Float<&'a [u8]> for f64 {
        unsafe fn parse_buffer<I: Input<Token=u8>>(i: I, b: &'a [u8]) -> SimpleResult<I, Self> {
            let s: &str = str::from_utf8_unchecked(b);

            if let Ok(f) = s.parse() {
                i.ret(f)
            } else {
                // TODO: Add FloatParseError to Error type?
                i.err(Error::unexpected())
            }
        }
    }

    impl<'a> Float<&'a [u8]> for f32 {
        unsafe fn parse_buffer<I: Input<Token=u8>>(i: I, b: &'a [u8]) -> SimpleResult<I, Self> {
            let s: &str = str::from_utf8_unchecked(b);

            if let Ok(f) = s.parse() {
                i.ret(f)
            } else {
                // TODO: Add FloatParseError to Error type?
                i.err(Error::unexpected())
            }
        }
    }
}

/// Matches a floating point number in base-10 with an optional exponent, returning a buffer.
///
/// Matches `/[+-]?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)/`
#[inline]
pub fn match_float<I: Input<Token=u8>>(i: I) -> SimpleResult<I, I::Buffer> {
    /// Parses a sign
    #[inline]
    fn sign<I: Input<Token=u8>>(i: I) -> SimpleResult<I, u8> {
        or(i, |i| token(i, b'+'), |i| token(i, b'-'))
    }

    /// Parses a signed decimal with optional leading sign
    #[inline]
    fn signed_decimal<I: Input<Token=u8>>(i: I) -> SimpleResult<I, ()> {
        option(i, sign, b'+').then(|i| skip_while1(i, is_digit))
    }

    /// Parses e or E
    #[inline]
    fn e<I: Input<Token=u8>>(i: I) -> SimpleResult<I, u8> {
        or(i, |i| token(i, b'e'), |i| token(i, b'E'))
    }

    matched_by(i, |i|
        signed_decimal(i).then(|i|
        option(i, |i| token(i, b'.').then(|i| skip_while1(i, is_digit)), ()).then(|i|
        option(i, |i| e(i).then(signed_decimal), ())))).map(|(b, _)| b)
}

// TODO: Maybe we can use specialization to avoid allocation by specializing for a Buffer=&[u8]
/// Parses a float into a `f64` or `f32`, will error with an `Error::unexpected` if the float
/// does not map to a proper float.
///
/// Supports the format `/[+-]?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)/`
///
/// NOTE: Currently requires an allocation due to being generic over `Input::Buffer` and
/// internally Rust's `f32` requires a `&str` to be able to parse. If the nightly compiler is used
/// the `Float` trait implementation for `f32` and `f64` will be specialized if the `Buffer` is
/// `&[u8]` and will not require an allocation.
///
/// ```
/// use chomp::parse_only;
/// use chomp::ascii::float;
///
/// assert_eq!(parse_only(float, &b"3.14159265359"[..]), Ok(3.14159265359));
/// ```
pub fn float<I: Input<Token=u8>, F: Float<I::Buffer>>(i: I) -> SimpleResult<I, F> {
    match_float(i).bind(|i, b| unsafe { F::parse_buffer(i, b) })
}

#[inline]
fn compare_ci(a: u8, b: u8) -> bool {
    (match a {
        b'A'...b'Z' => a | 0x20,
        x           => x
    } == match b {
        b'A'...b'Z' => b | 0x20,
        x           => x
    })
}

/// Matches the given slice against the parser in a case-insensitive manner, returning the matched
/// slice upon success. Only respects ASCII characters for the case-insensitive comparison.
///
/// If the length of the contained data is shorter than the given slice this parser is considered
/// incomplete.
///
/// ```
/// use chomp::prelude::parse_only;
/// use chomp::ascii::string_ci;
///
/// assert_eq!(parse_only(|i| string_ci(i, b"abc"), b"abcdef"), Ok(&b"abc"[..]));
/// assert_eq!(parse_only(|i| string_ci(i, b"abc"), b"aBCdef"), Ok(&b"aBC"[..]));
/// ```
pub fn string_ci<I: Input<Token=u8>>(mut i: I, s: &'static [u8]) -> SimpleResult<I, I::Buffer> {
    use primitives::Primitives;

    let mut n = 0;
    let len   = s.len();

    // TODO: There has to be some more efficient way here
    let b = i.consume_while(|c| {
        if n >= len || !compare_ci(c, s[n]) {
            false
        }
        else {
            n += 1;

            true
        }
    });

    if n >= len {
        i.ret(b)
    } else {
        i.err(Error::expected(s[n]))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::{compare_ci, to_decimal, string_ci};
    use parsers::Error;
    use primitives::IntoInner;

    macro_rules! test_to_decimal {
        ( $($n:ty),+ ) => { $(
            assert_eq!(to_decimal::<$n, _>(&b""[..]), 0);
            assert_eq!(to_decimal::<$n, _>(&b"0"[..]), 0);
            assert_eq!(to_decimal::<$n, _>(&b"1"[..]), 1);
            assert_eq!(to_decimal::<$n, _>(&b"2"[..]), 2);
            assert_eq!(to_decimal::<$n, _>(&b"10"[..]), 10);
            assert_eq!(to_decimal::<$n, _>(&b"20"[..]), 20);
            assert_eq!(to_decimal::<$n, _>(&b"25"[..]), 25);
        )+ }
    }

    #[test]
    fn test_to_decimal_u8() {
        test_to_decimal!(u8, u16, u32, u64, i16, i32, i64);
    }

    #[test]
    fn match_float_test() {
        assert_eq!(match_float(&b"abc"[..]).into_inner(),           (&b"abc"[..], Err(Error::unexpected())));
        assert_eq!(match_float(&b"1.0e+1"[..]).into_inner(),        (&b""[..], Ok(&b"1.0e+1"[..])));
        assert_eq!(match_float(&b"1.0e1"[..]).into_inner(),         (&b""[..], Ok(&b"1.0e1"[..])));
        assert_eq!(match_float(&b"1e1"[..]).into_inner(),           (&b""[..], Ok(&b"1e1"[..])));
        assert_eq!(match_float(&b"3.12159265359"[..]).into_inner(), (&b""[..], Ok(&b"3.12159265359"[..])));
        assert_eq!(match_float(&b"1.0"[..]).into_inner(),           (&b""[..], Ok(&b"1.0"[..])));
        assert_eq!(match_float(&b"1"[..]).into_inner(),             (&b""[..], Ok(&b"1"[..])));
        assert_eq!(match_float(&b"1."[..]).into_inner(),            (&b"."[..], Ok(&b"1"[..])));
        assert_eq!(match_float(&b"1.."[..]).into_inner(),           (&b".."[..], Ok(&b"1"[..])));
        assert_eq!(match_float(&b"1.abc"[..]).into_inner(),         (&b".abc"[..], Ok(&b"1"[..])));
        assert_eq!(match_float(&b"0.234"[..]).into_inner(),         (&b""[..], Ok(&b"0.234"[..])));
        assert_eq!(match_float(&b"0.234e-123"[..]).into_inner(),    (&b""[..], Ok(&b"0.234e-123"[..])));
        assert_eq!(match_float(&b"0.234e-123  "[..]).into_inner(),  (&b"  "[..], Ok(&b"0.234e-123"[..])));
        assert_eq!(match_float(&b"0.234e-123ee"[..]).into_inner(),  (&b"ee"[..], Ok(&b"0.234e-123"[..])));
        assert_eq!(match_float(&b"0.234e-123.."[..]).into_inner(),  (&b".."[..], Ok(&b"0.234e-123"[..])));
        assert_eq!(match_float(&b"0.234e-.."[..]).into_inner(),     (&b"e-.."[..], Ok(&b"0.234"[..])));
    }

    #[test]
    fn float_test() {
        assert_eq!(float(&b"3.14159265359"[..]).into_inner(), (&b""[..], Ok(3.14159265359)));
        assert_eq!(float(&b"+3.14159265359"[..]).into_inner(), (&b""[..], Ok(3.14159265359)));
        assert_eq!(float(&b"-3.14159265359"[..]).into_inner(), (&b""[..], Ok(-3.14159265359)));
        assert_eq!(float(&b"0.0"[..]).into_inner(), (&b""[..], Ok(0.0)));
        assert_eq!(float(&b"0"[..]).into_inner(), (&b""[..], Ok(0.0)));
        assert_eq!(float(&b"1"[..]).into_inner(), (&b""[..], Ok(1.0)));
        assert_eq!(float(&b"1E0"[..]).into_inner(), (&b""[..], Ok(1.0)));
        assert_eq!(float(&b"1E1"[..]).into_inner(), (&b""[..], Ok(10.0)));
        assert_eq!(float(&b"1E2"[..]).into_inner(), (&b""[..], Ok(100.0)));
        assert_eq!(float(&b"1e0"[..]).into_inner(), (&b""[..], Ok(1.0)));
        assert_eq!(float(&b"1e1"[..]).into_inner(), (&b""[..], Ok(10.0)));
        assert_eq!(float(&b"1e2"[..]).into_inner(), (&b""[..], Ok(100.0)));
        assert_eq!(float(&b"2E2"[..]).into_inner(), (&b""[..], Ok(200.0)));
        assert_eq!(float(&b"2e2"[..]).into_inner(), (&b""[..], Ok(200.0)));
        assert_eq!(float(&b"1E-0"[..]).into_inner(), (&b""[..], Ok(1.0)));
        assert_eq!(float(&b"1E-1"[..]).into_inner(), (&b""[..], Ok(0.1)));
        assert_eq!(float(&b"1E-2"[..]).into_inner(), (&b""[..], Ok(0.01)));
        assert_eq!(float(&b"1e-0"[..]).into_inner(), (&b""[..], Ok(1.0)));
        assert_eq!(float(&b"1e-1"[..]).into_inner(), (&b""[..], Ok(0.1)));
        assert_eq!(float(&b"1e-2"[..]).into_inner(), (&b""[..], Ok(0.01)));
    }

    #[test]
    fn compare_ci_test() {
        assert!(compare_ci(b'a', b'a'));
        assert!(compare_ci(b'a', b'A'));
        assert!(compare_ci(b'b', b'b'));
        assert!(compare_ci(b'b', b'B'));
        assert!(compare_ci(b'y', b'y'));
        assert!(compare_ci(b'y', b'Y'));
        assert!(compare_ci(b'z', b'z'));
        assert!(compare_ci(b'z', b'Z'));

        for i in 0..127 {
            for j in 0..127 {
                let eq = match i {
                    b'A'...b'Z' => i | 0x20,
                    x           => x
                } == match j {
                    b'A'...b'Z' => j | 0x20,
                    x           => x
                };

                assert_eq!(eq, compare_ci(i, j), "{} {} failed", i, j);
            }
        }
    }

    #[test]
    fn string_ci_test() {
        assert_eq!(string_ci(&b""[..],    b""     ).into_inner(), (&b""[..],    Ok(&b""[..])));
        assert_eq!(string_ci(&b""[..],    b"a"    ).into_inner(), (&b""[..],    Err(Error::expected(b'a'))));
        assert_eq!(string_ci(&b"a"[..],   b"a"    ).into_inner(), (&b""[..],    Ok(&b"a"[..])));
        assert_eq!(string_ci(&b"b"[..],   b"a"    ).into_inner(), (&b"b"[..],   Err(Error::expected(b'a'))));
        assert_eq!(string_ci(&b"abc"[..], b"a"    ).into_inner(), (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(string_ci(&b"abc"[..], b"ab"   ).into_inner(), (&b"c"[..],   Ok(&b"ab"[..])));
        assert_eq!(string_ci(&b"abc"[..], b"abc"  ).into_inner(), (&b""[..],    Ok(&b"abc"[..])));
        assert_eq!(string_ci(&b"abc"[..], b"abcd" ).into_inner(), (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string_ci(&b"abc"[..], b"abcde").into_inner(), (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string_ci(&b"abc"[..], b"ac"   ).into_inner(), (&b"bc"[..],  Err(Error::expected(b'c'))));

        assert_eq!(string_ci(&b""[..],    b""     ).into_inner(), (&b""[..],    Ok(&b""[..])));
        assert_eq!(string_ci(&b""[..],    b"a"    ).into_inner(), (&b""[..],    Err(Error::expected(b'a'))));
        assert_eq!(string_ci(&b"A"[..],   b"a"    ).into_inner(), (&b""[..],    Ok(&b"A"[..])));
        assert_eq!(string_ci(&b"B"[..],   b"a"    ).into_inner(), (&b"B"[..],   Err(Error::expected(b'a'))));
        assert_eq!(string_ci(&b"ABC"[..], b"a"    ).into_inner(), (&b"BC"[..],  Ok(&b"A"[..])));
        assert_eq!(string_ci(&b"ABC"[..], b"ab"   ).into_inner(), (&b"C"[..],   Ok(&b"AB"[..])));
        assert_eq!(string_ci(&b"ABC"[..], b"abc"  ).into_inner(), (&b""[..],    Ok(&b"ABC"[..])));
        assert_eq!(string_ci(&b"ABC"[..], b"abcd" ).into_inner(), (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string_ci(&b"ABC"[..], b"abcde").into_inner(), (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string_ci(&b"ABC"[..], b"ac"   ).into_inner(), (&b"BC"[..],  Err(Error::expected(b'c'))));

        assert_eq!(string_ci(&b"{|}"[..], b"{|}"  ).into_inner(), (&b""[..],     Ok(&b"{|}"[..])));
        assert_eq!(string_ci(&b"[\\]"[..],b"{|}"  ).into_inner(), (&b"[\\]"[..], Err(Error::expected(b'{'))));
        assert_eq!(string_ci(&b"[\\]"[..],b"[\\]" ).into_inner(), (&b""[..],     Ok(&b"[\\]"[..])));
        assert_eq!(string_ci(&b"{|}"[..], b"[\\]" ).into_inner(), (&b"{|}"[..],  Err(Error::expected(b'['))));

        assert_eq!(string_ci("äbc".as_bytes(), "ä".as_bytes()).into_inner(), (&b"bc"[..],  Ok("ä".as_bytes())));
        // We need to slice a bit, since the first byte of the two-byte ä and Ä are is the same,
        // so that one will match
        assert_eq!(string_ci("ÄBC".as_bytes(), "ä".as_bytes()).into_inner(), (&"ÄBC".as_bytes()[1..], Err(Error::expected("ä".as_bytes()[1]))));

        assert_eq!(string_ci(&b"125"[..], b"125").into_inner(), (&b""[..],    Ok(&b"125"[..])));
    }
}
