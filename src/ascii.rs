//! Utilities and parsers for dealing with ASCII data in `u8` format.

use std::ops::{Add, Mul};

use conv::{
    NoError,
    ValueFrom,
};
use conv::errors::UnwrapOk;

use combinators::option;
use parsers::{Error, satisfy, skip_while, take_while1};
use types::{Buffer, Input, Parser};

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
/// assert_eq!(parse_only(skip_whitespace(), b" \t "), Ok(()));
/// ```
#[inline]
pub fn skip_whitespace<I: Input<Token=u8>>() -> impl Parser<I, Output=(), Error=Error<u8>> {
    skip_while(is_whitespace)
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
/// assert_eq!(parse_only(digit(), b"1"), Ok(b'1'));
/// ```
#[inline]
pub fn digit<I: Input<Token=u8>>() -> impl Parser<I, Output=u8, Error=Error<u8>> {
    satisfy(is_digit)
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
/// let r: Result<i16, _> = parse_only(signed(decimal()), b"-123");
///
/// assert_eq!(r, Ok(-123i16));
/// ```
#[inline]
pub fn signed<I: Input<Token=u8>, T, F>(f: F) -> impl Parser<I, Output=T, Error=Error<u8>>
  where T: Copy + ValueFrom<i8, Err=NoError> + Add<Output=T> + Mul<Output=T>,
        F: Parser<I, Output=T, Error=Error<u8>> {
    option(
        satisfy(|c| c == b'-' || c == b'+').map(|s| T::value_from(if s == b'+' { 1 } else { -1 }).unwrap_ok()),
        T::value_from(1).unwrap_ok())
        .bind(|sign| f.map(move |num| sign * num))
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
/// let r = parse_only(decimal::<_, u8>(), b"123");
///
/// assert_eq!(r, Ok(123u8));
/// ```
#[inline]
pub fn decimal<I, T>() -> impl Parser<I, Output=T, Error=Error<u8>>
  where I: Input<Token=u8>,
        T: Copy + ValueFrom<u8, Err=NoError> + Add<Output=T> + Mul<Output=T> {
    take_while1(is_digit).map(to_decimal)
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
/// assert_eq!(parse_only(string_ci(b"abc"), b"abcdef"), Ok(&b"abc"[..]));
/// assert_eq!(parse_only(string_ci(b"abc"), b"aBCdef"), Ok(&b"aBC"[..]));
/// ```
pub fn string_ci<I: Input<Token=u8>>(s: &'static [u8]) -> impl Parser<I, Output=I::Buffer, Error=Error<u8>> {
    move |mut i: I| {
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
            (i, Ok(b))
        } else {
            (i, Err(Error::expected(s[n])))
        }
    }
}


#[cfg(test)]
mod test {
    use super::{compare_ci, to_decimal, string_ci};
    use types::Parser;
    use parsers::Error;

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
        assert_eq!(string_ci(b""     ).parse(&b""[..]),    (&b""[..],    Ok(&b""[..])));
        assert_eq!(string_ci(b"a"    ).parse(&b""[..]),    (&b""[..],    Err(Error::expected(b'a'))));
        assert_eq!(string_ci(b"a"    ).parse(&b"a"[..]),   (&b""[..],    Ok(&b"a"[..])));
        assert_eq!(string_ci(b"a"    ).parse(&b"b"[..]),   (&b"b"[..],   Err(Error::expected(b'a'))));
        assert_eq!(string_ci(b"a"    ).parse(&b"abc"[..]), (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(string_ci(b"ab"   ).parse(&b"abc"[..]), (&b"c"[..],   Ok(&b"ab"[..])));
        assert_eq!(string_ci(b"abc"  ).parse(&b"abc"[..]), (&b""[..],    Ok(&b"abc"[..])));
        assert_eq!(string_ci(b"abcd" ).parse(&b"abc"[..]), (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string_ci(b"abcde").parse(&b"abc"[..]), (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string_ci(b"ac"   ).parse(&b"abc"[..]), (&b"bc"[..],  Err(Error::expected(b'c'))));

        assert_eq!(string_ci(b""     ).parse(&b""[..]),    (&b""[..],    Ok(&b""[..])));
        assert_eq!(string_ci(b"a"    ).parse(&b""[..]),    (&b""[..],    Err(Error::expected(b'a'))));
        assert_eq!(string_ci(b"a"    ).parse(&b"A"[..]),   (&b""[..],    Ok(&b"A"[..])));
        assert_eq!(string_ci(b"a"    ).parse(&b"B"[..]),   (&b"B"[..],   Err(Error::expected(b'a'))));
        assert_eq!(string_ci(b"a"    ).parse(&b"ABC"[..]), (&b"BC"[..],  Ok(&b"A"[..])));
        assert_eq!(string_ci(b"ab"   ).parse(&b"ABC"[..]), (&b"C"[..],   Ok(&b"AB"[..])));
        assert_eq!(string_ci(b"abc"  ).parse(&b"ABC"[..]), (&b""[..],    Ok(&b"ABC"[..])));
        assert_eq!(string_ci(b"abcd" ).parse(&b"ABC"[..]), (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string_ci(b"abcde").parse(&b"ABC"[..]), (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string_ci(b"ac"   ).parse(&b"ABC"[..]), (&b"BC"[..],  Err(Error::expected(b'c'))));

        assert_eq!(string_ci(b"{|}"   ).parse(&b"{|}"[..]),  (&b""[..],     Ok(&b"{|}"[..])));
        assert_eq!(string_ci(b"{|}"   ).parse(&b"[\\]"[..]), (&b"[\\]"[..], Err(Error::expected(b'{'))));
        assert_eq!(string_ci(b"[\\]"  ).parse(&b"[\\]"[..]), (&b""[..],     Ok(&b"[\\]"[..])));
        assert_eq!(string_ci(b"[\\]"  ).parse(&b"{|}"[..]),  (&b"{|}"[..],  Err(Error::expected(b'['))));

        assert_eq!(string_ci("ä".as_bytes()    ).parse("äbc".as_bytes()), (&b"bc"[..],  Ok("ä".as_bytes())));
        // We need to slice a bit, since the first byte of the two-byte ä and Ä are is the same,
        // so that one will match
        assert_eq!(string_ci("ä".as_bytes()    ).parse("ÄBC".as_bytes()), (&"ÄBC".as_bytes()[1..], Err(Error::expected("ä".as_bytes()[1]))));

        assert_eq!(string_ci(b"125"  ).parse(&b"125"[..]), (&b""[..],    Ok(&b"125"[..])));
    }
}
