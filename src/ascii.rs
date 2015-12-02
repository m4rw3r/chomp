//! Utilities and parsers for dealing with ASCII data in `u8` format.

use conv::{NoError, ValueFrom};
use conv::errors::UnwrapOk;

use std::ops::{Add, Mul};

use {Input, U8Result};
use parsers::{take_while, take_while1, satisfy};

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
/// use chomp::Input;
/// use chomp::ascii::skip_whitespace;
///
/// let i = Input::new(b" \t ");
///
/// assert_eq!(skip_whitespace(i).unwrap(), ());
/// ```
#[inline]
pub fn skip_whitespace(i: Input<u8>) -> U8Result<()> {
    take_while(i, is_whitespace).map(|_| ())
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
/// use chomp::Input;
/// use chomp::ascii::digit;
///
/// let i = Input::new(b"1");
///
/// let r = digit(i);
///
/// assert_eq!(r.unwrap(), b'1');
/// ```
#[inline]
pub fn digit(i: Input<u8>) -> U8Result<u8> {
    satisfy(i, is_digit)
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
/// use chomp::Input;
/// use chomp::ascii::decimal;
///
/// let i = Input::new(b"123");
///
/// let r = decimal::<u8>(i);
///
/// assert_eq!(r.unwrap(), 123u8);
/// ```
#[inline]
pub fn decimal<T: Copy + ValueFrom<u8, Err=NoError> + Add<Output=T> + Mul<Output=T>>(i: Input<u8>) -> U8Result<T> {
    take_while1(i, is_digit).bind(|i, buf| i.ret(to_decimal(buf)))
}

/// Internal function converting a `[u8]` to the given integer type `T`.
///
/// # Notes
///
/// * The slice must not contain any other characters besides 0 to 9.
/// * The `T` type must be larger than `u8` if it is signed.
#[inline]
fn to_decimal<T: Copy + ValueFrom<u8, Err=NoError> + Add<Output=T> + Mul<Output=T>>(buf: &[u8]) -> T {
    buf.iter().fold(T::value_from(0).unwrap_ok(), |a, n| a * T::value_from(10).unwrap_ok() + T::value_from(n - b'0').unwrap_ok())
}

#[cfg(test)]
mod test {
    use super::to_decimal;

    macro_rules! test_to_decimal {
        ( $($n:ty),+ ) => { $(
            assert_eq!(to_decimal::<$n>(b""), 0);
            assert_eq!(to_decimal::<$n>(b"0"), 0);
            assert_eq!(to_decimal::<$n>(b"1"), 1);
            assert_eq!(to_decimal::<$n>(b"2"), 2);
            assert_eq!(to_decimal::<$n>(b"10"), 10);
            assert_eq!(to_decimal::<$n>(b"20"), 20);
            assert_eq!(to_decimal::<$n>(b"25"), 25);
        )+ }
    }

    #[test]
    fn test_to_decimal_u8() {
        test_to_decimal!(u8, u16, u32, u64, i16, i32, i64);
    }
}
