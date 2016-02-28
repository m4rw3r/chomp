//! Basic parsers.

use std::mem;
use std::any;
use std::error;
use std::fmt;

use input::Input;
use parse_result::SimpleResult;
use primitives::InputBuffer;

/// Matches any item, returning it if present.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::{parse_only, any};
///
/// assert_eq!(parse_only(any, b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn any<I: Copy>(i: Input<I>) -> SimpleResult<I, I> {
    let b = i.buffer();

    match b.first() {
        None     => i.incomplete(1),
        Some(&c) => i.replace(&b[1..]).ret(c),
    }
}

/// Matches an item using ``f``, the item is returned if ``f`` yields true, otherwise this parser
/// fails.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::{parse_only, satisfy};
///
/// assert_eq!(parse_only(|i| satisfy(i, |c| c == b'a'), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn satisfy<I: Copy, F>(i: Input<I>, f: F) -> SimpleResult<I, I>
  where F: FnOnce(I) -> bool {
    let b = i.buffer();

    match b.first() {
        None             => i.incomplete(1),
        Some(&c) if f(c) => i.replace(&b[1..]).ret(c),
        Some(_)          => i.err(err::unexpected()),
    }
}

/// Reads a single token, applies the transformation `F` and then succeeds with the transformed
/// valeue if the predicate `P` yields true on this transformed value.
///
/// ```
/// use std::ascii::AsciiExt;
///
/// use chomp::{parse_only, satisfy_with};
///
/// let r = parse_only(
///     |i| satisfy_with(i, |c| AsciiExt::to_ascii_uppercase(&c), |c| c == b'T'),
///     b"testing");
///
/// assert_eq!(r, Ok(b'T'));
/// ```
#[inline]
pub fn satisfy_with<I: Copy, T: Clone, F, P>(i: Input<I>, f: F, p: P) -> SimpleResult<I, T>
  where F: FnOnce(I) -> T,
        P: FnOnce(T) -> bool {
    let b = i.buffer();

    match b.first().cloned() {
        Some(n) => {
            let t = f(n);

            if p(t.clone()) {
                i.replace(&b[1..]).ret(t)
            } else {
                i.err(err::unexpected())
            }
        },
        None    => i.incomplete(1),
    }
}

/// Matches a single token, returning the match on success.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::{parse_only, token};
///
/// assert_eq!(parse_only(|i| token(i, b'a'), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn token<I: Copy + PartialEq>(i: Input<I>, t: I) -> SimpleResult<I, I> {
    let b = i.buffer();

    match b.first() {
        None               => i.incomplete(1),
        Some(&c) if t == c => i.replace(&b[1..]).ret(c),
        Some(_)            => i.err(err::expected(t)),
    }
}

/// Matches a single token as long as it is not equal to `t`, returning the match on success.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::{parse_only, not_token};
///
/// assert_eq!(parse_only(|i| not_token(i, b'b'), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn not_token<I: Copy + PartialEq>(i: Input<I>, t: I) -> SimpleResult<I, I> {
    let b = i.buffer();

    match b.first() {
        None               => i.incomplete(1),
        Some(&c) if t != c => i.replace(&b[1..]).ret(c),
        Some(_)            => i.err(err::unexpected()),
    }
}

/// Matches any item but does not consume it, on success it gives ``Some`` but if no input remains
/// ``None`` is produced.
///
/// This parser is never considered incomplete.
///
/// ```
/// use chomp::{parse_only, peek};
///
/// assert_eq!(parse_only(peek, b"abc"), Ok(Some(b'a')));
///
/// assert_eq!(parse_only(peek, b""), Ok(None));
/// ```
#[inline]
pub fn peek<I: Copy>(i: Input<I>) -> SimpleResult<I, Option<I>> {
    let d = i.buffer().first().cloned();

    i.ret(d)
}

/// Matches any item but does not consume it.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::{parse_only, peek_next};
///
/// assert_eq!(parse_only(peek_next, b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn peek_next<I: Copy>(i: Input<I>) -> SimpleResult<I, I> {
    match i.buffer().first().cloned() {
        None    => i.incomplete(1),
        Some(c) => i.ret(c),
    }
}

/// Matches ``num`` items no matter what they are, returning a slice of the matched items.
///
/// If the buffer length is less than ``num`` this parser is considered incomplete.
///
/// ```
/// use chomp::{parse_only, take};
///
/// assert_eq!(parse_only(|i| take(i, 3), b"abcd"), Ok(&b"abc"[..]));
/// ```
#[inline]
pub fn take<I: Copy>(i: Input<I>, num: usize) -> SimpleResult<I, &[I]> {
    let b = i.buffer();

    if num <= b.len() {
        i.replace(&b[num..]).ret(&b[..num])
    } else {
        i.incomplete(num - b.len())
    }
}

/// Matches all items while ``f`` returns false, returns a slice of all the matched items.
///
/// If no failure can be found the parser will be considered to be incomplete as there might be
/// more input which needs to be matched.
///
/// ```
/// use chomp::{parse_only, take_while};
///
/// let r = parse_only(|i| take_while(i, |c| c == b'a' || c == b'b'), b"abcdcba");
///
/// assert_eq!(r, Ok(&b"ab"[..]));
/// ```
///
/// Without managing to match anything:
///
/// ```
/// use chomp::{parse_only, take_while};
///
/// let r = parse_only(|i| take_while(i, |c| c == b'z'), b"abcdcba");
///
/// assert_eq!(r, Ok(&b""[..]));
/// ```
#[inline]
pub fn take_while<I: Copy, F>(i: Input<I>, f: F) -> SimpleResult<I, &[I]>
  where F: Fn(I) -> bool {
    let b = i.buffer();

    match b.iter().position(|c| f(*c) == false) {
        Some(n) => i.replace(&b[n..]).ret(&b[..n]),
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => if i.is_last_slice() {
            // Last slice and we have just read everything of it, replace with zero-sized slice:
            // Hack to avoid branch and overflow, does not matter where this zero-sized slice is
            // allocated
            i.replace(&b[..0]).ret(b)
        } else {
            i.incomplete(1)
        },
    }
}

/// Matches all items while ``f`` returns true, if at least one item matched this parser succeeds
/// and returns a slice of all the matched items.
///
/// If no failure can be found the parser will be considered to be incomplete as there might be
/// more input which needs to be matched. If zero items were matched an error will be returned.
///
/// ```
/// use chomp::{parse_only, take_while1};
///
/// let r = parse_only(|i| take_while1(i, |c| c == b'a' || c == b'b'), b"abcdcba");
///
/// assert_eq!(r, Ok(&b"ab"[..]));
/// ```
#[inline]
pub fn take_while1<I: Copy, F>(i: Input<I>, f: F) -> SimpleResult<I, &[I]>
  where F: Fn(I) -> bool {
    let b = i.buffer();

    match b.iter().position(|c| f(*c) == false) {
        Some(0) => i.err(err::unexpected()),
        Some(n) => i.replace(&b[n..]).ret(&b[..n]),
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => if b.len() > 0 && i.is_last_slice() {
            // Last slice and we have just read everything of it, replace with zero-sized slice:
            // Hack to avoid branch and overflow, does not matter where this zero-sized slice is
            // allocated
            i.replace(&b[..0]).ret(b)
        } else {
            i.incomplete(1)
        },
    }
}

/// Matches all items until ``f`` returns true, all items to that point will be returned as a slice
/// upon success.
///
/// If no failure can be found the parser will be considered to be incomplete as there might be
/// more input which needs to be matched.
///
/// ```
/// use chomp::{parse_only, take_till};
///
/// let r = parse_only(|i| take_till(i, |c| c == b'd'), b"abcdef");
///
/// assert_eq!(r, Ok(&b"abc"[..]));
/// ```
#[inline]
pub fn take_till<I: Copy, F>(i: Input<I>, f: F) -> SimpleResult<I, &[I]>
  where F: Fn(I) -> bool {
    let b = i.buffer();

    match b.iter().cloned().position(f) {
        Some(n) => i.replace(&b[n..]).ret(&b[0..n]),
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => i.incomplete(1),
    }
}

/// The predicate consumes and transforms a state argument, this parser will match everything until
/// the predicate returns `None`.
///
/// ```
/// use chomp::{parse_only, scan};
///
/// let p = |i| scan(i, false, |s, c| match (s, c) {
///     (true, b'/') => None,
///     (_,    b'*') => Some(true),
///     (_, _)       => Some(false),
/// });
///
/// assert_eq!(parse_only(p, b"/*test*of*scan*/ foo"), Ok(&b"/*test*of*scan*"[..]));
/// ```
#[inline]
pub fn scan<I: Copy, S, F>(i: Input<I>, s: S, mut f: F) -> SimpleResult<I, &[I]>
  where F: FnMut(S, I) -> Option<S> {
    let b         = i.buffer();
    let mut state = Some(s);

    match b.iter().position(|&c| { state = f(mem::replace(&mut state, None).unwrap(), c); state.is_none()}) {
        Some(n) => i.replace(&b[n..]).ret(&b[0..n]),
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => i.incomplete(1),
    }
}

/// Like `scan` but generalized to return the final state of the scanner.
///
/// ```
/// use chomp::{parse_only, run_scanner};
///
/// let p = |i| run_scanner(i, 0, |s, c| match (s, c) {
///     (b'*', b'/') => None,
///     (_,    c)    => Some(c),
/// });
///
/// assert_eq!(parse_only(p, b"/*test*of*scan*/ foo"), Ok((&b"/*test*of*scan*"[..], b'*')));
/// ```
#[inline]
// TODO: Remove Copy bound on S
pub fn run_scanner<I: Copy, S: Copy, F>(i: Input<I>, s: S, mut f: F) -> SimpleResult<I, (&[I], S)>
  where F: FnMut(S, I) -> Option<S> {
    let b         = i.buffer();
    let mut state = s;

    match b.iter().position(|&c| { let t = f(state, c); match t { None => true, Some(v) => { state = v; false } } }) {
        Some(n) => i.replace(&b[n..]).ret((&b[0..n], state)),
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => i.incomplete(1),
    }
}

/// Matches the remainder of the buffer and returns it, always succeeds.
///
/// ```
/// use chomp::{parse_only, take_remainder};
///
/// assert_eq!(parse_only(take_remainder, b"abcd"), Ok(&b"abcd"[..]));
/// ```
#[inline]
pub fn take_remainder<I: Copy>(i: Input<I>) -> SimpleResult<I, &[I]> {
    let b = i.buffer();
    // Last slice and we have just read everything of it, replace with zero-sized slice:
    //
    // Hack to avoid branch and overflow, does not matter where this zero-sized slice is
    // allocated as long as it is the same origin slice
    i.replace(&b[..0]).ret(b)
}

/// Matches the given slice against the parser, returning the matched slice upon success.
///
/// If the length of the contained data is shorter than the given slice this parser is considered
/// incomplete.
///
/// ```
/// use chomp::{parse_only, string};
///
/// assert_eq!(parse_only(|i| string(i, b"abc"), b"abcdef"), Ok(&b"abc"[..]));
/// ```
#[inline]
pub fn string<'a, 'b, I: Copy + PartialEq>(i: Input<'a, I>, s: &'b [I])
    -> SimpleResult<'a, I, &'a [I]> {
    let b = i.buffer();

    if s.len() > b.len() {
        return i.incomplete(s.len() - b.len());
    }

    let d = &b[..s.len()];

    for j in 0..s.len() {
        if s[j] != d[j] {
            return i.replace(&b[j..]).err(Error::Expected(d[j]))
        }
    }

    i.replace(&b[s.len()..]).ret(d)
}

/// Matches the end of the input.
///
/// ```
/// use chomp::{parse_only, token, eof};
///
/// let r = parse_only(|i| token(i, b'a').then(eof), b"a");
///
/// assert_eq!(r, Ok(()));
/// ```
#[inline]
pub fn eof<I>(i: Input<I>) -> SimpleResult<I, ()> {
    if i.buffer().len() == 0 && i.is_last_slice() {
        i.ret(())
    } else {
        i.err(err::unexpected())
    }
}

/// Common error for the basic Chomp parsers, verbose version.
///
/// This is a verbose version of the common error for the basic Chomp parsers. It will contain
/// information about what a parser expected or if it encountered something unexpected (in the
/// case of user supplied predicates, eg. `satisfy`).
///
/// This is coupled with the state found in the error state of the `ParseResult` type.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Error<I> {
    /// Expected a specific token
    Expected(I),
    /// Did not expect the token present in the input stream
    Unexpected,
}

impl<I> Error<I> {
    /// Creates a new Unexpected error.
    ///
    /// Should be used when the error value is not important.
    pub fn new() -> Self {
        Error::Unexpected
    }
}

impl<I> fmt::Display for Error<I>
  where I: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Expected(ref c) => write!(f, "expected {:?}", *c),
            Error::Unexpected      => write!(f, "unexpected"),
        }
    }
}

impl<I: any::Any + fmt::Debug> error::Error for Error<I> {
    fn description(&self) -> &str {
        match *self {
            Error::Expected(_) => "expected a certain token, received another",
            Error::Unexpected  => "received an unexpected token",
        }
    }
}

mod err {
    //! This is a private module to contain the constructors for the verbose error type.
    //!
    //! All constructors are #[inline(always)] and will construct the appropriate error type.

    use super::Error;

    #[inline(always)]
    pub fn unexpected<I>() -> Error<I> {
        Error::Unexpected
    }

    #[inline(always)]
    pub fn expected<I>(i: I) -> Error<I> {
        Error::Expected(i)
    }
}

#[cfg(test)]
mod test {
    use primitives::input::{new, DEFAULT, END_OF_INPUT};
    use primitives::IntoInner;
    use primitives::State;
    use super::*;
    use super::err;
    use {Input, SimpleResult};

    #[test]
    fn parse_decimal() {
        fn is_digit(c: u8) -> bool {
            c >= b'0' && c <= b'9'
        }

        fn decimal(i: Input<u8>) -> SimpleResult<u8, usize> {
            take_while1(i, is_digit).bind(|i, bytes|
                i.ret(bytes.iter().fold(0, |a, b| a * 10 + (b - b'0') as usize)))
        }

        let i = new(END_OF_INPUT, b"123.4567 ");

        let p = decimal(i).bind(|i, real|
            token(i, b'.').bind(|i, _|
                decimal(i).bind(|i, frac|
                    i.ret((real, frac)))));

        let d: SimpleResult<_, _> = p.bind(|i, num| take_remainder(i)
                                           .bind(|i, r| i.ret((r, num))));

        assert_eq!(d.into_inner(), State::Data(new(END_OF_INPUT, b""), (&b" "[..], (123, 4567))));
    }

    #[test]
    fn parse_remainder_empty() {
        let i = new(END_OF_INPUT, b"");

        let r = take_remainder(i);

        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), &b""[..]));
    }

    #[test]
    fn take_while1_empty() {
        let n = new(END_OF_INPUT, b"");

        let r = take_while1(n, |_| true);

        assert_eq!(r.into_inner(), State::Incomplete(1));
    }

    #[test]
    fn token_test() {
        assert_eq!(token(new(DEFAULT, b""), b'a').into_inner(), State::Incomplete(1));
        assert_eq!(token(new(DEFAULT, b"ab"), b'a').into_inner(), State::Data(new(DEFAULT, b"b"), b'a'));
        assert_eq!(token(new(DEFAULT, b"bb"), b'a').into_inner(), State::Error(b"bb", err::expected(b'a')));
    }

    #[test]
    fn take_test() {
        assert_eq!(take(new(DEFAULT, b"a"), 1).into_inner(), State::Data(new(DEFAULT, b""), &b"a"[..]));
        assert_eq!(take(new(DEFAULT, b"a"), 2).into_inner(), State::Incomplete(1));
        assert_eq!(take(new(DEFAULT, b"a"), 3).into_inner(), State::Incomplete(2));
        assert_eq!(take(new(DEFAULT, b"ab"), 1).into_inner(), State::Data(new(DEFAULT, b"b"), &b"a"[..]));
        assert_eq!(take(new(DEFAULT, b"ab"), 2).into_inner(), State::Data(new(DEFAULT, b""), &b"ab"[..]));
    }

    #[test]
    fn take_while_test() {
        assert_eq!(take_while(new(DEFAULT, b"abc"), |c| c != b'b').into_inner(), State::Data(new(DEFAULT, b"bc"), &b"a"[..]));
        assert_eq!(take_while(new(DEFAULT, b"bbc"), |c| c != b'b').into_inner(), State::Data(new(DEFAULT, b"bbc"), &b""[..]));
        assert_eq!(take_while(new(END_OF_INPUT, b"bbc"), |c| c != b'b').into_inner(), State::Data(new(END_OF_INPUT, b"bbc"), &b""[..]));
        assert_eq!(take_while(new(END_OF_INPUT, b"abc"), |c| c != b'b').into_inner(), State::Data(new(END_OF_INPUT, b"bc"), &b"a"[..]));
        // TODO: Update when the incomplete type has been updated
        assert_eq!(take_while(new(DEFAULT, b"acc"), |c| c != b'b').into_inner(), State::Incomplete(1));
        assert_eq!(take_while(new(END_OF_INPUT, b"acc"), |c| c != b'b').into_inner(), State::Data(new(END_OF_INPUT, b""), &b"acc"[..]));
    }

    #[test]
    fn take_while1_test() {
        assert_eq!(take_while1(new(DEFAULT, b"abc"), |c| c != b'b').into_inner(), State::Data(new(DEFAULT, b"bc"), &b"a"[..]));
        assert_eq!(take_while1(new(DEFAULT, b"bbc"), |c| c != b'b').into_inner(), State::Error(&b"bbc"[..], err::unexpected()));
        assert_eq!(take_while1(new(END_OF_INPUT, b"bbc"), |c| c != b'b').into_inner(), State::Error(&b"bbc"[..], err::unexpected()));
        assert_eq!(take_while1(new(END_OF_INPUT, b"abc"), |c| c != b'b').into_inner(), State::Data(new(END_OF_INPUT, b"bc"), &b"a"[..]));
        // TODO: Update when the incomplete type has been updated
        assert_eq!(take_while1(new(DEFAULT, b"acc"), |c| c != b'b').into_inner(), State::Incomplete(1));
        assert_eq!(take_while1(new(END_OF_INPUT, b"acc"), |c| c != b'b').into_inner(), State::Data(new(END_OF_INPUT, b""), &b"acc"[..]));
    }

    #[test]
    fn peek_next_test() {
        assert_eq!(peek_next(new(DEFAULT, b"abc")).into_inner(), State::Data(new(DEFAULT, b"abc"), b'a'));
        assert_eq!(peek_next(new(END_OF_INPUT, b"abc")).into_inner(), State::Data(new(END_OF_INPUT, b"abc"), b'a'));
        assert_eq!(peek_next(new(DEFAULT, b"")).into_inner(), State::Incomplete(1));
        assert_eq!(peek_next(new(END_OF_INPUT, b"")).into_inner(), State::Incomplete(1));
    }

    #[test]
    fn satisfy_with_test() {
        let mut m1 = 0;
        let mut n1 = 0;
        assert_eq!(satisfy_with(new(DEFAULT, b"abc"), |m| { m1 += 1; m % 8 }, |n| { n1 += 1; n == 1 }).into_inner(), State::Data(new(DEFAULT, b"bc"), 1));
        assert_eq!(m1, 1);
        assert_eq!(n1, 1);

        let mut m2 = 0;
        let mut n2 = 0;
        assert_eq!(satisfy_with(new(DEFAULT, b""), |m| { m2 += 1; m % 8 }, |n| { n2 += 1; n == 1 }).into_inner(), State::Incomplete(1));
        assert_eq!(m2, 0);
        assert_eq!(n2, 0);
    }

    #[test]
    fn string_test() {
        assert_eq!(string(new(DEFAULT, b"abc"), b"a").into_inner(), State::Data(new(DEFAULT, b"bc"), &b"a"[..]));
        assert_eq!(string(new(DEFAULT, b"abc"), b"ab").into_inner(), State::Data(new(DEFAULT, b"c"), &b"ab"[..]));
        assert_eq!(string(new(DEFAULT, b"abc"), b"abc").into_inner(), State::Data(new(DEFAULT, b""), &b"abc"[..]));
        assert_eq!(string(new(DEFAULT, b"abc"), b"abcd").into_inner(), State::Incomplete(1));
        assert_eq!(string(new(DEFAULT, b"abc"), b"abcde").into_inner(), State::Incomplete(2));
        assert_eq!(string(new(DEFAULT, b"abc"), b"ac").into_inner(), State::Error(b"bc", err::expected(b'b')));

        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"a").into_inner(), State::Data(new(END_OF_INPUT, b"bc"), &b"a"[..]));
        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"ab").into_inner(), State::Data(new(END_OF_INPUT, b"c"), &b"ab"[..]));
        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"abc").into_inner(), State::Data(new(END_OF_INPUT, b""), &b"abc"[..]));
        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"abcd").into_inner(), State::Incomplete(1));
        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"abcde").into_inner(), State::Incomplete(2));
        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"ac").into_inner(), State::Error(b"bc", err::expected(b'b')));
    }
}
