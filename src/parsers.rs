//! Basic parsers.

use std::mem;

use types::{
    Buffer,
    Input,
    ParseResult,
};
use primitives::Primitives;

pub use self::error::Error;

/// Result returned from the basic parsers.
pub type SimpleResult<I, T> = ParseResult<I, T, Error<<I as Input>::Token>>;

// Only export if we have backtraces enabled, in debug/test profiles the StackFrame is only used
// to debug-print.
#[cfg(feature="backtrace")]
pub use debugtrace::StackFrame;

/// Matches any item, returning it if present.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, any};
///
/// assert_eq!(parse_only(any, b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn any<I: Input>(mut i: I) -> SimpleResult<I, I::Token> {
    match i.pop() {
        Some(c) => i.ret(c),
        None    => i.err(Error::unexpected()),
    }
}

/// Matches an item using ``f``, the item is returned if ``f`` yields true, otherwise this parser
/// fails.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, satisfy};
///
/// assert_eq!(parse_only(|i| satisfy(i, |c| c == b'a'), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn satisfy<I: Input, F>(mut i: I, f: F) -> SimpleResult<I, I::Token>
  where F: FnOnce(I::Token) -> bool {
    match i.peek() {
        Some(c) if f(c) => { i.pop(); i.ret(c) },
        _               => i.err(Error::unexpected()),
    }
}

/// Reads a single token, applies the transformation `F` and then succeeds with the transformed
/// valeue if the predicate `P` yields true on this transformed value.
///
/// ```
/// use std::ascii::AsciiExt;
///
/// use chomp::prelude::{parse_only, satisfy_with};
///
/// let r = parse_only(
///     |i| satisfy_with(i, |c| AsciiExt::to_ascii_uppercase(&c), |c| c == b'T'),
///     b"testing");
///
/// assert_eq!(r, Ok(b'T'));
/// ```
#[inline]
pub fn satisfy_with<I: Input, T: Clone, F, P>(mut i: I, f: F, p: P) -> SimpleResult<I, T>
  where F: FnOnce(I::Token) -> T,
        P: FnOnce(T) -> bool {
    match i.peek().map(f) {
        Some(c) => {
            if p(c.clone()) {
                i.pop();

                i.ret(c)
            } else {
                i.err(Error::unexpected())
            }
        },
        _                           => i.err(Error::unexpected()),
    }
}

/// Matches a single token, returning the match on success.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, token};
///
/// assert_eq!(parse_only(|i| token(i, b'a'), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn token<I: Input>(mut i: I, t: I::Token) -> SimpleResult<I, I::Token> {
    match i.peek() {
        Some(c) if c == t => { i.pop(); i.ret(c) },
        _                 => i.err(Error::expected(t)),
    }
}

/// Matches a single token as long as it is not equal to `t`, returning the match on success.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, not_token};
///
/// assert_eq!(parse_only(|i| not_token(i, b'b'), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn not_token<I: Input>(mut i: I, t: I::Token) -> SimpleResult<I, I::Token> {
    match i.peek() {
        Some(c) if c != t => { i.pop(); i.ret(c) },
        _                 => i.err(Error::unexpected()),
    }
}

/// Matches any item but does not consume it, on success it gives ``Some`` but if no input remains
/// ``None`` is produced.
///
/// This parser is never considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, peek};
///
/// assert_eq!(parse_only(peek, b"abc"), Ok(Some(b'a')));
///
/// assert_eq!(parse_only(peek, b""), Ok(None));
/// ```
#[inline]
pub fn peek<I: Input>(mut i: I) -> SimpleResult<I, Option<I::Token>> {
    let t = i.peek();

    i.ret(t)
}

/// Matches any item but does not consume it.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, peek_next};
///
/// assert_eq!(parse_only(peek_next, b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn peek_next<I: Input>(mut i: I) -> SimpleResult<I, I::Token> {
    match i.peek() {
        Some(c) => i.ret(c),
        None    => i.err(Error::unexpected()),
    }
}

/// Matches ``num`` items no matter what they are, returning a slice of the matched items.
///
/// If the buffer length is less than ``num`` this parser is considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, take};
///
/// assert_eq!(parse_only(|i| take(i, 3), b"abcd"), Ok(&b"abc"[..]));
/// ```
#[inline]
pub fn take<I: Input>(mut i: I, num: usize) -> SimpleResult<I, I::Buffer> {
    match i.consume(num) {
        Some(b) => i.ret(b),
        // TODO: Proper incomplete error here?
        None    => i.err(Error::unexpected()),
    }
}

/// Matches all items while ``f`` returns false, returns a slice of all the matched items.
///
/// If no failure can be found the parser will be considered to be incomplete as there might be
/// more input which needs to be matched.
///
/// ```
/// use chomp::prelude::{parse_only, take_while};
///
/// let r = parse_only(|i| take_while(i, |c| c == b'a' || c == b'b'), b"abcdcba");
///
/// assert_eq!(r, Ok(&b"ab"[..]));
/// ```
///
/// Without managing to match anything:
///
/// ```
/// use chomp::prelude::{parse_only, take_while};
///
/// let r = parse_only(|i| take_while(i, |c| c == b'z'), b"abcdcba");
///
/// assert_eq!(r, Ok(&b""[..]));
/// ```
#[inline]
pub fn take_while<I: Input, F>(mut i: I, f: F) -> SimpleResult<I, I::Buffer>
  where F: FnMut(I::Token) -> bool {
    let b = i.consume_while(f);

    i.ret(b)
}

/// Matches all items while ``f`` returns true, if at least one item matched this parser succeeds
/// and returns a slice of all the matched items.
///
/// If no failure can be found the parser will be considered to be incomplete as there might be
/// more input which needs to be matched. If zero items were matched an error will be returned.
///
/// ```
/// use chomp::prelude::{parse_only, take_while1};
///
/// let r = parse_only(|i| take_while1(i, |c| c == b'a' || c == b'b'), b"abcdcba");
///
/// assert_eq!(r, Ok(&b"ab"[..]));
/// ```
#[inline]
pub fn take_while1<I: Input, F>(mut i: I, f: F) -> SimpleResult<I, I::Buffer>
  where F: FnMut(I::Token) -> bool {
    let b = i.consume_while(f);

    if b.is_empty() {
        i.err(Error::unexpected())
    } else {
        i.ret(b)
    }
}

/// Matches all items until ``f`` returns true, all items to that point will be returned as a slice
/// upon success.
///
/// If no failure can be found the parser will be considered to be incomplete as there might be
/// more input which needs to be matched.
///
/// ```
/// use chomp::prelude::{parse_only, take_till};
///
/// let r = parse_only(|i| take_till(i, |c| c == b'd'), b"abcdef");
///
/// assert_eq!(r, Ok(&b"abc"[..]));
/// ```
#[inline]
pub fn take_till<I: Input, F>(mut i: I, mut f: F) -> SimpleResult<I, I::Buffer>
  where F: FnMut(I::Token) -> bool {
    let mut ok = false;

    let b = i.consume_while(|c| {
        if f(c) {
            ok = true;

            false
        } else {
            true
        }
    });

    if ok {
        i.ret(b)
    } else {
        i.err(Error::unexpected())
    }
}

/// The predicate consumes and transforms a state argument, this parser will match everything until
/// the predicate returns `None`.
///
/// ```
/// use chomp::prelude::{parse_only, scan};
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
pub fn scan<I: Input, S, F>(mut i: I, s: S, mut f: F) -> SimpleResult<I, I::Buffer>
  where F: FnMut(S, I::Token) -> Option<S> {
    let mut state = Some(s);

    let b = i.consume_while(|c| { state = f(mem::replace(&mut state, None).expect("scan: Failed to obtain state, consume_while most likely called closure after end"), c); state.is_some() });

    i.ret(b)
}

/// Like `scan` but generalized to return the final state of the scanner.
///
/// ```
/// use chomp::prelude::{parse_only, run_scanner};
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
pub fn run_scanner<I: Input, S: Copy, F>(mut i: I, s: S, mut f: F) -> SimpleResult<I, (I::Buffer, S)>
  where F: FnMut(S, I::Token) -> Option<S> {
    let mut state = s;

    let b = i.consume_while(|c| {
        let t = f(state, c);
        match t {
            None    => false,
            Some(v) => { state = v; true }
        }
    });

    i.ret((b, state))
}

/// Matches the remainder of the buffer and returns it, always succeeds.
///
/// ```
/// use chomp::prelude::{parse_only, take_remainder};
///
/// assert_eq!(parse_only(take_remainder, b"abcd"), Ok(&b"abcd"[..]));
/// ```
#[inline]
pub fn take_remainder<I: Input>(mut i: I) -> SimpleResult<I, I::Buffer> {
    let b = i.consume_remaining();

    i.ret(b)
}

/// Matches the given slice against the parser, returning the matched slice upon success.
///
/// If the length of the contained data is shorter than the given slice this parser is considered
/// incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, string};
///
/// assert_eq!(parse_only(|i| string(i, b"abc"), b"abcdef"), Ok(&b"abc"[..]));
/// ```
// TODO: Does not actually work with &str yet
#[inline]
pub fn string<T: Copy + PartialEq, I: Input<Token=T>>(mut i: I, s: &[T])
    -> SimpleResult<I, I::Buffer> {
    let mut n = 0;
    let len   = s.len();

    // TODO: There has to be some more efficient way here
    let b = i.consume_while(|c| {
        if n >= len {
            false
        }
        else if c == s[n] {
            n += 1;

            true
        } else {
            false
        }
    });

    if n >= len {
        i.ret(b)
    } else {
        i.err(Error::expected(s[n]))
    }
}

/// Matches the end of the input.
///
/// ```
/// use chomp::prelude::{parse_only, token, eof};
///
/// let r = parse_only(|i| token(i, b'a').then(eof), b"a");
///
/// assert_eq!(r, Ok(()));
/// ```
#[inline]
pub fn eof<I: Input>(mut i: I) -> SimpleResult<I, ()> {
    if i.peek() == None {
        i.ret(())
    } else {
        i.err(Error::unexpected())
    }
}

mod error {
    use std::any;
    use std::error;
    use std::fmt;

    use debugtrace::Trace;

    #[cfg(feature="noop_error")]
    use std::marker::PhantomData;
    #[cfg(not(feature="noop_error"))]
    use std::ops::Deref;

    /// Empty type to eat the generic without printing
    #[cfg(feature="noop_error")]
    #[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
    struct Expected<I>(PhantomData<I>);

    #[cfg(feature="noop_error")]
    impl<I: fmt::Debug> fmt::Debug for Expected<I> {
        fn fmt(&self, _f: &mut fmt::Formatter) -> fmt::Result {
            // Intentionally empty
            Ok(())
        }
    }

    /// `Some(T)` if it expected a specific token, `None` if it encountered something unexpected.
    #[cfg(not(feature="noop_error"))]
    #[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
    struct Expected<I>(Option<I>);

    #[cfg(not(feature="noop_error"))]
    impl<I> Deref for Expected<I> {
        type Target = Option<I>;

        fn deref(&self) -> &Option<I> {
            &self.0
        }
    }

    #[cfg(not(feature="noop_error"))]
    impl<I: fmt::Debug> fmt::Debug for Expected<I> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self.0 {
                Some(ref c) => write!(f, "Expected({:?})", c),
                None        => write!(f, "Unexpected"),
            }
        }
    }

    /// Common error for the basic Chomp parsers.
    ///
    /// This is the common error for the basic Chomp parsers. It will contain information about what a
    /// parser expected or if it encountered something unexpected (in the case of user supplied
    /// predicates, eg. `satisfy`).
    ///
    /// This is coupled with the state found in the error state of the `ParseResult` type.
    #[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
    pub struct Error<I>(Trace<Expected<I>>);

    #[cfg(feature="noop_error")]
    impl<I> fmt::Display for Error<I>
      where I: fmt::Debug {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "parse error")
        }
    }

    #[cfg(not(feature="noop_error"))]
    impl<I> fmt::Display for Error<I>
      where I: fmt::Debug {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self.0.as_ref() {
                Some(ref c) => write!(f, "expected {:?}", *c),
                None        => write!(f, "unexpected"),
            }
        }
    }

    #[cfg(feature="noop_error")]
    impl<I: any::Any + fmt::Debug> error::Error for Error<I> {
        fn description(&self) -> &str {
            &"parse error"
        }
    }

    #[cfg(not(feature="noop_error"))]
    impl<I: any::Any + fmt::Debug> error::Error for Error<I> {
        fn description(&self) -> &str {
            match self.0.as_ref() {
                Some(_) => "expected a certain token, received another",
                None    => "received an unexpected token",
            }
        }
    }

    #[cfg(feature="noop_error")]
    macro_rules! create_error {
        ($_e:expr) => { Error(Trace::new(Expected(PhantomData))) }
    }

    #[cfg(not(feature="noop_error"))]
    macro_rules! create_error {
        ($e:expr) => { Error(Trace::new(Expected($e))) }
    }

    impl<I> Error<I> {
        /// Creates a new Unexpected error.
        ///
        /// Should be used when the error value is not important.
        #[inline(always)]
        pub fn new() -> Self {
            create_error!(None)
        }

        /// Creates a new Unexpected error.
        ///
        /// Should be used when the token was unexpected, as in the case of `satisfy` where a user
        /// provided predicate is provided.
        #[inline(always)]
        pub fn unexpected() -> Self {
            create_error!(None)
        }

        /// Creates a new Expected error.
        ///
        /// Should be used when a specific token was expected.
        #[inline(always)]
        #[allow(unused_variables)]
        pub fn expected(i: I) -> Self {
            create_error!(Some(i))
        }

        /// Returns `Some(&I)` if a specific token was expected, `None` otherwise.
        ///
        /// Will always yield `None` since `noop_error` is enabled.
        #[inline]
        #[cfg(feature="noop_error")]
        pub fn expected_token(&self) -> Option<&I> {
            None
        }

        /// Returns `Some(&I)` if a specific token was expected, `None` otherwise.
        #[inline]
        #[cfg(not(feature="noop_error"))]
        pub fn expected_token(&self) -> Option<&I> {
            self.0.as_ref()
        }

        /// Returns a stack-trace to where the error was created.
        #[cfg(feature="backtrace")]
        pub fn trace(&self) -> Vec<::debugtrace::StackFrame> {
            self.0.resolve()
        }
    }
}

#[cfg(test)]
mod test {
    use primitives::IntoInner;
    use super::*;
    use types::{Input, ParseResult};

    #[test]
    fn parse_decimal() {
        fn is_digit(c: u8) -> bool {
            c >= b'0' && c <= b'9'
        }

        fn decimal<'i, I: Input<Token=u8, Buffer=&'i [u8]>>(i: I) -> SimpleResult<I, usize> {
            take_while1(i, is_digit).bind(|i, bytes|
                i.ret(bytes.iter().fold(0, |a, b| a * 10 + (b - b'0') as usize)))
        }

        let i = &b"123.4567 "[..];

        let p = decimal(i).bind(|i, real|
            token(i, b'.').bind(|i, _|
                decimal(i).bind(|i, frac|
                    i.ret((real, frac)))));

        // ParseResult necessary here due to inference, for some reason is
        // `Error<<I as Input>::Token>` not specific enough to actually help inference.
        let d: ParseResult<_, _, Error<u8>> = p.bind(|i, num| take_remainder(i)
                                           .bind(|i, r| i.ret((r, num))));

        assert_eq!(d.into_inner(), (&b""[..], Ok((&b" "[..], (123, 4567)))));
    }

    #[test]
    fn parse_remainder_empty() {
        assert_eq!(take_remainder(&b""[..]).into_inner(), (&b""[..], Ok(&b""[..])));
    }

    #[test]
    fn take_while1_empty() {
        assert_eq!(take_while1(&b""[..], |_| true).into_inner(), (&b""[..], Err(Error::unexpected())));
    }

    #[test]
    fn token_test() {
        assert_eq!(token(&b""[..],   b'a').into_inner(), (&b""[..],   Err(Error::expected(b'a'))));
        assert_eq!(token(&b"ab"[..], b'a').into_inner(), (&b"b"[..],  Ok(b'a')));
        assert_eq!(token(&b"bb"[..], b'a').into_inner(), (&b"bb"[..], Err(Error::expected(b'a'))));
    }

    #[test]
    fn take_test() {
        assert_eq!(take(&b""[..],   0).into_inner(), (&b""[..],  Ok(&b""[..])));
        assert_eq!(take(&b"a"[..],  0).into_inner(), (&b"a"[..], Ok(&b""[..])));
        assert_eq!(take(&b"a"[..],  1).into_inner(), (&b""[..],  Ok(&b"a"[..])));
        assert_eq!(take(&b"a"[..],  2).into_inner(), (&b"a"[..], Err(Error::unexpected())));
        assert_eq!(take(&b"a"[..],  3).into_inner(), (&b"a"[..], Err(Error::unexpected())));
        assert_eq!(take(&b"ab"[..], 1).into_inner(), (&b"b"[..], Ok(&b"a"[..])));
        assert_eq!(take(&b"ab"[..], 2).into_inner(), (&b""[..],  Ok(&b"ab"[..])));
    }

    #[test]
    fn take_while_test() {
        assert_eq!(take_while(&b""[..],    |c| c != b'b').into_inner(), (&b""[..],    Ok(&b""[..])));
        assert_eq!(take_while(&b"a"[..],   |c| c != b'b').into_inner(), (&b""[..],    Ok(&b"a"[..])));
        assert_eq!(take_while(&b"b"[..],   |c| c != b'b').into_inner(), (&b"b"[..],   Ok(&b""[..])));
        assert_eq!(take_while(&b"abc"[..], |c| c != b'b').into_inner(), (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(take_while(&b"bbc"[..], |c| c != b'b').into_inner(), (&b"bbc"[..], Ok(&b""[..])));
        assert_eq!(take_while(&b"bbc"[..], |c| c != b'b').into_inner(), (&b"bbc"[..], Ok(&b""[..])));
        assert_eq!(take_while(&b"abc"[..], |c| c != b'b').into_inner(), (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(take_while(&b"acc"[..], |c| c != b'b').into_inner(), (&b""[..],    Ok(&b"acc"[..])));
    }

    #[test]
    fn take_while1_test() {
        assert_eq!(take_while1(&b""[..],    |c| c != b'b').into_inner(), (&b""[..],    Err(Error::unexpected())));
        assert_eq!(take_while1(&b"a"[..],   |c| c != b'b').into_inner(), (&b""[..],    Ok(&b"a"[..])));
        assert_eq!(take_while1(&b"b"[..],   |c| c != b'b').into_inner(), (&b"b"[..],   Err(Error::unexpected())));
        assert_eq!(take_while1(&b"ab"[..],  |c| c != b'b').into_inner(), (&b"b"[..],   Ok(&b"a"[..])));
        assert_eq!(take_while1(&b"abc"[..], |c| c != b'b').into_inner(), (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(take_while1(&b"bbc"[..], |c| c != b'b').into_inner(), (&b"bbc"[..], Err(Error::unexpected())));
        assert_eq!(take_while1(&b"bbc"[..], |c| c != b'b').into_inner(), (&b"bbc"[..], Err(Error::unexpected())));
        assert_eq!(take_while1(&b"abc"[..], |c| c != b'b').into_inner(), (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(take_while1(&b"acc"[..], |c| c != b'b').into_inner(), (&b""[..],    Ok(&b"acc"[..])));
    }

    #[test]
    fn peek_next_test() {
        assert_eq!(peek_next(&b"abc"[..]).into_inner(), (&b"abc"[..], Ok(b'a')));
        assert_eq!(peek_next(&b"abc"[..]).into_inner(), (&b"abc"[..], Ok(b'a')));
        assert_eq!(peek_next(&b""[..]).into_inner(),    (&b""[..],    Err(Error::unexpected())));
        assert_eq!(peek_next(&b""[..]).into_inner(),    (&b""[..],    Err(Error::unexpected())));
    }

    #[test]
    fn satisfy_with_test() {
        let mut m1 = 0;
        let mut n1 = 0;
        assert_eq!(satisfy_with(&b"abc"[..], |m| { m1 += 1; m % 8 }, |n| { n1 += 1; n == 1 }).into_inner(), (&b"bc"[..], Ok(1)));
        assert_eq!(m1, 1);
        assert_eq!(n1, 1);

        let mut m2 = 0;
        let mut n2 = 0;
        assert_eq!(satisfy_with(&b""[..], |m| { m2 += 1; m % 8 }, |n| { n2 += 1; n == 1 }).into_inner(), (&b""[..], Err(Error::unexpected())));
        assert_eq!(m2, 0);
        assert_eq!(n2, 0);
    }

    #[test]
    fn string_test() {
        assert_eq!(string(&b""[..],    b"").into_inner(),      (&b""[..],    Ok(&b""[..])));
        assert_eq!(string(&b""[..],    b"a").into_inner(),     (&b""[..],    Err(Error::expected(b'a'))));
        assert_eq!(string(&b"a"[..],   b"a").into_inner(),     (&b""[..],    Ok(&b"a"[..])));
        assert_eq!(string(&b"b"[..],   b"a").into_inner(),     (&b"b"[..],   Err(Error::expected(b'a'))));
        assert_eq!(string(&b"abc"[..], b"a").into_inner(),     (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(string(&b"abc"[..], b"ab").into_inner(),    (&b"c"[..],   Ok(&b"ab"[..])));
        assert_eq!(string(&b"abc"[..], b"abc").into_inner(),   (&b""[..],    Ok(&b"abc"[..])));
        assert_eq!(string(&b"abc"[..], b"abcd").into_inner(),  (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string(&b"abc"[..], b"abcde").into_inner(), (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string(&b"abc"[..], b"ac").into_inner(),    (&b"bc"[..],  Err(Error::expected(b'c'))));
    }

    #[test]
    #[cfg(not(feature = "noop_error"))]
    fn error_test() {
        let e = Error::<()>::new();
        assert_eq!(e.expected_token(), None);
        let e = Error::<()>::unexpected();
        assert_eq!(e.expected_token(), None);
        let e = Error::expected(b'a');
        assert_eq!(e.expected_token(), Some(&b'a'));
    }

    #[test]
    #[cfg(feature = "noop_error")]
    fn noop_error_test() {
        let e = Error::<()>::new();
        assert_eq!(e.expected_token(), None);
        let e = Error::<()>::unexpected();
        assert_eq!(e.expected_token(), None);
        let e = Error::expected(b'a');
        assert_eq!(e.expected_token(), None);
    }

    #[test]
    #[cfg(feature="backtrace")]
    fn backtrace_test() {
        let e = Error::<()>::new();

        let trace = e.trace();
        let this  = &trace[0];

        assert!(this.name.as_ref().map(|n| n.contains("parsers::test::backtrace_test")).unwrap_or(false), "Expected trace to contain \"parsers::test::backtrace_test\", got: {:?}", this.name.as_ref());
    }
}
