//! Basic parsers.

use std::mem;

use input::Input;
use parse_result::SimpleResult;
use primitives::Primitives;

pub use self::error::Error;

// Only export if we have backtraces enabled, in debug/test profiles the StackFrame is only used
// to debug-print.
#[cfg(feature="backtrace")]
pub use debugtrace::StackFrame;

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
pub fn any<I: Input>(mut i: I) -> SimpleResult<I, I::Token> {
    match i.first() {
        None    => i.incomplete(1),
        Some(c) => {
            i.discard(1);

            i.ret(c)
        },
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
pub fn satisfy<I: Input, F>(mut i: I, f: F) -> SimpleResult<I, I::Token>
  where F: FnOnce(I::Token) -> bool {
    match i.first() {
        None            => i.incomplete(1),
        Some(c) if f(c) => {
            i.discard(1);

            i.ret(c)
        },
        Some(_)         => i.err(Error::unexpected()),
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
pub fn satisfy_with<I: Input, T: Clone, F, P>(mut i: I, f: F, p: P) -> SimpleResult<I, T>
  where F: FnOnce(I::Token) -> T,
        P: FnOnce(T) -> bool {
    match i.first() {
        Some(n) => {
            let t = f(n);

            if p(t.clone()) {
                i.discard(1);

                i.ret(t)
            } else {
                i.err(Error::unexpected())
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
pub fn token<I: Input>(mut i: I, t: I::Token) -> SimpleResult<I, I::Token>
  where I::Token: PartialEq {
    match i.first() {
        None              => i.incomplete(1),
        Some(c) if t == c => {
            i.discard(1);

            i.ret(c)
        },
        Some(_)           => i.err(Error::expected(t)),
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
pub fn not_token<I: Input>(mut i: I, t: I::Token) -> SimpleResult<I, I::Token>
  where I::Token: PartialEq {
    match i.first() {
        None              => i.incomplete(1),
        Some(c) if t != c => {
            i.discard(1);
            i.ret(c)
        },
        Some(_)           => i.err(Error::unexpected()),
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
pub fn peek<I: Input>(i: I) -> SimpleResult<I, Option<I::Token>>
  where I::Token: Clone {
    let d = i.first();

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
pub fn peek_next<I: Input>(i: I) -> SimpleResult<I, I::Token>
  where I::Token: Clone {
    match i.first() {
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
pub fn take<I: Input>(mut i: I, num: usize) -> SimpleResult<I, I::Buffer> {
    let r = i.min_remaining();

    if num <= r {
        let b = i.consume(num);

        i.ret(b)
    } else {
        i.incomplete(num - r)
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
pub fn take_while<I: Input, F>(mut i: I, f: F) -> SimpleResult<I, I::Buffer>
  where F: Fn(I::Token) -> bool {
    match i.iter().position(|c| f(c) == false) {
        Some(n) => {
            let b = i.consume(n);

            i.ret(b)
        },
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => if i.is_end() {
            // Last slice and we have just read everything of it, replace with zero-sized slice:
            let r = i.min_remaining();
            let b = i.consume(r);

            i.ret(b)
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
pub fn take_while1<I: Input, F>(mut i: I, f: F) -> SimpleResult<I, I::Buffer>
  where F: Fn(I::Token) -> bool {
    match i.iter().position(|c| f(c) == false) {
        Some(0) => i.err(Error::unexpected()),
        Some(n) => {
            let b = i.consume(n);

            i.ret(b)
        },
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => if i.min_remaining() > 0 && i.is_end() {
            // Last slice and we have just read everything of it, replace with zero-sized slice:
            let r = i.min_remaining();
            let b = i.consume(r);

            i.ret(b)
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
pub fn take_till<I: Input, F>(mut i: I, f: F) -> SimpleResult<I, I::Buffer>
  where F: Fn(I::Token) -> bool,
        I::Token: Clone {
    match i.iter().position(f) {
        Some(n) => {
            let b = i.consume(n);

            i.ret(b)
        },
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
pub fn scan<I: Input, S, F>(mut i: I, s: S, mut f: F) -> SimpleResult<I, I::Buffer>
  where F: FnMut(S, I::Token) -> Option<S> {
    let mut state = Some(s);

    match i.iter().position(|c| { state = f(mem::replace(&mut state, None).unwrap(), c); state.is_none()}) {
        Some(n) => {
            let b = i.consume(n);

            i.ret(b)
        },
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
pub fn run_scanner<I: Input, S: Copy, F>(mut i: I, s: S, mut f: F) -> SimpleResult<I, (I::Buffer, S)>
  where F: FnMut(S, I::Token) -> Option<S> {
    let mut state = s;

    match i.iter().position(|c| { let t = f(state, c); match t { None => true, Some(v) => { state = v; false } } }) {
        Some(n) => {
            let b = i.consume(n);

            i.ret((b, state))
        },
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
pub fn take_remainder<I: Input>(mut i: I) -> SimpleResult<I, I::Buffer> {
    // Last slice and we have just read everything of it, replace with zero-sized slice:
    let r = i.min_remaining();
    let b = i.consume(r);

    i.ret(b)
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
pub fn string<'b, T: Copy + PartialEq, I: Input<Token=T>>(mut i: I, s: &'b [T])
    -> SimpleResult<I, I::Buffer> {
    let r = i.min_remaining();

    if s.len() > r {
        return i.incomplete(s.len() - r);
    }

    // TODO: Check if this is efficient:
    for (n, (a, b)) in i.iter().zip(s.iter()).enumerate() {
        if a != *b {
            i.discard(n);

            return i.err(Error::expected(*b));
        }
    }

    let b = i.consume(s.len());

    i.ret(b)
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
pub fn eof<I: Input>(i: I) -> SimpleResult<I, ()> {
    if i.min_remaining() == 0 && i.is_end() {
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
        pub fn expected(_i: I) -> Self {
            create_error!(Some(_i))
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
    use primitives::input::{new_buf, DEFAULT, END_OF_INPUT};
    use primitives::IntoInner;
    use primitives::State;
    use super::*;
    use {Input, SimpleResult, ParseResult};

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

        let d: ParseResult<_, _, Error<u8>> = p.bind(|i, num| take_remainder(i)
                                           .bind(|i, r| i.ret((r, num))));

        assert_eq!(d.into_inner(), State::Data(&b""[..], (&b" "[..], (123, 4567))));
    }

    #[test]
    fn parse_remainder_empty() {
        let i = &b""[..];

        let r = take_remainder(i);

        assert_eq!(r.into_inner(), State::Data(&b""[..], &b""[..]));
    }

    #[test]
    fn take_while1_empty() {
        let n = &b""[..];

        let r = take_while1(n, |_| true);

        assert_eq!(r.into_inner(), State::Incomplete(1));
    }

    #[test]
    fn token_test() {
        assert_eq!(token(new_buf(DEFAULT, b""), b'a').into_inner(), State::Incomplete(1));
        assert_eq!(token(new_buf(DEFAULT, b"ab"), b'a').into_inner(), State::Data(new_buf(DEFAULT, b"b"), b'a'));
        assert_eq!(token(new_buf(DEFAULT, b"bb"), b'a').into_inner(), State::Error(new_buf(DEFAULT, b"bb"), Error::expected(b'a')));
    }

    #[test]
    fn take_test() {
        assert_eq!(take(new_buf(DEFAULT, b"a"), 1).into_inner(), State::Data(new_buf(DEFAULT, b""), &b"a"[..]));
        assert_eq!(take(new_buf(DEFAULT, b"a"), 2).into_inner(), State::Incomplete(1));
        assert_eq!(take(new_buf(DEFAULT, b"a"), 3).into_inner(), State::Incomplete(2));
        assert_eq!(take(new_buf(DEFAULT, b"ab"), 1).into_inner(), State::Data(new_buf(DEFAULT, b"b"), &b"a"[..]));
        assert_eq!(take(new_buf(DEFAULT, b"ab"), 2).into_inner(), State::Data(new_buf(DEFAULT, b""), &b"ab"[..]));
    }

    #[test]
    fn take_while_test() {
        assert_eq!(take_while(new_buf(DEFAULT, b"abc"), |c| c != b'b').into_inner(), State::Data(new_buf(DEFAULT, b"bc"), &b"a"[..]));
        assert_eq!(take_while(new_buf(DEFAULT, b"bbc"), |c| c != b'b').into_inner(), State::Data(new_buf(DEFAULT, b"bbc"), &b""[..]));
        assert_eq!(take_while(&b"bbc"[..], |c| c != b'b').into_inner(), State::Data(&b"bbc"[..], &b""[..]));
        assert_eq!(take_while(&b"abc"[..], |c| c != b'b').into_inner(), State::Data(&b"bc"[..], &b"a"[..]));
        // TODO: Update when the incomplete type has been updated
        assert_eq!(take_while(new_buf(DEFAULT, b"acc"), |c| c != b'b').into_inner(), State::Incomplete(1));
        assert_eq!(take_while(&b"acc"[..], |c| c != b'b').into_inner(), State::Data(&b""[..], &b"acc"[..]));
    }

    #[test]
    fn take_while1_test() {
        assert_eq!(take_while1(new_buf(DEFAULT, b"abc"), |c| c != b'b').into_inner(), State::Data(new_buf(DEFAULT, b"bc"), &b"a"[..]));
        assert_eq!(take_while1(new_buf(DEFAULT, b"bbc"), |c| c != b'b').into_inner(), State::Error(new_buf(DEFAULT, b"bbc"), Error::unexpected()));
        assert_eq!(take_while1(&b"bbc"[..], |c| c != b'b').into_inner(), State::Error(&b"bbc"[..], Error::unexpected()));
        assert_eq!(take_while1(&b"abc"[..], |c| c != b'b').into_inner(), State::Data(&b"bc"[..], &b"a"[..]));
        // TODO: Update when the incomplete type has been updated
        assert_eq!(take_while1(new_buf(DEFAULT, b"acc"), |c| c != b'b').into_inner(), State::Incomplete(1));
        assert_eq!(take_while1(&b"acc"[..], |c| c != b'b').into_inner(), State::Data(&b""[..], &b"acc"[..]));
    }

    #[test]
    fn peek_next_test() {
        assert_eq!(peek_next(new_buf(DEFAULT, b"abc")).into_inner(), State::Data(new_buf(DEFAULT, b"abc"), b'a'));
        assert_eq!(peek_next(&b"abc"[..]).into_inner(), State::Data(&b"abc"[..], b'a'));
        assert_eq!(peek_next(new_buf(DEFAULT, b"")).into_inner(), State::Incomplete(1));
        assert_eq!(peek_next(&b""[..]).into_inner(), State::Incomplete(1));
    }

    #[test]
    fn satisfy_with_test() {
        let mut m1 = 0;
        let mut n1 = 0;
        assert_eq!(satisfy_with(new_buf(DEFAULT, b"abc"), |m| { m1 += 1; m % 8 }, |n| { n1 += 1; n == 1 }).into_inner(), State::Data(new_buf(DEFAULT, b"bc"), 1));
        assert_eq!(m1, 1);
        assert_eq!(n1, 1);

        let mut m2 = 0;
        let mut n2 = 0;
        assert_eq!(satisfy_with(new_buf(DEFAULT, b""), |m| { m2 += 1; m % 8 }, |n| { n2 += 1; n == 1 }).into_inner(), State::Incomplete(1));
        assert_eq!(m2, 0);
        assert_eq!(n2, 0);
    }

    #[test]
    fn string_test() {
        assert_eq!(string(new_buf(DEFAULT, b"abc"), b"a").into_inner(), State::Data(new_buf(DEFAULT, b"bc"), &b"a"[..]));
        assert_eq!(string(new_buf(DEFAULT, b"abc"), b"ab").into_inner(), State::Data(new_buf(DEFAULT, b"c"), &b"ab"[..]));
        assert_eq!(string(new_buf(DEFAULT, b"abc"), b"abc").into_inner(), State::Data(new_buf(DEFAULT, b""), &b"abc"[..]));
        assert_eq!(string(new_buf(DEFAULT, b"abc"), b"abcd").into_inner(), State::Incomplete(1));
        assert_eq!(string(new_buf(DEFAULT, b"abc"), b"abcde").into_inner(), State::Incomplete(2));
        assert_eq!(string(new_buf(DEFAULT, b"abc"), b"ac").into_inner(), State::Error(new_buf(DEFAULT, b"bc"), Error::expected(b'c')));

        assert_eq!(string(&b"abc"[..], b"a").into_inner(), State::Data(&b"bc"[..], &b"a"[..]));
        assert_eq!(string(&b"abc"[..], b"ab").into_inner(), State::Data(&b"c"[..], &b"ab"[..]));
        assert_eq!(string(&b"abc"[..], b"abc").into_inner(), State::Data(&b""[..], &b"abc"[..]));
        assert_eq!(string(&b"abc"[..], b"abcd").into_inner(), State::Incomplete(1));
        assert_eq!(string(&b"abc"[..], b"abcde").into_inner(), State::Incomplete(2));
        assert_eq!(string(&b"abc"[..], b"ac").into_inner(), State::Error(&b"bc"[..], Error::expected(b'c')));
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
