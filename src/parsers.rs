//! Basic parsers.

use std::mem;

use types::{
    Buffer,
    Input,
    Parser,
};

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
/// use chomp::prelude::{parse_only, any};
///
/// assert_eq!(parse_only(any(), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn any<I: Input>() -> impl Parser<I, Output=I::Token, Error=Error<I::Token>> {
    move |mut i: I| match i.pop() {
        Some(c) => (i, Ok(c)),
        None    => (i, Err(Error::unexpected())),
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
/// assert_eq!(parse_only(satisfy(|c| c == b'a'), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn satisfy<I: Input, F>(f: F) -> impl Parser<I, Output=I::Token, Error=Error<I::Token>>
  where F: FnOnce(I::Token) -> bool {
    move |mut i: I| match i.peek() {
        Some(c) if f(c) => { i.pop(); (i, Ok(c)) },
        _               => (i, Err(Error::unexpected())),
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
///     satisfy_with(|c| AsciiExt::to_ascii_uppercase(&c), |c| c == b'T'),
///     b"testing");
///
/// assert_eq!(r, Ok(b'T'));
/// ```
#[inline]
pub fn satisfy_with<I: Input, T: Clone, F, P>(f: F, p: P) -> impl Parser<I, Output=T, Error=Error<I::Token>>
  where F: FnOnce(I::Token) -> T,
        P: FnOnce(T) -> bool {
    move |mut i: I| match i.peek().map(f) {
        Some(c) => {
            if p(c.clone()) {
                i.pop();

                (i, Ok(c))
            } else {
                (i, Err(Error::unexpected()))
            }
        },
        _ => (i, Err(Error::unexpected())),
    }
}

/// Matches a single token, returning the match on success.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, token};
///
/// assert_eq!(parse_only(token(b'a'), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn token<I: Input>(t: I::Token) -> impl Parser<I, Output=I::Token, Error=Error<I::Token>> {
    move |mut i: I| match i.peek() {
        Some(c) if c == t => { i.pop(); (i, Ok(c)) },
        _                 => (i, Err(Error::expected(t))),
    }
}

/// Matches a single token as long as it is not equal to `t`, returning the match on success.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, not_token};
///
/// assert_eq!(parse_only(not_token(b'b'), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn not_token<I: Input>(t: I::Token) -> impl Parser<I, Output=I::Token, Error=Error<I::Token>> {
    move |mut i: I| match i.peek() {
        Some(c) if c != t => { i.pop(); (i, Ok(c)) },
        _                 => (i, Err(Error::unexpected())),
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
/// assert_eq!(parse_only(peek(), b"abc"), Ok(Some(b'a')));
///
/// assert_eq!(parse_only(peek(), b""), Ok(None));
/// ```
#[inline]
pub fn peek<I: Input>() -> impl Parser<I, Output=Option<I::Token>, Error=Error<I::Token>> {
    |mut i: I| {
        let t = i.peek();

        (i, Ok(t))
    }
}

/// Matches any item but does not consume it.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, peek_next};
///
/// assert_eq!(parse_only(peek_next(), b"abc"), Ok(b'a'));
/// ```
#[inline]
pub fn peek_next<I: Input>() -> impl Parser<I, Output=I::Token, Error=Error<I::Token>> {
    move |mut i: I| match i.peek() {
        Some(c) => (i, Ok(c)),
        None    => (i, Err(Error::unexpected())),
    }
}

/// Matches ``num`` items no matter what they are, returning a slice of the matched items.
///
/// If the buffer length is less than ``num`` this parser is considered incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, take};
///
/// assert_eq!(parse_only(take(3), b"abcd"), Ok(&b"abc"[..]));
/// ```
#[inline]
pub fn take<I: Input>(num: usize) -> impl Parser<I, Output=I::Buffer, Error=Error<I::Token>> {
    move |mut i: I| match i.consume(num) {
        Some(b) => (i, Ok(b)),
        None    => (i, Err(Error::unexpected())),
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
/// let r = parse_only(take_while(|c| c == b'a' || c == b'b'), b"abcdcba");
///
/// assert_eq!(r, Ok(&b"ab"[..]));
/// ```
///
/// Without managing to match anything:
///
/// ```
/// use chomp::prelude::{parse_only, take_while};
///
/// let r = parse_only(take_while(|c| c == b'z'), b"abcdcba");
///
/// assert_eq!(r, Ok(&b""[..]));
/// ```
#[inline]
pub fn take_while<I: Input, F>(f: F) -> impl Parser<I, Output=I::Buffer, Error=Error<I::Token>>
  where F: FnMut(I::Token) -> bool {
    move |mut i: I| {
        let b = i.consume_while(f);

        (i, Ok(b))
    }
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
/// let r = parse_only(take_while1(|c| c == b'a' || c == b'b'), b"abcdcba");
///
/// assert_eq!(r, Ok(&b"ab"[..]));
/// ```
#[inline]
pub fn take_while1<I: Input, F>(f: F) -> impl Parser<I, Output=I::Buffer, Error=Error<I::Token>>
  where F: FnMut(I::Token) -> bool {
    move |mut i: I| {
        let b = i.consume_while(f);

        if b.is_empty() {
            (i, Err(Error::unexpected()))
        } else {
            (i, Ok(b))
        }
    }
}

/// Skips over tokens in the input until `f` returns false.
///
/// ```
/// use chomp::prelude::{Parser, skip_while};
///
/// assert_eq!(skip_while(|c| c == b'a').parse(&b"aaabc"[..]), (&b"bc"[..], Ok(())));
/// ```
#[inline]
pub fn skip_while<I: Input, F>(f: F) -> impl Parser<I, Output=(), Error=Error<I::Token>>
  where F: FnMut(I::Token) -> bool {
    move |mut i: I| {
        i.skip_while(f);

        (i, Ok(()))
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
/// let r = parse_only(take_till(|c| c == b'd'), b"abcdef");
///
/// assert_eq!(r, Ok(&b"abc"[..]));
/// ```
#[inline]
pub fn take_till<I: Input, F>(mut f: F) -> impl Parser<I, Output=I::Buffer, Error=Error<I::Token>>
  where F: FnMut(I::Token) -> bool {
    move |mut i: I| {
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
            (i, Ok(b))
        } else {
            (i, Err(Error::unexpected()))
        }
    }
}

/// The predicate consumes and transforms a state argument, this parser will match everything until
/// the predicate returns `None`.
///
/// ```
/// use chomp::prelude::{parse_only, scan};
///
/// let p = scan(false, |s, c| match (s, c) {
///     (true, b'/') => None,
///     (_,    b'*') => Some(true),
///     (_, _)       => Some(false),
/// });
///
/// assert_eq!(parse_only(p, b"/*test*of*scan*/ foo"), Ok(&b"/*test*of*scan*"[..]));
/// ```
#[inline]
pub fn scan<I: Input, S, F>(s: S, mut f: F) -> impl Parser<I, Output=I::Buffer, Error=Error<I::Token>>
  where F: FnMut(S, I::Token) -> Option<S> {
    move |mut i: I| {
        let mut state = Some(s);

        let b = i.consume_while(|c| { state = f(mem::replace(&mut state, None).expect("scan: Failed to obtain state, consume_while most likely called closure after end"), c); state.is_some() });

        (i, Ok(b))
    }
}

/// Like `scan` but generalized to return the final state of the scanner.
///
/// ```
/// use chomp::prelude::{parse_only, run_scanner};
///
/// let p = run_scanner(0, |s, c| match (s, c) {
///     (b'*', b'/') => None,
///     (_,    c)    => Some(c),
/// });
///
/// assert_eq!(parse_only(p, b"/*test*of*scan*/ foo"), Ok((&b"/*test*of*scan*"[..], b'*')));
/// ```
#[inline]
// TODO: Remove Copy bound on S
pub fn run_scanner<I: Input, S: Copy, F>(s: S, mut f: F) -> impl Parser<I, Output=(I::Buffer, S), Error=Error<I::Token>>
  where F: FnMut(S, I::Token) -> Option<S> {
    move |mut i: I| {
        let mut state = s;

        let b = i.consume_while(|c| {
            let t = f(state, c);
            match t {
                None    => false,
                Some(v) => { state = v; true }
            }
        });

        (i, Ok((b, state)))
    }
}

/// Matches the remainder of the buffer and returns it, always succeeds.
///
/// ```
/// use chomp::prelude::{parse_only, take_remainder};
///
/// assert_eq!(parse_only(take_remainder(), b"abcd"), Ok(&b"abcd"[..]));
/// ```
#[inline]
pub fn take_remainder<I: Input>() -> impl Parser<I, Output=I::Buffer, Error=Error<I::Token>> {
    move |mut i: I| {
        let b = i.consume_remaining();

        (i, Ok(b))
    }
}

/// Matches the given slice against the parser, returning the matched slice upon success.
///
/// If the length of the contained data is shorter than the given slice this parser is considered
/// incomplete.
///
/// ```
/// use chomp::prelude::{parse_only, string};
///
/// assert_eq!(parse_only(string(b"abc"), b"abcdef"), Ok(&b"abc"[..]));
/// ```
// TODO: Does not actually work with &str yet
#[inline]
// pub fn string<'a, I: Input>(s: &'a [I::Token]) -> impl Parser<I, Output=I::Buffer, Error=Error<I::Token>> {
pub fn string<I: Input>(s: &'static [I::Token]) -> impl Parser<I, Output=I::Buffer, Error=Error<I::Token>> {
    move |mut i: I| {
        let mut n = 0;
        let len   = s.len();

        // TODO: There has to be some more efficient way here
        let b = i.consume_while(|c| {
            if n >= len || c != s[n] {
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

/// Matches the end of the input.
///
/// ```
/// use chomp::prelude::{Parser, parse_only, token, eof};
///
/// let r = parse_only(token(b'a').then(eof()), b"a");
///
/// assert_eq!(r, Ok(()));
/// ```
#[inline]
pub fn eof<I: Input>() -> impl Parser<I, Output=(), Error=Error<I::Token>> {
    move |mut i: I| if i.peek() == None {
        (i, Ok(()))
    } else {
        (i, Err(Error::unexpected()))
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
                Some(c) => write!(f, "expected {:?}", *c),
                None    => write!(f, "unexpected"),
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
    use super::*;
    use types::{Buffer, Input, Parser, ret};

    #[test]
    fn parse_decimal() {
        fn is_digit(c: u8) -> bool {
            c >= b'0' && c <= b'9'
        }

        fn decimal<I: Input<Token=u8>>() -> impl Parser<I, Output=usize, Error=Error<u8>> {
            take_while1(is_digit).bind(|bytes: I::Buffer|
                ret(bytes.fold(0, |a, b| a * 10 + (b - b'0') as usize)))
        }

        let i = &b"123.4567 "[..];

        let p = decimal().bind(|real| token(b'.').then(decimal().map(move |frac| (real, frac))))
            .bind(|num| take_remainder().map(move |r| (r, num)));

        assert_eq!(p.parse(i), (&b""[..], Ok((&b" "[..], (123, 4567)))));
    }

    #[test]
    fn parse_remainder_empty() {
        assert_eq!(take_remainder().parse(&b""[..]), (&b""[..], Ok(&b""[..])));
    }

    #[test]
    fn take_while1_empty() {
        assert_eq!(take_while1(|_| true).parse(&b""[..]), (&b""[..], Err(Error::unexpected())));
    }

    #[test]
    fn token_test() {
        assert_eq!(token(b'a').parse(&b""[..]), (&b""[..],   Err(Error::expected(b'a'))));
        assert_eq!(token(b'a').parse(&b"ab"[..]), (&b"b"[..],  Ok(b'a')));
        assert_eq!(token(b'a').parse(&b"bb"[..]), (&b"bb"[..], Err(Error::expected(b'a'))));
    }

    #[test]
    fn take_test() {
        assert_eq!(take(0).parse(&b""[..]), (&b""[..],  Ok(&b""[..])));
        assert_eq!(take(0).parse(&b"a"[..]), (&b"a"[..], Ok(&b""[..])));
        assert_eq!(take(1).parse(&b"a"[..]), (&b""[..],  Ok(&b"a"[..])));
        assert_eq!(take(2).parse(&b"a"[..]), (&b"a"[..], Err(Error::unexpected())));
        assert_eq!(take(3).parse(&b"a"[..]), (&b"a"[..], Err(Error::unexpected())));
        assert_eq!(take(1).parse(&b"ab"[..]), (&b"b"[..], Ok(&b"a"[..])));
        assert_eq!(take(2).parse(&b"ab"[..]), (&b""[..],  Ok(&b"ab"[..])));
    }

    #[test]
    fn take_while_test() {
        assert_eq!(take_while(|c| c != b'b').parse(&b""[..]), (&b""[..],    Ok(&b""[..])));
        assert_eq!(take_while(|c| c != b'b').parse(&b"a"[..]), (&b""[..],    Ok(&b"a"[..])));
        assert_eq!(take_while(|c| c != b'b').parse(&b"b"[..]), (&b"b"[..],   Ok(&b""[..])));
        assert_eq!(take_while(|c| c != b'b').parse(&b"abc"[..]), (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(take_while(|c| c != b'b').parse(&b"bbc"[..]), (&b"bbc"[..], Ok(&b""[..])));
        assert_eq!(take_while(|c| c != b'b').parse(&b"bbc"[..]), (&b"bbc"[..], Ok(&b""[..])));
        assert_eq!(take_while(|c| c != b'b').parse(&b"abc"[..]), (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(take_while(|c| c != b'b').parse(&b"acc"[..]), (&b""[..],    Ok(&b"acc"[..])));
    }

    #[test]
    fn take_while1_test() {
        assert_eq!(take_while1(|c| c != b'b').parse(&b""[..]), (&b""[..],    Err(Error::unexpected())));
        assert_eq!(take_while1(|c| c != b'b').parse(&b"a"[..]), (&b""[..],    Ok(&b"a"[..])));
        assert_eq!(take_while1(|c| c != b'b').parse(&b"b"[..]), (&b"b"[..],   Err(Error::unexpected())));
        assert_eq!(take_while1(|c| c != b'b').parse(&b"ab"[..]), (&b"b"[..],   Ok(&b"a"[..])));
        assert_eq!(take_while1(|c| c != b'b').parse(&b"abc"[..]), (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(take_while1(|c| c != b'b').parse(&b"bbc"[..]), (&b"bbc"[..], Err(Error::unexpected())));
        assert_eq!(take_while1(|c| c != b'b').parse(&b"bbc"[..]), (&b"bbc"[..], Err(Error::unexpected())));
        assert_eq!(take_while1(|c| c != b'b').parse(&b"abc"[..]), (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(take_while1(|c| c != b'b').parse(&b"acc"[..]), (&b""[..],    Ok(&b"acc"[..])));
    }

    #[test]
    fn peek_next_test() {
        assert_eq!(peek_next().parse(&b"abc"[..]), (&b"abc"[..], Ok(b'a')));
        assert_eq!(peek_next().parse(&b"abc"[..]), (&b"abc"[..], Ok(b'a')));
        assert_eq!(peek_next().parse(&b""[..]),    (&b""[..],    Err(Error::unexpected())));
        assert_eq!(peek_next().parse(&b""[..]),    (&b""[..],    Err(Error::unexpected())));
    }

    #[test]
    fn satisfy_with_test() {
        let mut m1 = 0;
        let mut n1 = 0;
        assert_eq!(satisfy_with(|m| { m1 += 1; m % 8 }, |n| { n1 += 1; n == 1 }).parse(&b"abc"[..]), (&b"bc"[..], Ok(1)));
        assert_eq!(m1, 1);
        assert_eq!(n1, 1);

        let mut m2 = 0;
        let mut n2 = 0;
        assert_eq!(satisfy_with(|m| { m2 += 1; m % 8 }, |n| { n2 += 1; n == 1 }).parse(&b""[..]), (&b""[..], Err(Error::unexpected())));
        assert_eq!(m2, 0);
        assert_eq!(n2, 0);
    }

    #[test]
    fn string_test() {
        assert_eq!(string(b""     ).parse(&b""[..]),      (&b""[..],    Ok(&b""[..])));
        assert_eq!(string(b"a"    ).parse(&b""[..]),     (&b""[..],    Err(Error::expected(b'a'))));
        assert_eq!(string(b"a"    ).parse(&b"a"[..]),     (&b""[..],    Ok(&b"a"[..])));
        assert_eq!(string(b"a"    ).parse(&b"b"[..]),     (&b"b"[..],   Err(Error::expected(b'a'))));
        assert_eq!(string(b"a"    ).parse(&b"abc"[..]),     (&b"bc"[..],  Ok(&b"a"[..])));
        assert_eq!(string(b"ab"   ).parse(&b"abc"[..]),    (&b"c"[..],   Ok(&b"ab"[..])));
        assert_eq!(string(b"abc"  ).parse(&b"abc"[..]),   (&b""[..],    Ok(&b"abc"[..])));
        assert_eq!(string(b"abcd" ).parse(&b"abc"[..]),  (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string(b"abcde").parse(&b"abc"[..]), (&b""[..],    Err(Error::expected(b'd'))));
        assert_eq!(string(b"ac"   ).parse(&b"abc"[..]),    (&b"bc"[..],  Err(Error::expected(b'c'))));
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
