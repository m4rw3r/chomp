//! Basic parsers.

use std::mem;

use input::Input;
use parse_result::SimpleResult;
use primitives::InputBuffer;

pub use self::error::Error;
#[cfg(all(not(feature="noop_error"), feature="backtrace"))]
pub use self::error::StackFrame;

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
        Some(_)          => i.err(Error::unexpected()),
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
pub fn token<I: Copy + PartialEq>(i: Input<I>, t: I) -> SimpleResult<I, I> {
    let b = i.buffer();

    match b.first() {
        None               => i.incomplete(1),
        Some(&c) if t == c => i.replace(&b[1..]).ret(c),
        Some(_)            => i.err(Error::expected(t)),
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
        Some(_)            => i.err(Error::unexpected()),
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
        Some(0) => i.err(Error::unexpected()),
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
            return i.replace(&b[j..]).err(Error::expected(d[j]))
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
        i.err(Error::unexpected())
    }
}

#[cfg(not(any(feature="noop_error", feature="backtrace")))]
mod error {
    use std::any;
    use std::error;
    use std::fmt;

    /// Common error for the basic Chomp parsers.
    ///
    /// This is the common error for the basic Chomp parsers. It will contain information about what a
    /// parser expected or if it encountered something unexpected (in the case of user supplied
    /// predicates, eg. `satisfy`).
    ///
    /// This is coupled with the state found in the error state of the `ParseResult` type.
    #[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
    pub struct Error<I> {
        /// `Some(T)` if it expected a specific token, `None` if it encountered something unexpected.
        expected: Option<I>,
    }

    impl<I: fmt::Debug> fmt::Debug for Error<I> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self.expected {
                Some(ref c) => write!(f, "Error(Expected({:?}))", c),
                None        => write!(f, "Error(Unexpected)"),
            }
        }
    }

    impl<I> Error<I> {
        /// Creates a new Unexpected error.
        ///
        /// Should be used when the error value is not important.
        #[inline(always)]
        pub fn new() -> Self {
            Error {
                expected: None,
            }
        }

        /// Creates a new Unexpected error.
        ///
        /// Should be used when the token was unexpected, as in the case of `satisfy` where a user
        /// provided predicate is provided.
        #[inline(always)]
        pub fn unexpected() -> Self {
            Error {
                expected: None,
            }
        }

        /// Creates a new Expected error.
        ///
        /// Should be used when a specific token was expected.
        #[inline(always)]
        pub fn expected(i: I) -> Self {
            Error {
                expected: Some(i),
            }
        }

        /// Returns `Some(&I)` if a specific token was expected, `None` otherwise.
        #[inline]
        pub fn expected_token(&self) -> Option<&I> {
            self.expected.as_ref()
        }
    }

    impl<I> fmt::Display for Error<I>
      where I: fmt::Debug {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self.expected.as_ref() {
                Some(ref c) => write!(f, "expected {:?}", *c),
                None        => write!(f, "unexpected"),
            }
        }
    }

    impl<I: any::Any + fmt::Debug> error::Error for Error<I> {
        fn description(&self) -> &str {
            match self.expected.as_ref() {
                Some(_) => "expected a certain token, received another",
                None    => "received an unexpected token",
            }
        }
    }
}

#[cfg(all(not(feature="noop_error"), feature="backtrace"))]
mod error {
    use std::any;
    use std::error;
    use std::fmt;
    use std::os::raw;
    use std::ops;
    use std::borrow::Cow;

    use backtrace;

    /// Common error for the basic Chomp parsers. `backtrace` enabled.
    ///
    /// This is the common error for the basic Chomp parsers. It will contain information about what a
    /// parser expected or if it encountered something unexpected (in the case of user supplied
    /// predicates, eg. `satisfy`).
    ///
    /// This is coupled with the state found in the error state of the `ParseResult` type.
    #[derive(Clone, Ord, PartialOrd, Hash)]
    pub struct Error<I> {
        /// `Some(T)` if it expected a specific token, `None` if it encountered something unexpected.
        expected: Option<I>,
        trace:    Vec<*mut raw::c_void>,
    }

    impl<I: PartialEq> PartialEq<Error<I>> for Error<I> {
        fn eq(&self, other: &Error<I>) -> bool {
            self.expected == other.expected
        }
    }

    impl<I: Eq> Eq for Error<I> {}

    impl<I: fmt::Debug> fmt::Debug for Error<I> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self.expected {
                Some(ref c) => try!(write!(f, "Error(Expected({:?}), \n", c)),
                None        => try!(write!(f, "Error(Unexpected, \n")),
            }

            for frame in self.trace().into_iter() {
                // TODO: is there any nicer way to get a decent indent?
                try!(write!(f, "    "));
                try!(fmt::Debug::fmt(&frame, f));
                try!(write!(f, "\n"));
            }

            write!(f, ")")
        }
    }

    /// A stack frame with information gathered from the runtime.
    ///
    /// See notes from the `backtrace` crate about when this information might and might not be
    /// available.
    #[derive(Clone, Eq, PartialEq)]
    pub struct StackFrame {
        /// Instruction pointer
        pub ip:   *mut raw::c_void,
        /// Function name if found
        pub name: Option<String>,
        /// Address
        pub addr: Option<*mut raw::c_void>,
        /// Source file name
        pub file: Option<String>,
        /// Source line number
        pub line: Option<u32>,
    }

    impl fmt::Debug for StackFrame {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let n = self.line.map(|n| Cow::Owned(format!("{}", n)))
                .unwrap_or(Cow::Borrowed("<unknown>"));

            write!(f, "{:16p} - {} ({}:{})",
                self.ip,
                self.name.as_ref().map(ops::Deref::deref).unwrap_or("<unknown>"),
                self.file.as_ref().map(ops::Deref::deref).unwrap_or("<unknown>"),
                n,
                )
        }
    }

    macro_rules! new_trace {
        () => { {
            let mut v = Vec::new();

            backtrace::trace(&mut |frame| {
                v.push(frame.ip());

                true
            });

            v
        } }
    }

    impl<I> Error<I> {
        /// Creates a new Unexpected error.
        ///
        /// Should be used when the error value is not important.
        #[inline(always)]
        pub fn new() -> Self {
            Error {
                expected: None,
                trace:    new_trace!(),
            }
        }

        /// Creates a new Unexpected error.
        ///
        /// Should be used when the token was unexpected, as in the case of `satisfy` where a user
        /// provided predicate is provided.
        #[inline(always)]
        pub fn unexpected() -> Self {
            Error {
                expected: None,
                trace:    new_trace!(),
            }
        }

        /// Creates a new Expected error.
        ///
        /// Should be used when a specific token was expected.
        #[inline(always)]
        pub fn expected(i: I) -> Self {
            Error {
                expected: Some(i),
                trace:    new_trace!(),
            }
        }

        /// Returns `Some(&I)` if a specific token was expected, `None` otherwise.
        #[inline]
        pub fn expected_token(&self) -> Option<&I> {
            self.expected.as_ref()
        }

        /// Returns a stack-trace to where the error was created.
        pub fn trace(&self) -> Vec<StackFrame> {
            self.trace.iter().map(|&ip| {
                let mut f = StackFrame { ip: ip, name: None, addr: None, file: None, line: None };

                backtrace::resolve(ip, &mut |sym| {
                    f.name = sym.name().map(String::from_utf8_lossy).map(|mangled| {
                        let mut name = String::new();

                        match backtrace::demangle(&mut name, &mangled) {
                            Ok(()) => name,
                            Err(_) => mangled.into_owned(),
                        }
                    });
                    f.addr = sym.addr();
                    f.file = sym.filename().map(String::from_utf8_lossy).map(Cow::into_owned);
                    f.line = sym.lineno();
                });

                f
            }).collect()
        }
    }

    impl<I> fmt::Display for Error<I>
      where I: fmt::Debug {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self.expected.as_ref() {
                Some(ref c) => write!(f, "expected {:?}", *c),
                None        => write!(f, "unexpected"),
            }
        }
    }

    impl<I: any::Any + fmt::Debug> error::Error for Error<I> {
        fn description(&self) -> &str {
            match self.expected.as_ref() {
                Some(_) => "expected a certain token, received another",
                None    => "received an unexpected token",
            }
        }
    }
}

#[cfg(feature="noop_error")]
mod error {
    use std::any;
    use std::error;
    use std::fmt;
    use std::marker::PhantomData;

    /// Common error for the basic Chomp parsers. `noop_error` enabled.
    ///
    /// This is the common error for the basic Chomp parsers. It is an empty type signalling that a
    /// parser failed at the location specified in the error state from `ParseResult`.
    #[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
    pub struct Error<I> {
        _i: PhantomData<I>,
    }

    impl<I> Error<I> {
        /// Creates a new Unexpected error.
        ///
        /// Should be used when the error value is not important.
        #[inline(always)]
        pub fn new() -> Self {
            Error {
                _i: PhantomData,
            }
        }

        /// Creates a new Unexpected error.
        ///
        /// Should be used when the token was unexpected, as in the case of `satisfy` where a user
        /// provided predicate is provided.
        #[inline(always)]
        pub fn unexpected() -> Self {
            Error {
                _i: PhantomData,
            }
        }

        /// Creates a new Expected error.
        ///
        /// Should be used when a specific token was expected.
        #[inline(always)]
        pub fn expected(_i: I) -> Self {
            Error {
                _i: PhantomData,
            }
        }

        /// Always returns `None` since the feature `noop_error` is enabled.
        pub fn expected_token(&self) -> Option<&I> {
            None
        }
    }

    impl<I> fmt::Display for Error<I>
      where I: fmt::Debug {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "parse error")
        }
    }

    impl<I: any::Any + fmt::Debug> error::Error for Error<I> {
        fn description(&self) -> &str {
            &"parse error"
        }
    }
}

#[cfg(test)]
mod test {
    use primitives::input::{new, DEFAULT, END_OF_INPUT};
    use primitives::IntoInner;
    use primitives::State;
    use super::*;
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
        assert_eq!(token(new(DEFAULT, b"bb"), b'a').into_inner(), State::Error(b"bb", Error::expected(b'a')));
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
        assert_eq!(take_while1(new(DEFAULT, b"bbc"), |c| c != b'b').into_inner(), State::Error(&b"bbc"[..], Error::unexpected()));
        assert_eq!(take_while1(new(END_OF_INPUT, b"bbc"), |c| c != b'b').into_inner(), State::Error(&b"bbc"[..], Error::unexpected()));
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
        assert_eq!(string(new(DEFAULT, b"abc"), b"ac").into_inner(), State::Error(b"bc", Error::expected(b'b')));

        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"a").into_inner(), State::Data(new(END_OF_INPUT, b"bc"), &b"a"[..]));
        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"ab").into_inner(), State::Data(new(END_OF_INPUT, b"c"), &b"ab"[..]));
        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"abc").into_inner(), State::Data(new(END_OF_INPUT, b""), &b"abc"[..]));
        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"abcd").into_inner(), State::Incomplete(1));
        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"abcde").into_inner(), State::Incomplete(2));
        assert_eq!(string(new(END_OF_INPUT, b"abc"), b"ac").into_inner(), State::Error(b"bc", Error::expected(b'b')));
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
    fn error_test() {
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
        let frame = trace.iter().find(|frame| frame.name.as_ref().map(|n| n.starts_with("parsers::test::backtrace_test")).unwrap_or(false));

        assert!(frame.is_some());
    }
}
