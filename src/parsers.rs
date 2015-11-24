//! Basic parsers.

use std::mem;
use std::any;
use std::error;
use std::fmt;

#[cfg(not(feature = "verbose_error"))]
use std::marker::PhantomData;

use input::Input;
use parse_result::SimpleResult;
use primitives::InputBuffer;

/// Matches any item, returning it if present.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::{Input, any};
///
/// let p = Input::new(b"abc");
///
/// assert_eq!(any(p).unwrap(), b'a');
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
/// use chomp::{Input, satisfy};
///
/// let p = Input::new(b"abc");
///
/// assert_eq!(satisfy(p, |c| c == b'a').unwrap(), b'a');
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

/// Matches a single token, returning the match on success.
///
/// If the buffer length is 0 this parser is considered incomplete.
///
/// ```
/// use chomp::{Input, token};
///
/// let p = Input::new(b"abc");
///
/// assert_eq!(token(p, b'a').unwrap(), b'a');
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
/// use chomp::{Input, not_token};
///
/// let p1 = Input::new(b"abc");
///
/// assert_eq!(not_token(p1, b'b').unwrap(), b'a');
///
/// let p2 = Input::new(b"abc");
///
/// assert_eq!(not_token(p2, b'b').unwrap(), b'a');
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
/// use chomp::{Input, peek};
///
/// let p1 = Input::new(b"abc");
///
/// assert_eq!(peek(p1).unwrap(), Some(b'a'));
///
/// let p2 = Input::new(b"");
///
/// assert_eq!(peek(p2).unwrap(), None);
/// ```
#[inline]
pub fn peek<I: Copy>(i: Input<I>) -> SimpleResult<I, Option<I>> {
    let d = i.buffer().first().cloned();

    i.ret(d)
}

/// Matches ``num`` items no matter what they are, returning a slice of the matched items.
///
/// If the buffer length is less than ``num`` this parser is considered incomplete.
///
/// ```
/// use chomp::{Input, take};
///
/// let p = Input::new(b"abcd");
///
/// assert_eq!(take(p, 3).unwrap(), b"abc");
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
/// use chomp::{Input, take_while};
///
/// let p = Input::new(b"abcdcba");
///
/// assert_eq!(take_while(p, |c| c == b'a' || c == b'b').unwrap(), b"ab");
/// ```
///
/// Without managing to match anything:
///
/// ```
/// use chomp::{Input, take_while};
///
/// let p = Input::new(b"abcdcba");
///
/// assert_eq!(take_while(p, |c| c == b'z').unwrap(), b"");
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
/// use chomp::{Input, take_while1};
///
/// let p = Input::new(b"abcdcba");
///
/// assert_eq!(take_while1(p, |c| c == b'a' || c == b'b').unwrap(), b"ab");
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
/// use chomp::{Input, take_till};
///
/// let p = Input::new(b"abcdef");
///
/// assert_eq!(take_till(p, |c| c == b'd').unwrap(), b"abc");
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
/// use chomp::{Input, scan};
///
/// let p = Input::new(b"/*test*of*scan*/ foo");
///
/// let r = scan(p, false, |s, c| match (s, c) {
///     (true, b'/') => None,
///     (_,    b'*') => Some(true),
///     (_, _)       => Some(false),
/// });
///
/// assert_eq!(r.unwrap(), b"/*test*of*scan*");
/// ```
#[inline]
pub fn scan<I: Copy, S,  F>(i: Input<I>, s: S, mut f: F) -> SimpleResult<I, &[I]>
  where F: FnMut(S, I) -> Option<S> {
    let b     = i.buffer();
    let mut state = Some(s);

    match b.iter().position(|&c| { state = f(mem::replace(&mut state, None).unwrap(), c); state.is_none()}) {
        Some(n) => i.replace(&b[n..]).ret(&b[0..n]),
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => i.incomplete(1),
    }
}

/// Matches the remainder of the buffer and returns it, always succeeds.
///
/// ```
/// use chomp::{Input, take_remainder};
///
/// let p = Input::new(b"abcd");
///
/// assert_eq!(take_remainder(p).unwrap(), b"abcd");
/// ```
#[inline]
pub fn take_remainder<I: Copy>(i: Input<I>) -> SimpleResult<I, &[I]> {
    let b = i.buffer();
    // Last slice and we have just read everything of it, replace with zero-sized slice:
    //
    // Hack to avoid branch and overflow, does not matter where this zero-sized slice is
    // allocated
    i.replace(&b[..0]).ret(b)
}

/// Matches the given slice against the parser, returning the matched slice upon success.
///
/// If the length of the contained data is shorter than the given slice this parser is considered
/// incomplete.
///
/// ```
/// use chomp::{Input, string};
///
/// let p = Input::new(b"abcdef");
///
/// assert_eq!(string(p, b"abc").unwrap(), b"abc");
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
            return err::string(i, j, s);
        }
    }

    i.replace(&b[s.len()..]).ret(d)
}

/// Matches the end of the input.
///
/// ```
/// use chomp::{Input, token, eof};
///
/// let i = Input::new(b"a");
///
/// let r = token(i, b'a').bind(|i, _| eof(i));
///
/// assert_eq!(r.unwrap(), ());
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
#[cfg(feature = "verbose_error")]
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Error<I> {
    /// Expected a specific token
    Expected(I),
    /// Did not expect the token present in the input stream
    Unexpected,
    /// Expected a specific string of tokens
    String(Vec<I>),
}

#[cfg(feature = "verbose_error")]
impl<I> fmt::Display for Error<I>
  where I: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Expected(ref c) => write!(f, "expected {:?}", *c),
            Error::Unexpected      => write!(f, "unexpected"),
            Error::String(ref s)   => write!(f, "expected {:?}", *s),
        }
    }
}

#[cfg(feature = "verbose_error")]
impl<I: any::Any + fmt::Debug> error::Error for Error<I> {
    fn description(&self) -> &str {
        match *self {
            Error::Expected(_) => "expected a certain token, received another",
            Error::Unexpected  => "received an unexpected token",
            Error::String(_)   =>
                "expected a certain string of tokens, encountered an unexpected token",
        }
    }
}

#[cfg(feature = "verbose_error")]
mod err {
    //! This is a private module to contain the constructors for the verbose error type.
    //!
    //! All constructors are #[inline(always)] and will construct the appropriate error type.

    use input::Input;
    use parse_result::ParseResult;
    use super::Error;

    #[inline(always)]
    pub fn unexpected<I>() -> Error<I> {
        Error::Unexpected
    }

    #[inline(always)]
    pub fn expected<'a, I>(i: I) -> Error<I> {
        Error::Expected(i)
    }


    #[inline(always)]
    pub fn string<'a, 'b, I, T>(i: Input<'a, I>, _offset: usize, expected: &'b [I])
        -> ParseResult<'a, I, T, Error<I>>
      where I: Copy {
        i.err(Error::String(expected.to_vec()))
    }
}

/// Common error for the basic Chomp parsers, noop version.
///
/// An empty error type, it only indicates that an error occurred. The error state in the
/// `ParseResult` type provides the position of the error.
///
/// This is coupled with the state found in the error state of the `ParseResult` type.
#[cfg(not(feature = "verbose_error"))]
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Error<I>(PhantomData<I>);

#[cfg(not(feature = "verbose_error"))]
impl<I: fmt::Debug> fmt::Display for Error<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "generic parse error (chomp was compiled without --feature verbose_error)")
    }
}

#[cfg(not(feature = "verbose_error"))]
impl<I: any::Any + fmt::Debug> error::Error for Error<I> {
    fn description(&self) -> &str {
        "generic parse error (chomp was compiled without --feature verbose_error)"
    }
}

#[cfg(not(feature = "verbose_error"))]
mod err {
    //! This is a private module to contain the constructors for the smaller error type.
    //!
    //! All constructors are #[inline(always)], and will just noop the data.

    use std::marker::PhantomData;

    use input::Input;
    use parse_result::ParseResult;
    use super::Error;


    #[inline(always)]
    pub fn unexpected<I>() -> Error<I> {
        Error(PhantomData)
    }

    #[inline(always)]
    pub fn expected<'a, I>(_: I) -> Error<I> {
        Error(PhantomData)
    }

    #[inline(always)]
    pub fn string<'a, 'b, I, T>(i: Input<'a, I>, offset: usize, _expected: &'b [I])
        -> ParseResult<'a, I, T, Error<I>>
      where I: Copy {
        use primitives::InputBuffer;

        let b = i.buffer();

        i.replace(&b[offset..]).err(Error(PhantomData))
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

        let i = Input::new(b"123.4567 ");

        let p = decimal(i).bind(|i, real|
            token(i, b'.').bind(|i, _|
                decimal(i).bind(|i, frac|
                    i.ret((real, frac)))));

        let d: SimpleResult<_, _> = p.bind(|i, num| take_remainder(i)
                                           .bind(|i, r| i.ret((r, num))));
        let (buf, state) = d.unwrap();

        assert_eq!(buf, &[b' ']);
        assert_eq!(state, (123, 4567));
    }

    #[test]
    fn parse_remainder_empty() {
        let i = Input::new(b"");

        let r = take_remainder(i);

        assert_eq!(r.unwrap(), b"" as &[u8]);
    }

    #[test]
    #[should_panic]
    fn take_while1_empty() {
        let n = Input::new(b"");

        let r = take_while1(n, |_| true);

        assert_eq!(r.unwrap(), b"");
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
}
