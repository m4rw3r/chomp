//! Basic combinators.

use std::iter::FromIterator;

use {ParseResult, Input};

use internal::State;
use internal::{IntoInner, InputBuffer, InputClone};
use iter::{EndState, Iter};


/// Applies the parser ``p`` exactly ``num`` times, propagating any error or incomplete state.
///
#[cfg_attr(feature = "verbose_error", doc = "
```
use chomp::{ParseResult, Error, Input, count, token, take_remainder};

let p1 = Input::new(b\"a  \");
let p2 = Input::new(b\"aa \");
let p3 = Input::new(b\"aaa\");

fn parse(i: Input<u8>) -> ParseResult<u8, Vec<u8>, Error<u8>> {
    count(i, 2, |i| token(i, b'a'))
}

assert_eq!(parse(p1).unwrap_err(), Error::Expected(b'a'));
assert_eq!(parse(p2).unwrap(), &[b'a', b'a']);

// TODO: Update once a proper way to extract data and remainder has been implemented
// a slightly odd way to obtain the remainder of the input stream, temporary:
let d: ParseResult<_, (_, Vec<_>), Error<_>> =
    parse(p3).bind(|i, d| take_remainder(i).bind(|i, r| i.ret((r, d))));
let (buf, data) = d.unwrap();

assert_eq!(buf, b\"a\");
assert_eq!(data, &[b'a', b'a']);
```
")]
#[inline]
pub fn count<'a, I, T, E, F, U>(i: Input<'a, I>, num: usize, p: F) -> ParseResult<'a, I, T, E>
  where I: Copy,
        U: 'a,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
        T: FromIterator<U> {
    // If we have gotten an item, if this is false after from_iter we have failed
    let mut count = 0;
    let mut iter  = Iter::new(i, p);

    let result: T      = FromIterator::from_iter(iter.by_ref()
                                                 .take(num)
                                                 .inspect(|_| count = count + 1 ));
    let (buffer, last) = iter.end_state();

    if count == num {
        buffer.ret(result)
    } else {
        // Can only be less than num here since take() limits it.
        // Just propagate the last state from the iterator.
        match last {
            EndState::Incomplete(n) => buffer.incomplete(n),
            EndState::Error(b, e)     => buffer.replace(b).err(e),
        }
    }
}

/// Tries the parser ``f``, on success it yields the parsed value, on failure ``default`` will be
/// yielded instead.
///
/// Incomplete state is propagated. Backtracks on error.
///
/// ```
/// use chomp::{Input, option, token};
///
/// let p1 = Input::new(b"abc");
/// let p2 = Input::new(b"bbc");
///
/// assert_eq!(option(p1, |i| token(i, b'a'), b'd').unwrap(), b'a');
/// assert_eq!(option(p2, |i| token(i, b'a'), b'd').unwrap(), b'd');
/// ```
#[inline]
pub fn option<'a, I, T, E, F>(i: Input<'a, I>, f: F, default: T) -> ParseResult<'a, I, T, E>
  where I: 'a + Copy,
        F: FnOnce(Input<'a, I>) -> ParseResult<'a, I, T, E> {
    match f(i.clone()).into_inner() {
        State::Data(b, d)    => b.ret(d),
        State::Error(_, _)   => i.ret(default),
        State::Incomplete(n) => i.incomplete(n),
    }
}

/// Tries to match the parser ``f``, if ``f`` fails it tries ``g``. Returns the success value of
/// the first match, otherwise the error of the last one if both fail.
///
/// Incomplete state is propagated from the first one to report incomplete.
///
#[cfg_attr(feature = "verbose_error", doc = "
```
use chomp::{Input, Error, or, token};

let p1 = Input::new(b\"abc\");
let p2 = Input::new(b\"bbc\");
let p3 = Input::new(b\"cbc\");

assert_eq!(or(p1, |i| token(i, b'a'), |i| token(i, b'b')).unwrap(), b'a');
assert_eq!(or(p2, |i| token(i, b'a'), |i| token(i, b'b')).unwrap(), b'b');
assert_eq!(or(p3, |i| token(i, b'a'), |i| token(i, b'b')).unwrap_err(), Error::Expected(b'b'));
```
")]
#[inline]
pub fn or<'a, I, T, E, F, G>(i: Input<'a, I>, f: F, g: G) -> ParseResult<'a, I, T, E>
  where F: FnOnce(Input<'a, I>) -> ParseResult<'a, I, T, E>,
        G: FnOnce(Input<'a, I>) -> ParseResult<'a, I, T, E> {
    match f(i.clone()).into_inner() {
        State::Data(b, d)    => b.ret(d),
        State::Error(_, _)   => g(i),
        State::Incomplete(n) => i.incomplete(n),
    }
}

/// Parses many instances of ``f`` until it does no longer match, returning all matches.
///
/// Note: If the last parser succeeds on the last input item then this parser is still considered
/// incomplete as there might be more data to fill.
///
/// Note: Allocates data.
///
/// ```
/// use chomp::{ParseResult, Error, Input, token, many, take_while1};
///
/// let p = Input::new(b"a,bc,cd ");
///
/// let r: ParseResult<_, Vec<&[u8]>, Error<u8>> =
///     many(p, |i| take_while1(i, |c| c != b',' && c != b' ').bind(|i, c|
///         token(i, b',').bind(|i, _| i.ret(c))));
/// let v = r.unwrap();
///
/// assert_eq!(v.len(), 2);
/// assert_eq!(v[0], b"a");
/// assert_eq!(v[1], b"bc");
/// ```
#[inline]
pub fn many<'a, I, T, E, F, U>(i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
  where I: Copy,
        U: 'a,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
        T: FromIterator<U> {
    let mut iter = Iter::new(i, f);

    let result: T = FromIterator::from_iter(iter.by_ref());

    match iter.end_state() {
        // Ok, last parser failed, we have iterated all.
        // Return remainder of buffer and the collected result
        (s, EndState::Error(_, _))   => s.ret(result),
        // Nested parser incomplete, propagate
        (s, EndState::Incomplete(n)) => if s.buffer().len() == 0 && s.is_last_slice() {
            s.ret(result)
        } else {
            s.incomplete(n)
        },
    }
}

/// Parses at least one instance of ``f`` and continues until it does no longer match,
/// returning all matches.
///
/// Note: If the last parser succeeds on the last input item then this parser is still considered
/// incomplete as there might be more data to fill.
///
/// Note: Allocates data.
///
#[cfg_attr(feature = "verbose_error", doc = "
```
use chomp::{ParseResult, Error, Input, token, many1, take_while1};

let p1 = Input::new(b\"a \");
let p2 = Input::new(b\"a, \");

fn parse(i: Input<u8>) -> ParseResult<u8, Vec<&[u8]>, Error<u8>> {
    many1(i, |i| take_while1(i, |c| c != b',' && c != b' ').bind(|i, c|
        token(i, b',').bind(|i, _| i.ret(c))))
}

assert_eq!(parse(p1).unwrap_err(), Error::Expected(b','));
assert_eq!(parse(p2).unwrap(), &[b\"a\"]);
```
")]
#[inline]
pub fn many1<'a, I, T, E, F, U>(i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
  where I: Copy,
        U: 'a,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
        T: FromIterator<U> {
    // If we managed to parse anything
    let mut item = false;
    // If we have gotten an item, if this is false after from_iter we have failed
    let mut iter = Iter::new(i, f);

    let result: T = FromIterator::from_iter(iter.by_ref().inspect(|_| item = true ));

    if !item {
        match iter.end_state() {
            (s, EndState::Error(b, e))   => s.replace(b).err(e),
            (s, EndState::Incomplete(n)) => s.incomplete(n),
        }
    } else {
        match iter.end_state() {
            (s, EndState::Error(_, _))   => s.ret(result),
            // TODO: Indicate potentially more than 1?
            (s, EndState::Incomplete(n)) => if s.buffer().len() == 0 && s.is_last_slice() {
                s.ret(result)
            } else {
                s.incomplete(n)
            },
        }
    }
}

/// Runs the given parser until it fails, discarding matched input.
///
/// Incomplete state will be propagated.
///
/// This is more efficient to use compared to using ``many`` and then just discarding the result as
/// ``many`` allocates a separate data structure to contain the data before proceeding.
///
/// ```
/// use chomp::{Input, skip_many, token};
///
/// let p = Input::new(b"aaaabc");
///
/// assert_eq!(skip_many(p, |i| token(i, b'a')).bind(|i, _| token(i, b'b')).unwrap(), b'b');
/// ```
#[inline]
pub fn skip_many<'a, I, T, E, F>(mut i: Input<'a, I>, mut f: F) -> ParseResult<'a, I, (), E>
  where T: 'a, F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
    loop {
        match f(i.clone()).into_inner() {
            State::Data(b, _)    => i = b,
            State::Error(_, _)   => break,
            State::Incomplete(n) => return i.incomplete(n),
        }
    }

    i.ret(())
}
