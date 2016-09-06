//! Basic combinators.

#[macro_use]
mod macros;

pub mod bounded;

use std::iter::FromIterator;

use either::Either;

use types::{Input, Parser};

/// Applies the parser `p` exactly `num` times collecting all items into `T: FromIterator`.
///
/// ```
/// use chomp::prelude::*;
///
/// let parse = || count(2, || token(b'a'));
///
/// assert_eq!(parse_only(parse(), b"a  "), Err((&b"  "[..], Error::expected(b'a'))));
/// assert_eq!(parse_only(parse(), b"aa "), Ok(vec![b'a', b'a']));
///
/// let with_remainder = parse().bind(|d| take_remainder().map(|r| (r, d)));
///
/// assert_eq!(parse_only(with_remainder, b"aaa"), Ok((&b"a"[..], vec![b'a', b'a'])));
/// ```
#[inline]
pub fn count<I: Input, P, T, F>(num: usize, p: F) -> impl Parser<I, Output=T, Error=P::Error>
  where F: FnMut() -> P,
        P: Parser<I>,
        T: FromIterator<P::Output> {
    bounded::many(num, p)
}

/// Tries the parser `f`, on success it yields the parsed value, on failure `default` will be
/// yielded instead.
///
/// Incomplete state is propagated. Backtracks on error.
///
/// ```
/// #![feature(conservative_impl_trait)]
/// use chomp::prelude::{U8Input, Parser, Error, parse_only, option, token};
///
/// fn f<I: U8Input>() -> impl Parser<I, Output=u8, Error=Error<u8>> {
///     option(token(b'a'), b'd')
/// }
///
/// assert_eq!(parse_only(f(), b"abc"), Ok(b'a'));
/// assert_eq!(parse_only(f(), b"bbc"), Ok(b'd'));
/// ```
#[inline]
pub fn option<I: Input, P>(p: P, default: P::Output) -> impl Parser<I, Output=P::Output, Error=P::Error>
  where P: Parser<I> {
    move |i: I| {
        let m = i.mark();

        match p.parse(i) {
            (b, Ok(d))  => (b, Ok(d)),
            (b, Err(_)) => (b.restore(m), Ok(default)),
        }
    }
}

/// Attempts the left parser first and then the right parser if the first parser fails. Result is
/// returned as an `Either<T, U>` depending on which parser succeeded.
///
/// NOTE: If both parsers have the same return-type, use `or` instead.
///
/// ```
/// use chomp::prelude::{Error, parse_only, either, token, Left, Right};
///
/// let p = || either(token(b'a'), token(b'b'));
///
/// assert_eq!(parse_only(p(), b"a"), Ok(Left(b'a')));
/// assert_eq!(parse_only(p(), b"b"), Ok(Right(b'b')));
/// assert_eq!(parse_only(p(), b"c"), Err((&b"c"[..], Error::expected(b'b'))));
/// ```
#[inline]
pub fn either<I, L, R>(l: L, r: R) -> impl Parser<I, Output=Either<L::Output, R::Output>, Error=L::Error>
  where I: Input,
        L: Parser<I>,
        R: Parser<I, Error=L::Error> {
    move |i: I| {
        let m = i.mark();

        match l.parse(i) {
            (b, Ok(l_t))  => (b, Ok(Either::Left(l_t))),
            (b, Err(_)) => match r.parse(b.restore(m)) {
                (c, Ok(r_t))  => (c, Ok(Either::Right(r_t))),
                (c, Err(r_e)) => (c, Err(r_e))
            }
        }
    }
}

/// Parses many instances of `f` until it does no longer match, collecting all matches into the
/// type `T: FromIterator`.
///
/// Note: Allocates data.
///
/// ```
/// use chomp::prelude::{Parser, parse_only, token, many, take_while1};
///
/// let r: Result<Vec<_>, _> = parse_only(
///     many(|| take_while1(|c| c != b',' && c != b' ').skip(token(b','))),
///     b"a,bc,cd ");
///
/// assert_eq!(r, Ok(vec![&b"a"[..], &b"bc"[..]]));
/// ```
#[inline]
pub fn many<I: Input, T, F, P>(f: F) -> impl Parser<I, Output=T, Error=P::Error>
  where F: FnMut() -> P,
        P: Parser<I>,
        T: FromIterator<P::Output> {
    bounded::many(.., f)
}

/// Parses at least one instance of `f` and continues until it does no longer match, collecting
/// all matches into the type `T: FromIterator`.
///
/// Note: If the last parser succeeds on the last input item then this parser is still considered
/// incomplete as there might be more data to fill.
///
/// Note: Allocates data.
///
/// ```
/// use chomp::prelude::{Parser, Error, parse_only, token, many1, take_while1};
///
/// let p = || many1(|| take_while1(|c| c != b',' && c != b' ').skip(token(b',')));
///
/// assert_eq!(parse_only(p(), b"a "), Err((&b" "[..], Error::expected(b','))));
/// assert_eq!(parse_only(p(), b"a, "), Ok(vec![&b"a"[..]]));
/// ```
#[inline]
pub fn many1<I: Input, F, T, P>(f: F) -> impl Parser<I, Output=T, Error=P::Error>
  where F: FnMut() -> P,
        P: Parser<I>,
        T: FromIterator<P::Output> {
    bounded::many(1.., f)
}

/// Applies the parser `R` zero or more times, separated by the parser `F`. All matches from `R`
/// will be collected into the type `T: FromIterator`.
///
/// If the separator or parser registers error or incomplete this parser stops and yields the
/// collected value.
///
/// Incomplete will be propagated from `R` if end of input has not been read.
///
/// ```
/// use chomp::prelude::{parse_only, sep_by, token};
/// use chomp::ascii::decimal;
///
/// let r: Result<Vec<u8>, _> = parse_only(sep_by(decimal, || token(b';')), b"91;03;20");
///
/// assert_eq!(r, Ok(vec![91, 03, 20]));
/// ```
#[inline]
pub fn sep_by<I, T, R, F, P, Q>(p: R, sep: F) -> impl Parser<I, Output=T, Error=P::Error>
  where I: Input,
        T: FromIterator<P::Output>,
        //E: From<N>,
        R: FnMut() -> P,
        F: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error> {
    bounded::sep_by(.., p, sep)
}

/// Applies the parser `R` one or more times, separated by the parser `F`. All matches from `R`
/// will be collected into the type `T: FromIterator`.
///
/// If the separator or parser registers error or incomplete this parser stops and yields the
/// collected value if at least one item has been read.
///
/// Incomplete will be propagated from `R` if end of input has not been read.
///
/// ```
/// use chomp::prelude::{parse_only, sep_by1, token};
/// use chomp::ascii::decimal;
///
/// let r: Result<Vec<u8>, _> = parse_only(sep_by1(decimal, || token(b';')), b"91;03;20");
///
/// assert_eq!(r, Ok(vec![91, 03, 20]));
/// ```
// TODO: Conversion of errors?
#[inline]
pub fn sep_by1<I, T, R, F, P, Q>(p: R, sep: F) -> impl Parser<I, Output=T, Error=P::Error>
  where I: Input,
        T: FromIterator<P::Output>,
        //E: From<N>,
        R: FnMut() -> P,
        F: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error> {
    bounded::sep_by(1.., p, sep)
}

/// Applies the parser `R` multiple times until the parser `F` succeeds and returns a
/// `T: FromIterator` populated by the values yielded by `R`. Consumes the matched part of `F`.
///
/// This parser is considered incomplete if the parser `R` is considered incomplete.
///
/// Errors from `R` are propagated.
///
/// ```
/// use chomp::prelude::{parse_only, many_till, any, token};
///
/// let r: Result<Vec<u8>, _> = parse_only(many_till(any, || token(b';')), b"abc;def");
///
/// assert_eq!(r, Ok(vec![b'a', b'b', b'c']));
/// ```
// TODO: Conversion of errors?
#[inline]
pub fn many_till<I, F, G, P, Q, T>(p: F, end: G) -> impl Parser<I, Output=T, Error=P::Error>
  where I: Input,
        //E: From<N>,
        F: FnMut() -> P,
        G: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error>,
        T: FromIterator<P::Output> {
    bounded::many_till(.., p, end)
}

/// Runs the given parser until it fails, discarding matched input.
///
/// Incomplete state will be propagated.
///
/// This is more efficient compared to using `many` and then just discarding the result as
/// `many` allocates a separate data structure to contain the data before proceeding.
///
/// ```
/// use chomp::prelude::{Parser, parse_only, skip_many, token};
///
/// let r = parse_only(skip_many(|| token(b'a')).then(token(b'b')), b"aaaabc");
///
/// assert_eq!(r, Ok(b'b'));
/// ```
#[inline]
pub fn skip_many<I, F, P>(f: F) -> impl Parser<I, Output=(), Error=P::Error>
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    bounded::skip_many(.., f)
}

/// Runs the given parser until it fails, discarding matched input, expects at least one match.
///
/// Incomplete state will be propagated. Will propagate the error if it occurs during the first
/// attempt.
///
/// This is more efficient compared to using `many1` and then just discarding the result as
/// `many1` allocates a separate data structure to contain the data before proceeding.
///
/// ```
/// use chomp::prelude::{Parser, Error, parse_only, skip_many1, token};
///
/// let p = || skip_many1(|| token(b'a')).then(token(b'b'));
///
/// assert_eq!(parse_only(p(), b"aaaabc"), Ok(b'b'));
/// assert_eq!(parse_only(p(), b"abc"), Ok(b'b'));
///
/// assert_eq!(parse_only(p(), b"bc"), Err((&b"bc"[..], Error::expected(b'a'))));
/// ```
#[inline]
pub fn skip_many1<I, F, P>(f: F) -> impl Parser<I, Output=(), Error=P::Error>
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    bounded::skip_many(1.., f)
}

/// Returns the result of the given parser as well as the slice which matched it.
///
/// ```
/// use chomp::prelude::{parse_only, matched_by};
/// use chomp::ascii::decimal;
///
/// assert_eq!(parse_only(matched_by(decimal()), b"123"), Ok((&b"123"[..], 123u32)));
/// ```
#[inline]
pub fn matched_by<I: Input, F>(f: F) -> impl Parser<I, Output=(I::Buffer, F::Output), Error=F::Error>
  where F: Parser<I> {
    move |i: I| {
        let m = i.mark();

        match f.parse(i) {
            (mut b, Ok(t)) => {
                let n = b.consume_from(m);

                (b, Ok((n, t)))
            },
            (b, Err(e))   => (b, Err(e)),
        }
    }
}

/// Applies the parser `F` without consuming any input.
///
/// ```
/// use chomp::prelude::{Parser, parse_only, take};
/// use chomp::combinators::look_ahead;
///
/// let p = look_ahead(take(4)).bind(|t| take(7).map(move |u| (t, u)));
///
/// assert_eq!(parse_only(p, b"testing"), Ok((&b"test"[..], &b"testing"[..])));
/// ```
#[inline]
pub fn look_ahead<I: Input, F>(f: F) -> impl Parser<I, Output=F::Output, Error=F::Error>
  where F: Parser<I> {
    move |i: I| {
        let m = i.mark();

        match f.parse(i) {
            (b, Ok(t))  => (b.restore(m), Ok(t)),
            (b, Err(t)) => (b.restore(m), Err(t)),
        }
    }
}

#[cfg(test)]
mod test {
    use types::{Parser, err};
    use super::*;

    use parsers::{Error, any, take, token, string};

    #[test]
    fn option_test() {
        assert_eq!(option(any(), b'-').parse(&b""[..]), (&b""[..], Ok(b'-')));
        assert_eq!(option(any(), b'-').parse(&b"a"[..]), (&b""[..], Ok(b'a')));
        assert_eq!(option(take(2), &b""[..]).parse(&b""[..]),   (&b""[..], Ok(&b""[..])));
        assert_eq!(option(take(2), &b""[..]).parse(&b"a"[..]),  (&b"a"[..], Ok(&b""[..])));
        assert_eq!(option(take(2), &b""[..]).parse(&b"ab"[..]), (&b""[..], Ok(&b"ab"[..])));

        assert_eq!(option(token(b' ').map_err(|_| "token_err"), b'-').parse(&b"a"[..]), (&b"a"[..], Ok(b'-')));
    }

    #[test]
    fn many_test() {
        let r: (_, Result<Vec<u8>, _>) = many(|| err("the error")).parse(&b""[..]); assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<u8>, _>) = many(|| err("the error")).parse(&b"abc"[..]); assert_eq!(r, (&b"abc"[..], Ok(vec![])));

        let r: (_, Result<Vec<_>, _>) = many(|| token(b'a')).parse(&b""[..]); assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many(|| token(b'a')).parse(&b"a"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(|| token(b'a')).parse(&b"aa"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a'])));

        let r: (_, Result<Vec<_>, _>) = many(|| token(b'a')).parse(&b"bbb"[..]); assert_eq!(r, (&b"bbb"[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many(|| token(b'a')).parse(&b"abb"[..]); assert_eq!(r, (&b"bb"[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(|| token(b'a')).parse(&b"aab"[..]); assert_eq!(r, (&b"b"[..], Ok(vec![b'a', b'a'])));
    }

    #[test]
    fn many1_test() {
        let r: (_, Result<Vec<u8>, _>) = many1(|| err("the error")).parse(&b""[..]); assert_eq!(r, (&b""[..], Err("the error")));
        let r: (_, Result<Vec<u8>, _>) = many1(|| err("the error")).parse(&b"abc"[..]); assert_eq!(r, (&b"abc"[..], Err("the error")));

        let r: (_, Result<Vec<_>, _>) = many1(|| token(b'a')).parse(&b""[..]); assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many1(|| token(b'a')).parse(&b"a"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = many1(|| token(b'a')).parse(&b"aa"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a'])));

        let r: (_, Result<Vec<_>, _>) = many1(|| token(b'a')).parse(&b"bbb"[..]); assert_eq!(r, (&b"bbb"[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many1(|| token(b'a')).parse(&b"abb"[..]); assert_eq!(r, (&b"bb"[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = many1(|| token(b'a')).parse(&b"aab"[..]); assert_eq!(r, (&b"b"[..], Ok(vec![b'a', b'a'])));
    }

    #[test]
    fn count_test() {
        let r: (_, Result<Vec<u8>, _>) = count(3, || err("the error")).parse(&b""[..]); assert_eq!(r, (&b""[..], Err("the error")));

        let r: (_, Result<Vec<_>, _>) = count(3, || token(b'a')).parse(&b""[..]); assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = count(3, || token(b'a')).parse(&b"a"[..]); assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = count(3, || token(b'a')).parse(&b"aa"[..]); assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = count(3, || token(b'a')).parse(&b"aaa"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = count(3, || token(b'a')).parse(&b"aaaa"[..]); assert_eq!(r, (&b"a"[..], Ok(vec![b'a', b'a', b'a'])));
    }

    #[test]
    fn skip_many1_test() {
        assert_eq!(skip_many1(|| err::<(), _>("error")).parse(&b"bc"[..]), (&b"bc"[..], Err("error")));

        assert_eq!(skip_many1(|| token(b'a')).parse(&b"aabc"[..]), (&b"bc"[..], Ok(())));
        assert_eq!(skip_many1(|| token(b'a')).parse(&b"abc"[..]),  (&b"bc"[..], Ok(())));
        assert_eq!(skip_many1(|| token(b'a')).parse(&b"bc"[..]),   (&b"bc"[..], Err(Error::expected(b'a'))));
        assert_eq!(skip_many1(|| token(b'a')).parse(&b""[..]),     (&b""[..], Err(Error::expected(b'a'))));
        assert_eq!(skip_many1(|| token(b'a')).parse(&b"aaa"[..]),  (&b""[..], Ok(())));
    }

    #[test]
    fn many_till_test() {
        assert_eq!(many_till(any, || token(b'c')).parse(&b"abcd"[..]), (&b"d"[..], Ok(vec![b'a', b'b'])));
        let r: (_, Result<Vec<_>, _>) = many_till(any, || token(b'c')).parse(&b"abd"[..]); assert_eq!(r, (&b""[..], Err(Error::unexpected())));

        let r: (_, Result<Vec<u8>, _>) = many_till(|| err(Error::expected(b'@')), || token(b'c')).parse(&b"abcd"[..]); assert_eq!(r, (&b"abcd"[..], Err(Error::expected(b'@'))));

        // Variant to make sure error slice is propagated
        let mut n = 0;
        let r: (_, Result<Vec<_>, _>) = many_till(|| if n == 0 {
            n += 1;
            any().map_err(|_| Error::expected(b'i')).boxed()
        } else {
             err(Error::expected(b'@')).boxed()
        }, || token(b'c')).parse(&b"abcd"[..]);
        assert_eq!(r, (&b"bcd"[..], Err(Error::expected(b'@'))));
    }

    #[test]
    fn matched_by_test() {
        assert_eq!(matched_by(any()).parse(&b"abc"[..]), (&b"bc"[..], Ok((&b"a"[..], b'a'))));
        assert_eq!(matched_by(err::<(), _>("my error")).parse(&b"abc"[..], ), (&b"abc"[..], Err("my error")));
        assert_eq!(matched_by(any().map_err(|_| "any error").then(err::<(), _>("my error"))).parse(&b"abc"[..]), (&b"bc"[..], Err("my error")));
        assert_eq!(matched_by(any()).parse(&b""[..]), (&b""[..], Err(Error::unexpected())));
    }

    #[test]
    fn sep_by_test() {
        assert_eq!(sep_by(any, || token(b';')).parse(&b""[..]), (&b""[..],   Ok(vec![])));
        assert_eq!(sep_by(any, || token(b';')).parse(&b"a"[..]), (&b""[..],   Ok(vec![b'a'])));
        assert_eq!(sep_by(any, || token(b';')).parse(&b"a;c"[..]), (&b""[..],   Ok(vec![b'a', b'c'])));
        assert_eq!(sep_by(any, || token(b';')).parse(&b"a;c;"[..]), (&b";"[..],  Ok(vec![b'a', b'c'])));
        assert_eq!(sep_by(any, || token(b';')).parse(&b"abc"[..]), (&b"bc"[..], Ok(vec![b'a'])));
        assert_eq!(sep_by(any, || token(b';')).parse(&b"a;bc"[..]), (&b"c"[..],  Ok(vec![b'a', b'b'])));
        assert_eq!(sep_by(any, || token(b';')).parse(&b"abc"[..]), (&b"bc"[..], Ok(vec![b'a'])));
        assert_eq!(sep_by(any, || token(b';')).parse(&b"a;bc"[..]), (&b"c"[..],  Ok(vec![b'a', b'b'])));

        assert_eq!(sep_by(|| token(b'a'), || token(b';')).parse(&b"b"[..]), (&b"b"[..], Ok(vec![])));
        assert_eq!(sep_by(any, || string(b"--")).parse(&b"a--c-"[..]), (&b"-"[..], Ok(vec![b'a', b'c'])));

        // Incomplete becasue there might be another separator or item to be read
        let r: (_, Result<Vec<_>, _>) = sep_by(any, || token(b';')).parse(&b""[..]); assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = sep_by(any, || token(b';')).parse(&b"a"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = sep_by(any, || token(b';')).parse(&b"a;"[..]); assert_eq!(r, (&b";"[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = sep_by(any, || token(b';')).parse(&b"a;c"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a', b'c'])));
        let r: (_, Result<Vec<_>, _>) = sep_by(any, || token(b';')).parse(&b"a;c;"[..]); assert_eq!(r, (&b";"[..], Ok(vec![b'a', b'c'])));
        let r: (_, Result<Vec<_>, _>) = sep_by(any, || string(b"--")).parse(&b"a--c-"[..]);  assert_eq!(r, (&b"-"[..], Ok(vec![b'a', b'c'])));
        let r: (_, Result<Vec<_>, _>) = sep_by(|| string(b"aaa"), || string(b"--")).parse(&b"aaa--a"[..]); assert_eq!(r, (&b"--a"[..], Ok(vec![&b"aaa"[..]])));
    }

    #[test]
    fn sep_by1_test() {
        let r: (_, Result<Vec<_>, _>)  = sep_by1(any,               || token(b';')).parse(&b""[..]); assert_eq!(r, (&b""[..], Err(Error::unexpected())));
        let r: (_, Result<Vec<()>, _>) = sep_by1(|| err("my err"),  || token(b';').map_err(|_| "token_err")).parse(&b"b"[..]); assert_eq!(r, (&b"b"[..], Err("my err")));
        let r: (_, Result<Vec<_>, _>)  = sep_by1(any,               || token(b';')).parse(&b""[..]); assert_eq!(r, (&b""[..], Err(Error::unexpected())));
        let r: (_, Result<Vec<_>, _>)  = sep_by1(|| token(b'a'), || token(b';')).parse(&b"b"[..]); assert_eq!(r, (&b"b"[..], Err(Error::expected(b'a'))));

        assert_eq!(sep_by1(any, || token(b';')).parse(&b"a"[..]),       (&b""[..],   Ok(vec![b'a'])));
        assert_eq!(sep_by1(any, || token(b';')).parse(&b"a;c"[..]),     (&b""[..],   Ok(vec![b'a', b'c'])));
        assert_eq!(sep_by1(any, || token(b';')).parse(&b"a;c;"[..]),    (&b";"[..],  Ok(vec![b'a', b'c'])));
        assert_eq!(sep_by1(any, || string(b"--")).parse(&b"a--c-"[..]), (&b"-"[..],  Ok(vec![b'a', b'c'])));
        assert_eq!(sep_by1(any, || token(b';')).parse(&b"abc"[..]),     (&b"bc"[..], Ok(vec![b'a'])));
        assert_eq!(sep_by1(any, || token(b';')).parse(&b"a;bc"[..]),    (&b"c"[..],  Ok(vec![b'a', b'b'])));

        assert_eq!(sep_by1(any, || token(b';')).parse(&b"abc"[..]), (&b"bc"[..], Ok(vec![b'a'])));
        assert_eq!(sep_by1(any, || token(b';')).parse(&b"a;bc"[..]), (&b"c"[..],  Ok(vec![b'a', b'b'])));

        // Incomplete becasue there might be another separator or item to be read
        let r: (_, Result<Vec<_>, _>) = sep_by1(any, || token(b';')).parse(&b""[..]); assert_eq!(r, (&b""[..], Err(Error::unexpected())));
        let r: (_, Result<Vec<_>, _>) = sep_by1(any, || token(b';')).parse(&b"a"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = sep_by1(any, || token(b';')).parse(&b"a;"[..]); assert_eq!(r, (&b";"[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = sep_by1(any, || token(b';')).parse(&b"a;c"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a', b'c'])));
        let r: (_, Result<Vec<_>, _>) = sep_by1(any, || token(b';')).parse(&b"a;c;"[..]); assert_eq!(r, (&b";"[..], Ok(vec![b'a', b'c'])));
        let r: (_, Result<Vec<_>, _>) = sep_by1(any, || string(b"--")).parse(&b"a--c-"[..]); assert_eq!(r, (&b"-"[..], Ok(vec![b'a', b'c'])));
        let r: (_, Result<Vec<_>, _>) = sep_by1(|| string(b"aaa"), || string(b"--")).parse(&b"aaa--a"[..]); assert_eq!(r, (&b"--a"[..], Ok(vec![&b"aaa"[..]])));
    }

    #[test]
    fn look_ahead_test() {
        assert_eq!(look_ahead(any()).parse(&b"abc"[..]), (&b"abc"[..], Ok(b'a')));
        assert_eq!(look_ahead(string(b"abc")).parse(&b"a"[..]), (&b"a"[..], Err(Error::expected(b'b'))));
        assert_eq!(look_ahead(token(b'a').then(token(b'b')).map_err(|_| "err")).parse(&b"aa"[..]), (&b"aa"[..], Err("err")));
    }
}
