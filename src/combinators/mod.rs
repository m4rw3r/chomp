//! Basic combinators.

#[macro_use]
mod macros;

pub mod bounded;

use std::iter::FromIterator;

use types::{Input, Parser};

/// Applies the parser `p` exactly `num` times collecting all items into `T: FromIterator`.
///
/// ```
/// use chomp::prelude::*;
///
/// fn parse<I: U8Input>(i: I) -> SimpleResult<I, Vec<u8>> {
///     count(i, 2, |i| token(i, b'a'))
/// }
///
/// assert_eq!(parse_only(parse, b"a  "), Err((&b"  "[..], Error::expected(b'a'))));
/// assert_eq!(parse_only(parse, b"aa "), Ok(vec![b'a', b'a']));
///
/// let with_remainder = |i| parse(i).bind(|i, d| take_remainder(i).map(|r| (r, d)));
///
/// assert_eq!(parse_only(with_remainder, b"aaa"), Ok((&b"a"[..], vec![b'a', b'a'])));
/// ```
#[inline]
pub fn count<I: Input, P, T, F>(num: usize, p: F) -> impl Parser<I, Output=T, Error=P::Error>
  where F: FnMut() -> P,
        P: Parser<I>,
        T: FromIterator<P::Output> {
    bounded::many_exact(num, p)
}

/// Tries the parser `f`, on success it yields the parsed value, on failure `default` will be
/// yielded instead.
///
/// Incomplete state is propagated. Backtracks on error.
///
/// ```
/// use chomp::prelude::{U8Input, SimpleResult, parse_only, option, token};
///
/// fn f<I: U8Input>(i: I) -> SimpleResult<I, u8> {
///     option(i, |i| token(i, b'a'), b'd')
/// }
///
/// assert_eq!(parse_only(f, b"abc"), Ok(b'a'));
/// assert_eq!(parse_only(f, b"bbc"), Ok(b'd'));
/// ```
#[inline]
pub fn option<I: Input, P>(p: P, default: P::Output) -> impl Parser<I, Output=P::Output, Error=P::Error>
  where P: Parser<I> {
    move |mut i: I| {
        let m = i.mark();

        match p.parse(i) {
            (b, Ok(d))  => (b, Ok(d)),
            (b, Err(_)) => (b.restore(m), Ok(default)),
        }
    }
}

/// Tries to match the parser `f`, if `f` fails it tries `g`. Returns the success value of
/// the first match, otherwise the error of the last one if both fail.
///
/// Incomplete state is propagated from the first one to report incomplete.
///
/// If multiple `or` combinators are used in the same expression, consider using the `parse!` macro
/// and its alternation operator (`<|>`).
///
/// ```
/// use chomp::prelude::{Error, parse_only, or, token};
///
/// let p = |i| or(i,
///             |i| token(i, b'a'),
///             |i| token(i, b'b'));
///
/// assert_eq!(parse_only(&p, b"abc"), Ok(b'a'));
/// assert_eq!(parse_only(&p, b"bbc"), Ok(b'b'));
/// assert_eq!(parse_only(&p, b"cbc"), Err((&b"cbc"[..], Error::expected(b'b'))));
/// ```
#[inline]
pub fn or<I: Input, F, G>(f: F, g: G) -> impl Parser<I, Output=F::Output, Error=F::Error>
  where F: Parser<I>,
        G: Parser<I, Output=F::Output, Error=F::Error> {
    move |mut i: I| {
        let m = i.mark();

        match f.parse(i) {
            (b, Ok(d))  => (b, Ok(d)),
            (b, Err(_)) => g.parse(b.restore(m)),
        }
    }
}

/// Parses many instances of `f` until it does no longer match, collecting all matches into the
/// type `T: FromIterator`.
///
/// Note: Allocates data.
///
/// ```
/// use chomp::prelude::{parse_only, token, many, take_while1};
///
/// let r: Result<Vec<_>, _> = parse_only(|i| many(i,
///     |i| take_while1(i, |c| c != b',' && c != b' ')
///         .bind(|i, c| token(i, b',')
///                      .map(|_| c))),
///     b"a,bc,cd ");
///
/// assert_eq!(r, Ok(vec![&b"a"[..], &b"bc"[..]]));
/// ```
#[inline]
pub fn many<I: Input, T, F, P>(f: F) -> impl Parser<I, Output=T, Error=P::Error>
  where F: FnMut() -> P,
        P: Parser<I>,
        T: FromIterator<P::Output> {
    bounded::many_unbounded(f)
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
/// use chomp::prelude::{Error, parse_only, token, many1, take_while1};
///
/// let p = |i| many1(i, |i| take_while1(i, |c| c != b',' && c != b' ')
///             .bind(|i, c| token(i, b',')
///                          .map(|_| c)));
///
/// assert_eq!(parse_only(&p, b"a "), Err((&b" "[..], Error::expected(b','))));
/// assert_eq!(parse_only(&p, b"a, "), Ok(vec![&b"a"[..]]));
/// ```
#[inline]
pub fn many1<I: Input, F, T, P>(f: F) -> impl Parser<I, Output=T, Error=P::Error>
  where F: FnMut() -> P,
        P: Parser<I>,
        T: FromIterator<P::Output> {
    bounded::many_from(1, f)
}

// FIXME
/*
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
/// let r: Result<Vec<u8>, _> = parse_only(|i| sep_by(i, decimal, |i| token(i, b';')), b"91;03;20");
///
/// assert_eq!(r, Ok(vec![91, 03, 20]));
/// ```
#[inline]
pub fn sep_by<I: Input, T, R, F>(p: R, sep: F) -> impl Parser<I, Output=T, Error=R::Error>
  where T: FromIterator<R::Output>,
        //E: From<N>,
        R: Parser<I>,
        F: Parser<I, Error=R::Error> {
    bounded::sep_by_unbounded(p, sep)
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
/// let r: Result<Vec<u8>, _> = parse_only(|i| sep_by1(i, decimal, |i| token(i, b';')), b"91;03;20");
///
/// assert_eq!(r, Ok(vec![91, 03, 20]));
/// ```
#[inline]
pub fn sep_by1<I: Input, T, R, F>(p: R, sep: F) -> impl Parser<I, Output=T, Error=R::Error>
  where T: FromIterator<R::Output>,
        //E: From<N>,
        R: Parser<I>,
        F: Parser<I, Error=R::Error> {
    bounded::sep_by_from(1, p, sep)
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
/// let r: Result<Vec<u8>, _> = parse_only(|i| many_till(i, any, |i| token(i, b';')), b"abc;def");
///
/// assert_eq!(r, Ok(vec![b'a', b'b', b'c']));
/// ```
#[inline]
pub fn many_till<I: Input, T, R, F>(p: R, end: F) -> impl Parser<I, Output=T, Error=R::Error>
  where T: FromIterator<R::Output>,
        //E: From<N>,
        R: Parser<I>,
        F: Parser<I, Error=R::Error> {
    bounded::many_till_unbounded(p, end)
}

/// Runs the given parser until it fails, discarding matched input.
///
/// Incomplete state will be propagated.
///
/// This is more efficient compared to using `many` and then just discarding the result as
/// `many` allocates a separate data structure to contain the data before proceeding.
///
/// ```
/// use chomp::prelude::{parse_only, skip_many, token};
///
/// let r = parse_only(|i| skip_many(i, |i| token(i, b'a')).then(|i| token(i, b'b')), b"aaaabc");
///
/// assert_eq!(r, Ok(b'b'));
/// ```
#[inline]
pub fn skip_many<I: Input, F>(f: F) -> impl Parser<I, Output=(), Error=F::Error>
  where F: Parser<I> {
    bounded::skip_many_unbounded(f)
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
/// use chomp::prelude::{Error, parse_only, skip_many1, token};
///
/// let p = |i| skip_many1(i, |i| token(i, b'a')).bind(|i, _| token(i, b'b'));
///
/// assert_eq!(parse_only(&p, b"aaaabc"), Ok(b'b'));
/// assert_eq!(parse_only(&p, b"abc"), Ok(b'b'));
///
/// assert_eq!(parse_only(&p, b"bc"), Err((&b"bc"[..], Error::expected(b'a'))));
/// ```
#[inline]
pub fn skip_many1<I: Input, F>(f: F) -> impl Parser<I, Output=(), Error=F::Error>
  where F: Parser<I> {
    bounded::skip_many_from(1, f)
}
*/

/// Returns the result of the given parser as well as the slice which matched it.
///
/// ```
/// use chomp::prelude::{parse_only, matched_by};
/// use chomp::ascii::decimal;
///
/// assert_eq!(parse_only(|i| matched_by(i, decimal), b"123"), Ok((&b"123"[..], 123u32)));
/// ```
#[inline]
pub fn matched_by<I: Input, F>(f: F) -> impl Parser<I, Output=(I::Buffer, F::Output), Error=F::Error>
  where F: Parser<I> {
    move |mut i: I| {
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
/// use chomp::prelude::{parse_only, take};
/// use chomp::combinators::look_ahead;
///
/// let p = |i| look_ahead(i, |i| take(i, 4)).bind(|i, t| take(i, 7).map(|u| (t, u)));
///
/// assert_eq!(parse_only(p, b"testing"), Ok((&b"test"[..], &b"testing"[..])));
/// ```
#[inline]
pub fn look_ahead<I: Input, F>(f: F) -> impl Parser<I, Output=F::Output, Error=F::Error>
  where F: Parser<I> {
    move |mut i: I| {
        let m = i.mark();

        match f.parse(i) {
            (b, Ok(t))  => (b.restore(m), Ok(t)),
            (b, Err(t)) => (b.restore(m), Err(t)),
        }
    }
}

// FIXME: Update
/*
#[cfg(test)]
mod test {
    use types::{Input, ParseResult};
    use primitives::IntoInner;
    use super::*;

    use parsers::{Error, any, take, token, string};

    #[test]
    fn option_test() {
        assert_eq!(option(&b""[..],   any, b'-').into_inner(), (&b""[..], Ok(b'-')));
        assert_eq!(option(&b"a"[..],  any, b'-').into_inner(), (&b""[..], Ok(b'a')));
        assert_eq!(option(&b""[..],   |i| take(i, 2).map(ToOwned::to_owned), vec![]).into_inner(), (&b""[..], Ok(vec![])));
        assert_eq!(option(&b"a"[..],  |i| take(i, 2).map(ToOwned::to_owned), vec![]).into_inner(), (&b"a"[..], Ok(vec![])));
        assert_eq!(option(&b"ab"[..], |i| take(i, 2).map(ToOwned::to_owned), vec![]).into_inner(), (&b""[..], Ok(vec![b'a', b'b'])));

        assert_eq!(option(&b"a"[..], |i| token(i, b' ').map_err(|_| "token_err"), b'-').into_inner(), (&b"a"[..], Ok(b'-')));
    }

    #[test]
    fn or_test() {
        assert_eq!(or(&b""[..],  any, any).into_inner(), (&b""[..], Err(Error::unexpected())));
        assert_eq!(or(&b"a"[..], any, any).into_inner(), (&b""[..], Ok(b'a')));
        assert_eq!(or(&b"a"[..],  |i| take(i, 2), |i| take(i, 1)).into_inner(), (&b""[..], Ok(&b"a"[..])));
        assert_eq!(or(&b"ab"[..], |i| take(i, 2), |i| take(i, 1)).into_inner(), (&b""[..], Ok(&b"ab"[..])));
        assert_eq!(or(&b"a"[..],  |i| token(i, b'a'), |i| token(i, b'b')).into_inner(), (&b""[..], Ok(b'a')));
        assert_eq!(or(&b"b"[..],  |i| token(i, b'a'), |i| token(i, b'b')).into_inner(), (&b""[..], Ok(b'b')));
        assert_eq!(or(&b"c"[..],  |i| token(i, b'a').map_err(|_| "a err"), |i| token(i, b'b').map_err(|_| "b err")).into_inner(), (&b"c"[..], Err("b err")));
    }

    #[test]
    fn many_test() {
        let r: (_, Result<Vec<u8>, _>) = many(&b""[..], |i| i.err("the error")).into_inner();
        assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<u8>, _>) = many(&b"abc"[..], |i| i.err("the error")).into_inner();
        assert_eq!(r, (&b"abc"[..], Ok(vec![])));

        let r: (_, Result<Vec<_>, _>) = many(&b""[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many(&b"a"[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b""[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(&b"aa"[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a'])));

        let r: (_, Result<Vec<_>, _>) = many(&b"bbb"[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b"bbb"[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many(&b"abb"[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b"bb"[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(&b"aab"[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b"b"[..], Ok(vec![b'a', b'a'])));
    }

    #[test]
    fn many1_test() {
        let r: (_, Result<Vec<u8>, _>) = many1(&b""[..], |i| i.err("the error")).into_inner();
        assert_eq!(r, (&b""[..], Err("the error")));
        let r: (_, Result<Vec<u8>, _>) = many1(&b"abc"[..], |i| i.err("the error")).into_inner();
        assert_eq!(r, (&b"abc"[..], Err("the error")));

        let r: (_, Result<Vec<_>, _>) = many1(&b""[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many1(&b"a"[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b""[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = many1(&b"aa"[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a'])));

        let r: (_, Result<Vec<_>, _>) = many1(&b"bbb"[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b"bbb"[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many1(&b"abb"[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b"bb"[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = many1(&b"aab"[..], |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b"b"[..], Ok(vec![b'a', b'a'])));
    }

    #[test]
    fn count_test() {
        let r: (_, Result<Vec<u8>, _>) = count(&b""[..], 3, |i| i.err("the error")).into_inner();
        assert_eq!(r, (&b""[..], Err("the error")));

        let r: (_, Result<Vec<_>, _>) = count(&b""[..], 3, |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = count(&b"a"[..], 3, |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = count(&b"aa"[..], 3, |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = count(&b"aaa"[..], 3, |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = count(&b"aaaa"[..], 3, |i| token(i, b'a')).into_inner();
        assert_eq!(r, (&b"a"[..], Ok(vec![b'a', b'a', b'a'])));
    }

    #[test]
    fn skip_many1_test() {
        assert_eq!(skip_many1(&b"bc"[..], |i| i.err::<(), _>("error")).into_inner(), (&b"bc"[..], Err("error")));

        assert_eq!(skip_many1(&b"aabc"[..], |i| token(i, b'a')).into_inner(), (&b"bc"[..], Ok(())));
        assert_eq!(skip_many1(&b"abc"[..],  |i| token(i, b'a')).into_inner(), (&b"bc"[..], Ok(())));
        assert_eq!(skip_many1(&b"bc"[..],   |i| token(i, b'a')).into_inner(), (&b"bc"[..], Err(Error::expected(b'a'))));
        assert_eq!(skip_many1(&b""[..],     |i| token(i, b'a')).into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        assert_eq!(skip_many1(&b"aaa"[..],  |i| token(i, b'a')).into_inner(), (&b""[..], Ok(())));
    }

    #[test]
    fn many_till_test() {
        assert_eq!(many_till(&b"abcd"[..], any, |i| token(i, b'c')).into_inner(), (&b"d"[..], Ok(vec![b'a', b'b'])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abd"[..], any, |i| token(i, b'c'));
        assert_eq!(r.into_inner(), (&b""[..], Err(Error::unexpected())));

        let r: ParseResult<_, Vec<u8>, _> = many_till(&b"abcd"[..], |i| i.err(Error::expected(b'@')), |i| token(i, b'c'));
        assert_eq!(r.into_inner(), (&b"abcd"[..], Err(Error::expected(b'@'))));

        // Variant to make sure error slice is propagated
        let mut n = 0;
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abcd"[..], |i| if n == 0 { n += 1; any(i).map_err(|_| Error::expected(b'i')) } else { i.err(Error::expected(b'@')) }, |i| token(i, b'c'));
        assert_eq!(r.into_inner(), (&b"bcd"[..], Err(Error::expected(b'@'))));
    }

    #[test]
    fn matched_by_test() {
        assert_eq!(matched_by(&b"abc"[..], any).into_inner(), (&b"bc"[..], Ok((&b"a"[..], b'a'))));
        assert_eq!(matched_by(&b"abc"[..], |i| i.err::<(), _>("my error")).into_inner(), (&b"abc"[..], Err("my error")));
        assert_eq!(matched_by(&b"abc"[..], |i| any(i).map_err(|_| "any error").then(|i| i.err::<(), _>("my error"))).into_inner(), (&b"bc"[..], Err("my error")));
        assert_eq!(matched_by(&b""[..], any).into_inner(), (&b""[..], Err(Error::unexpected())));
    }

    #[test]
    fn sep_by_test() {
        assert_eq!(sep_by(&b""[..],      any, |i| token(i, b';')).into_inner(), (&b""[..],   Ok(vec![])));
        assert_eq!(sep_by(&b"a"[..],     any, |i| token(i, b';')).into_inner(), (&b""[..],   Ok(vec![b'a'])));
        assert_eq!(sep_by(&b"a;c"[..],   any, |i| token(i, b';')).into_inner(), (&b""[..],   Ok(vec![b'a', b'c'])));
        assert_eq!(sep_by(&b"a;c;"[..],  any, |i| token(i, b';')).into_inner(), (&b";"[..],  Ok(vec![b'a', b'c'])));
        assert_eq!(sep_by(&b"abc"[..],   any, |i| token(i, b';')).into_inner(), (&b"bc"[..], Ok(vec![b'a'])));
        assert_eq!(sep_by(&b"a;bc"[..],  any, |i| token(i, b';')).into_inner(), (&b"c"[..],  Ok(vec![b'a', b'b'])));
        assert_eq!(sep_by(&b"abc"[..],   any, |i| token(i, b';')).into_inner(), (&b"bc"[..], Ok(vec![b'a'])));
        assert_eq!(sep_by(&b"a;bc"[..],  any, |i| token(i, b';')).into_inner(), (&b"c"[..],  Ok(vec![b'a', b'b'])));

        assert_eq!(sep_by(&b"b"[..], |i| token(i, b'a'), |i| token(i, b';')).into_inner(), (&b"b"[..], Ok(vec![])));
        assert_eq!(sep_by(&b"a--c-"[..], any, |i| string(i, b"--")).into_inner(), (&b"-"[..], Ok(vec![b'a', b'c'])));

        // Incomplete becasue there might be another separator or item to be read
        let r: ParseResult<_, Vec<_>, _> = sep_by(&b""[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));

        let r: ParseResult<_, Vec<_>, _> = sep_by(&b"a"[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a'])));

        let r: ParseResult<_, Vec<_>, _> = sep_by(&b"a;"[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b";"[..], Ok(vec![b'a'])));

        let r: ParseResult<_, Vec<_>, _> = sep_by(&b"a;c"[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a', b'c'])));

        let r: ParseResult<_, Vec<_>, _> = sep_by(&b"a;c;"[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b";"[..], Ok(vec![b'a', b'c'])));

        let r: ParseResult<_, Vec<_>, _> = sep_by(&b"a--c-"[..], any, |i| string(i, b"--"));
        assert_eq!(r.into_inner(), (&b"-"[..], Ok(vec![b'a', b'c'])));

        let r: ParseResult<_, Vec<_>, _> = sep_by(&b"aaa--a"[..], |i| string(i, b"aaa"), |i| string(i, b"--"));
        assert_eq!(r.into_inner(), (&b"--a"[..], Ok(vec![&b"aaa"[..]])));
    }

    #[test]
    fn sep_by1_test() {
        let r: ParseResult<_, Vec<_>, _> = sep_by1(&b""[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b""[..], Err(Error::unexpected())));

        let r: ParseResult<_, Vec<()>, _> = sep_by1(&b"b"[..], |i| i.err("my err"), |i| token(i, b';').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), (&b"b"[..], Err("my err")));

        let r: ParseResult<_, Vec<_>, _> = sep_by1(&b""[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b""[..], Err(Error::unexpected())));

        let r: ParseResult<_, Vec<_>, _> = sep_by1(&b"b"[..], |i| token(i, b'a'), |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));

        assert_eq!(sep_by1(&b"a"[..],     any, |i| token(i, b';')).into_inner(),   (&b""[..],   Ok(vec![b'a'])));
        assert_eq!(sep_by1(&b"a;c"[..],   any, |i| token(i, b';')).into_inner(),   (&b""[..],   Ok(vec![b'a', b'c'])));
        assert_eq!(sep_by1(&b"a;c;"[..],  any, |i| token(i, b';')).into_inner(),   (&b";"[..],  Ok(vec![b'a', b'c'])));
        assert_eq!(sep_by1(&b"a--c-"[..], any, |i| string(i, b"--")).into_inner(), (&b"-"[..],  Ok(vec![b'a', b'c'])));
        assert_eq!(sep_by1(&b"abc"[..],   any, |i| token(i, b';')).into_inner(),   (&b"bc"[..], Ok(vec![b'a'])));
        assert_eq!(sep_by1(&b"a;bc"[..],  any, |i| token(i, b';')).into_inner(),   (&b"c"[..],  Ok(vec![b'a', b'b'])));

        assert_eq!(sep_by1(&b"abc"[..],  any, |i| token(i, b';')).into_inner(), (&b"bc"[..], Ok(vec![b'a'])));
        assert_eq!(sep_by1(&b"a;bc"[..], any, |i| token(i, b';')).into_inner(), (&b"c"[..],  Ok(vec![b'a', b'b'])));

        // Incomplete becasue there might be another separator or item to be read
        let r: ParseResult<_, Vec<_>, _> = sep_by1(&b""[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b""[..], Err(Error::unexpected())));

        let r: ParseResult<_, Vec<_>, _> = sep_by1(&b"a"[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a'])));

        let r: ParseResult<_, Vec<_>, _> = sep_by1(&b"a;"[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b";"[..], Ok(vec![b'a'])));

        let r: ParseResult<_, Vec<_>, _> = sep_by1(&b"a;c"[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a', b'c'])));

        let r: ParseResult<_, Vec<_>, _> = sep_by1(&b"a;c;"[..], any, |i| token(i, b';'));
        assert_eq!(r.into_inner(), (&b";"[..], Ok(vec![b'a', b'c'])));

        let r: ParseResult<_, Vec<_>, _> = sep_by1(&b"a--c-"[..], any, |i| string(i, b"--"));
        assert_eq!(r.into_inner(), (&b"-"[..], Ok(vec![b'a', b'c'])));

        let r: ParseResult<_, Vec<_>, _> = sep_by1(&b"aaa--a"[..], |i| string(i, b"aaa"), |i| string(i, b"--"));
        assert_eq!(r.into_inner(), (&b"--a"[..], Ok(vec![&b"aaa"[..]])));
    }

    #[test]
    fn look_ahead_test() {
        assert_eq!(look_ahead(&b"abc"[..], any).into_inner(), (&b"abc"[..], Ok(b'a')));
        assert_eq!(look_ahead(&b"a"[..], |i| string(i, b"abc")).into_inner(), (&b"a"[..], Err(Error::expected(b'b'))));
        assert_eq!(look_ahead(&b"aa"[..], |i| token(i, b'a').then(|i| token(i, b'b')).map_err(|_| "err")).into_inner(), (&b"aa"[..], Err("err")));
    }
}
*/
