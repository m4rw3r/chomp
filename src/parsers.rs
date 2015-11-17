//! Basic parsers.

use ::{Input, SimpleResult};
use ::err;
use ::internal::InputModify;
use ::internal::{data, error, incomplete};

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
pub fn any<'a, I: 'a + Copy>(i: Input<'a, I>) -> SimpleResult<'a, I, I> {
    i.parse(|b| match b.first() {
        None     => incomplete(1),
        Some(&c) => data(&b[1..], c),
    })
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
pub fn satisfy<'a, I: 'a + Copy, F>(i: Input<'a, I>, f: F) -> SimpleResult<'a, I, I>
  where F: FnOnce(I) -> bool {
    i.parse(|b| match b.first() {
        None             => incomplete(1),
        Some(&c) if f(c) => data(&b[1..], c),
        Some(_)          => error(b, err::unexpected()),
    })
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
pub fn token<'a, I: 'a + Copy + PartialEq>(i: Input<'a, I>, t: I) -> SimpleResult<'a, I, I> {
    i.parse(|b| match b.first() {
        None               => incomplete(1),
        Some(&c) if t == c => data(&b[1..], c),
        Some(_)            => error(b, err::expected(t)),
    })
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
pub fn not_token<'a, I: 'a + Copy + PartialEq>(i: Input<'a, I>, t: I) -> SimpleResult<'a, I, I> {
    i.parse(|b| match b.first() {
        None               => incomplete(1),
        Some(&c) if t != c => data(&b[1..], c),
        Some(_)            => error(b, err::unexpected()),
    })
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
pub fn peek<'a, I: 'a + Copy>(i: Input<'a, I>) -> SimpleResult<'a, I, Option<I>> {
    i.parse(|b| data(b, b.first().map(|&c| c)))
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
pub fn take<'a, I: 'a + Copy>(i: Input<'a, I>, num: usize) -> SimpleResult<'a, I, &'a [I]> {
    i.parse(|b| if num <= b.len() {
        data(&b[num..], &b[..num])
    } else {
        incomplete(num)
    })
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
pub fn take_while<'a, I: 'a + Copy, F>(i: Input<'a, I>, f: F) -> SimpleResult<'a, I, &'a [I]>
  where F: Fn(I) -> bool {
    i.parse(|b| match b.iter().map(|c| *c).position(|c| f(c) == false) {
        Some(n) => data(&b[n..], &b[..n]),
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => incomplete(1),
    })
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
pub fn take_while1<'a, I: 'a + Copy, F>(i: Input<'a, I>, f: F) -> SimpleResult<'a, I, &'a [I]>
  where F: Fn(I) -> bool {
    i.parse(|b| match b.iter().map(|c| *c).position(|c| f(c) == false) {
        Some(0) => error(b, err::unexpected()),
        Some(n) => data(&b[n..], &b[..n]),
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => incomplete(1),
    })
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
pub fn take_till<'a, I: 'a + Copy, F>(i: Input<'a, I>, f: F) -> SimpleResult<'a, I, &'a [I]>
  where F: Fn(I) -> bool {
    i.parse(|b| match b.iter().map(|c| *c).position(f) {
        Some(n) => data(&b[n..], &b[0..n]),
        // TODO: Should this following 1 be something else, seeing as take_while1 is potentially
        // infinite?
        None    => incomplete(1),
    })
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
pub fn take_remainder<'a, I: Copy>(i: Input<'a, I>) -> SimpleResult<'a, I, &'a [I]> {
    i.parse(|b| data(&b[b.len() -1 ..], b))
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
    i.parse(|b| {
        if s.len() > b.len() {
            return incomplete(s.len() - b.len());
        }

        let d = &b[..s.len()];

        for i in 0..s.len() {
            if s[i] != d[i] {
                return err::string(b, i, s);
            }
        }

        data(&b[s.len()..], d)
    })
}

#[cfg(test)]
mod test {
    use super::{take_while1, token, take_remainder};
    use ::{Input, SimpleResult};

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
}
