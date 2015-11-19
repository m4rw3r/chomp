//! Basic parsers.

use {Input, SimpleResult};
use err;
use internal::InputModify;

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
    match i.buffer().first() {
        None     => i.incomplete(1),
        Some(&c) => i.modify(|b| &b[1..]).ret(c),
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
pub fn satisfy<'a, I: 'a + Copy, F>(i: Input<'a, I>, f: F) -> SimpleResult<'a, I, I>
  where F: FnOnce(I) -> bool {
    match i.buffer().first() {
        None             => i.incomplete(1),
        Some(&c) if f(c) => i.modify(|b| &b[1..]).ret(c),
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
pub fn token<'a, I: 'a + Copy + PartialEq>(i: Input<'a, I>, t: I) -> SimpleResult<'a, I, I> {
    match i.buffer().first() {
        None               => i.incomplete(1),
        Some(&c) if t == c => i.modify(|b| &b[1..]).ret(c),
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
pub fn not_token<'a, I: 'a + Copy + PartialEq>(i: Input<'a, I>, t: I) -> SimpleResult<'a, I, I> {
    match i.buffer().first() {
        None               => i.incomplete(1),
        Some(&c) if t != c => i.modify(|b| &b[1..]).ret(c),
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
pub fn peek<'a, I: 'a + Copy>(i: Input<'a, I>) -> SimpleResult<'a, I, Option<I>> {
    let d = i.buffer().first().map(|&c| c);

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
pub fn take<'a, I: 'a + Copy>(i: Input<'a, I>, num: usize) -> SimpleResult<'a, I, &'a [I]> {
    let b = i.buffer();

    if num <= b.len() {
        i.replace(&b[num..]).ret(&b[..num])
    } else {
        i.incomplete(num)
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
pub fn take_while<'a, I: 'a + Copy, F>(i: Input<'a, I>, f: F) -> SimpleResult<'a, I, &'a [I]>
  where F: Fn(I) -> bool {
    let b = i.buffer();

    match b.iter().map(|c| *c).position(|c| f(c) == false) {
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
pub fn take_while1<'a, I: 'a + Copy, F>(i: Input<'a, I>, f: F) -> SimpleResult<'a, I, &'a [I]>
  where F: Fn(I) -> bool {
    let b = i.buffer();

    match b.iter().map(|c| *c).position(|c| f(c) == false) {
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
pub fn take_till<'a, I: 'a + Copy, F>(i: Input<'a, I>, f: F) -> SimpleResult<'a, I, &'a [I]>
  where F: Fn(I) -> bool {
    let b = i.buffer();

    match b.iter().map(|c| *c).position(f) {
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
pub fn take_remainder<'a, I: Copy>(i: Input<'a, I>) -> SimpleResult<'a, I, &'a [I]> {
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

#[cfg(test)]
mod test {
    use super::{take_while1, token, take_remainder};
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
}
