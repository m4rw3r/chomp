use {Input, ParseResult};
use primitives::{IntoInner, State};
use primitives::input;

/// Simple error type returned from `parse_only`.
#[derive(Debug, Eq, PartialEq)]
pub enum ParseError<'a, I, E>
  where I: 'a {
    Error(&'a [I], E),
    Incomplete(usize),
}

/// Runs the given parser on the supplied finite input.
///
/// ```
/// use chomp::{ParseError, Error};
/// use chomp::parse_only;
/// use chomp::ascii::decimal;
///
/// assert_eq!(parse_only(decimal, b"123foobar"), Ok(123u32));
///
/// // Annotation because `decimal` is generic over number types
/// let r: Result<u32, _> = parse_only(decimal, b"foobar");
/// assert_eq!(r, Err(ParseError::Error(&b"foobar"[..], Error::new())));
/// ```
///
/// This will not force the parser to consume all available input, any remainder will be
/// discarded. To force a parser to consume all its input, use `eof` at the end like this:
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::{Input, ParseError, Error, U8Result};
/// use chomp::{parse_only, string, eof};
///
/// fn my_parser(i: Input<u8>) -> U8Result<&[u8]> {
///     parse!{i;
///         let r = string(b"pattern");
///                 eof();
///
///         ret r
///     }
/// }
///
/// assert_eq!(parse_only(my_parser, b"pattern"), Ok(&b"pattern"[..]));
/// assert_eq!(parse_only(my_parser, b"pattern and more"),
///            Err(ParseError::Error(&b" and more"[..], Error::new())));
/// # }
/// ```
pub fn parse_only<'a, I, T, E, F>(parser: F, input: &'a [I]) -> Result<T, ParseError<'a, I, E>>
  where T: 'a,
        E: 'a,
        F: FnOnce(Input<'a, I>) -> ParseResult<'a, I, T, E> {
    match parser(input::new(input::END_OF_INPUT, input)).into_inner() {
        State::Data(_, t)    => Ok(t),
        State::Error(b, e)   => Err(ParseError::Error(b, e)),
        State::Incomplete(n) => Err(ParseError::Incomplete(n)),
    }
}

#[cfg(test)]
mod test {
    use primitives::InputBuffer;

    use super::{
        ParseError,
        parse_only,
    };

    #[test]
    fn inspect_input() {
        let mut state = None;
        let mut input = None;

        assert_eq!(parse_only(|i| {
            state = Some(i.is_last_slice());
            input = Some(i.buffer());

            i.ret::<_, ()>("the result")
        }, b"the input"), Ok("the result"));

        assert_eq!(input, Some(&b"the input"[..]));
        assert_eq!(state, Some(true));
    }

    #[test]
    fn err() {
        assert_eq!(parse_only(|i| {
            let buf = i.buffer();

            i.replace(&buf[4..]).err::<(), _>("my error")
        }, b"the input"), Err(ParseError::Error(&b"input"[..], "my error")));
    }

    #[test]
    fn incomplete() {
        assert_eq!(parse_only(|i| i.incomplete::<(), ()>(23), b"the input"), Err(ParseError::Incomplete(23)));
    }
}
