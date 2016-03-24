use types::ParseResult;
use primitives::{
    IntoInner,
    Primitives,
    State,
};

/// Simple error type returned from `parse_only`.
#[derive(Debug, Eq, PartialEq)]
pub enum ParseError<I, E> {
    /// A parse error occurred.
    Error(I, E),
    /// The parser attempted to read more data than available.
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
pub fn parse_only<'a, I, T, E, F>(parser: F, input: &'a [I]) -> Result<T, ParseError<&'a [I], E>>
  where I: Copy + PartialEq,
        F: FnOnce(&'a [I]) -> ParseResult<&'a [I], T, E> {
    match parser(input).into_inner() {
        State::Data(_, t)      => Ok(t),
        State::Error(mut b, e) => Err(ParseError::Error(b.consume_remaining(), e)),
    }
}

#[cfg(test)]
mod test {
    use Input;
    use primitives::Primitives;
    use super::{
        ParseError,
        parse_only,
    };

    /*
    #[test]
    fn inspect_input() {
        let mut state = None;
        let mut input = None;

        assert_eq!(parse_only(|i| {
            state = Some(i.is_end());
            input = Some(i.iter().cloned().collect());

            i.ret::<_, ()>("the result")
        }, b"the input"), Ok("the result"));

        assert_eq!(input, Some(b"the input".to_vec()));
        assert_eq!(state, Some(true));
    }
    */

    #[test]
    fn err() {
        assert_eq!(parse_only(|mut i| {
            i.consume(4);

            i.err::<(), _>("my error")
        }, b"the input"), Err(ParseError::Error(&b"input"[..], "my error")));
    }

    /*
    #[test]
    fn incomplete() {
        assert_eq!(parse_only(|i| i.incomplete::<(), ()>(23), b"the input"), Err(ParseError::Incomplete(23)));
    }
    */
}
