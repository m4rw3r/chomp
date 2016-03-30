use types::ParseResult;
use primitives::{
    IntoInner,
    Primitives,
};

/// Runs the given parser on the supplied finite input.
///
/// ```
/// use chomp::prelude::{parse_only, Error};
/// use chomp::ascii::decimal;
///
/// assert_eq!(parse_only(decimal, b"123foobar"), Ok(123u32));
///
/// // Annotation because `decimal` is generic over number types
/// let r: Result<u32, _> = parse_only(decimal, b"foobar");
/// assert_eq!(r, Err((&b"foobar"[..], Error::new())));
/// ```
///
/// This will not force the parser to consume all available input, any remainder will be
/// discarded. To force a parser to consume all its input, use `eof` at the end like this:
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::prelude::{U8Input, Input, Error, SimpleResult, parse_only, string, eof};
///
/// fn my_parser<I: U8Input>(i: I) -> SimpleResult<I, I::Buffer> {
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
///            Err((&b" and more"[..], Error::new())));
/// # }
/// ```
pub fn parse_only<'a, I, T, E, F>(parser: F, input: &'a [I]) -> Result<T, (&'a [I], E)>
  where I: Copy + PartialEq,
        F: FnOnce(&'a [I]) -> ParseResult<&'a [I], T, E> {
    match parser(input).into_inner() {
        (_, Ok(t))      => Ok(t),
        (mut b, Err(e)) => Err((b.consume_remaining(), e)),
    }
}

#[cfg(test)]
mod test {
    use types::Input;
    use primitives::Primitives;
    use super::{
        parse_only,
    };

    #[test]
    fn inspect_input() {
        let mut input = None;

        assert_eq!(parse_only(|i| {
            input = Some(i.iter().cloned().collect());

            i.ret::<_, ()>("the result")
        }, b"the input"), Ok("the result"));

        assert_eq!(input, Some(b"the input".to_vec()));
    }

    #[test]
    fn err() {
        assert_eq!(parse_only(|mut i| {
            i.consume(4);

            i.err::<(), _>("my error")
        }, b"the input"), Err((&b"input"[..], "my error")));
    }

    // FIXME:
    /*
    #[test]
    fn incomplete() {
        assert_eq!(parse_only(|i| i.incomplete::<(), ()>(23), b"the input"), Err(ParseError::Incomplete(23)));
    }
    */
}
