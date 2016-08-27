use types::{Input, Parser};

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
#[inline]
pub fn parse_only<'a, I, F>(parser: F, input: &'a [I]) -> Result<F::Output, (&'a [I], F::Error)>
  where I: Copy + PartialEq,
        F: Parser<&'a [I]> {
    match parser.parse(input) {
        (_,     Ok(t))  => Ok(t),
        (mut b, Err(e)) => Err((b.consume_remaining(), e)),
    }
}

/// Runs the given parser on the supplied string.
pub fn parse_only_str<'a, F>(parser: F, input: &'a str) -> Result<F::Output, (&'a str, F::Error)>
  where F: Parser<&'a str> {
    match parser.parse(input) {
        (_,     Ok(t))  => Ok(t),
        (mut b, Err(e)) => Err((b.consume_remaining(), e)),
    }
}

#[cfg(test)]
mod test {
    use types::Input;
    use super::*;

    #[test]
    fn inspect_input() {
        assert_eq!(parse_only(|i| {
            assert_eq!(i, b"the input");

            (i, Ok::<&'static str, ()>("the result"))
        }, b"the input"), Ok("the result"));
    }

    #[test]
    fn err() {
        assert_eq!(parse_only(|mut i| {
            Input::consume(&mut i, 4);

            (i, Err::<(), &'static str>("my error"))
        }, b"the input"), Err((&b"input"[..], "my error")));
    }

    #[test]
    fn inspect_input_str() {
        assert_eq!(parse_only_str(|i| {
            assert_eq!(i, "the input");

            (i, Ok::<_, ()>("the result"))
        }, "the input"), Ok("the result"));
    }

    #[test]
    fn err_str() {
        assert_eq!(parse_only_str(|mut i| {
            Input::consume(&mut i, 4);

            (i, Err::<(), _>("my error"))
        }, "the input"), Err(("input", "my error")));
    }
}
