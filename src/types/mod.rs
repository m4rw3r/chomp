mod input;
mod parse_result;
#[cfg(feature = "tendril")]
pub mod tendril;

use primitives::Guard;

pub use types::parse_result::{
    ParseResult
};
pub use types::input::InputBuf;

pub trait U8Input: Input<Token=u8> {}

// TODO: More restrictions? Buffer=&[u8]?
impl<T> U8Input for T
  where T: Input<Token=u8> {}

// FIXME: Docs
// TODO: More methods?
pub trait Buffer: PartialEq<Self> {
    /// The token type of this buffer.
    type Token: Copy + PartialEq;

    /// Applies a function in order on all tokens present in the buffer carrying an accumulator
    /// value `B` between invocations. The buffer is consumed as part of the folding and the last
    /// value of the accumulator is returned.
    // Would be prefereable if there was a &self -> Iterator method, but that does not work for
    // owned or maybe owned since the lifetimes will be wrong for one or the other. Higher Ranked
    // Trait Bounds (HRTB) does not seem to work either since it is not possible to later
    // instantiate the type in a function signature with a concrete lifetime without running into
    // an "expected bound lifetime but found concrete lifetime" error. Instantiation for HRTBs seem
    // to only take place in the actual code, not when a type is used in eg. a where clause.
    fn fold<B, F>(self, B, F) -> B
      where F: FnMut(B, Self::Token) -> B;

    /// The number of tokens present in this buffer.
    fn len(&self) -> usize;

    /// Consumes self to create an owned vector of tokens.
    ///
    /// Will allocate if the implementation borrows storage or does not use an owned type
    /// compatible with `Vec` internally.
    fn to_vec(self) -> Vec<Self::Token>;

    /// Returns true if this buffer is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// FIXME: Update, do not refer to type or linear type
/// Linear type containing the parser state, this type is threaded though `bind` and is also the
/// initial type passed to a parser.
///
/// Coupled with the `ParseResult` type it forms the parser monad:
///
/// ```ignore
/// Fn*(Input<I>, ...) -> ParseResult<I, T, E>;
/// ```
///
/// where ``Fn*`` is the appropriate closure/function trait, `I` the input token type (usually
/// something like `u8`), `...` additional parameters to the parser, `T` the carried type and `E`
/// the potential error type.
pub trait Input: Sized {
    /// The token type of the input.
    // TODO: Maybe remove the copy bound at some point?
    type Token: Copy + PartialEq;

    /// A marker type which is used to backtrack using `_mark` and `_restore`.
    ///
    /// It should also be possible to use this type to consume the data from the marked position to
    /// the current position.
    type Marker;

    /// The buffer type yielded by this input when multiple tokens are consumed in sequence.
    ///
    /// Can eg. provide zero-copy parsing if the input type is built to support it.
    type Buffer: Buffer<Token=Self::Token>;

    /// Returns `t` as a success value in the parsing context.
    ///
    /// Equivalent to Haskell's `return` function in the `Monad` typeclass.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{Input, parse_only};
    ///
    /// let r = parse_only(|i|
    ///     // Annotate the error type
    ///     i.ret::<_, ()>("Wohoo, success!"),
    ///     b"some input");
    ///
    /// assert_eq!(r, Ok("Wohoo, success!"));
    /// ```
    #[inline]
    fn ret<T, E>(self, t: T) -> ParseResult<Self, T, E> {
        parse_result::new(self, Ok(t))
    }

    /// Returns `e` as an error value in the parsing context.
    ///
    /// A more general version of Haskell's `fail` function in the `Monad` typeclass.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{Input, parse_only};
    ///
    /// let r = parse_only(|i|
    ///     // Annotate the value type
    ///     i.err::<(), _>("Something went wrong"),
    ///     b"some input");
    ///
    /// assert_eq!(r, Err((&b"some input"[..], "Something went wrong")));
    /// ```
    #[inline]
    fn err<T, E>(self, e: E) -> ParseResult<Self, T, E> {
        parse_result::new(self, Err(e))
    }

    /// Converts a `Result` into a `ParseResult`, preserving parser state.
    ///
    /// To convert an `Option` into a `ParseResult` it is recommended to use
    /// [`Option::ok_or`](https://doc.rust-lang.org/std/option/enum.Option.html#method.ok_or)
    /// or [`Option::ok_or_else`](https://doc.rust-lang.org/std/option/enum.Option.html#method.ok_or_else)
    /// in combination with this method.
    ///
    /// # Examples
    ///
    /// ```
    /// use chomp::prelude::{Input, parse_only};
    ///
    /// let r = parse_only(|i| i.from_result::<_, ()>(Ok("foo")), b"test");
    ///
    /// assert_eq!(r, Ok("foo"));
    ///
    /// let r = parse_only(|i| i.from_result::<(), _>(Err("error message")), b"test");
    ///
    /// assert_eq!(r, Err((&b"test"[..], "error message")));
    /// ```
    #[inline]
    fn from_result<T, E>(self, r: Result<T, E>) -> ParseResult<Self, T, E> {
        parse_result::new(self, r)
    }

    // Primitive methods

    /// **Primitive:** See `Primitives::peek` for documentation.
    ///
    /// Peeks at the next token in the input without consuming it. `None` if no more input is
    /// available.
    ///
    /// Note: Will refill automatically.
    #[inline]
    fn _peek(&mut self, Guard) -> Option<Self::Token>;

    /// **Primitive:** See `Primitives::pop` for documentation.
    ///
    /// Pops a token off the start of the input. `None` if no more input is available.
    ///
    /// Note: Will refill automatically.
    #[inline]
    fn _pop(&mut self, Guard) -> Option<Self::Token>;

    /// **Primitive:** See `Primitives::consume` for documentation.
    ///
    /// Attempt to consume `n` tokens, if it fails do not advance the position but return `None`.
    #[inline]
    fn _consume(&mut self, Guard, usize) -> Option<Self::Buffer>;

    /// **Primitive:** See `Primitives::consume_while` for documentation.
    ///
    /// Runs the closure `F` on the tokens *in order* until it returns false, all tokens up to that
    /// token will be returned as a buffer and discarded from the current input. MUST never run the
    /// closure more than once on the exact same token.
    ///
    /// Note: Will refill automatically.
    #[inline]
    fn _consume_while<F>(&mut self, Guard, F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool;

    /// **Primitive:** See `Primitives::consume_from for documentation.
    ///
    /// Returns the buffer from the marker to the current position, discarding the
    /// backtracking position carried by the marker.
    #[inline]
    fn _consume_from(&mut self, Guard, Self::Marker) -> Self::Buffer;

    /// **Primitive:** See `Primitives::consume_remaining` for documentation.
    ///
    /// Returns the remainder of the input in a buffer.
    ///
    /// Note: Will refill the intenal buffer until no more data is available if the underlying
    /// implementation supports it.
    #[inline]
    fn _consume_remaining(&mut self, Guard) -> Self::Buffer;

    /// **Primitive:** See `Primitives::mark` for documentation.
    ///
    /// Marks a position for backtracking along with relevant state.
    #[inline]
    fn _mark(&self, Guard) -> Self::Marker;

    /// **Primitive:** See `Primitives::restore` for documentation.
    ///
    /// Resumes from a previously marked state.
    #[inline]
    fn _restore(self, Guard, Self::Marker) -> Self;
}

#[cfg(test)]
mod test {
    use super::{Input, InputBuf, ParseResult};
    use primitives::IntoInner;

    #[test]
    fn ret() {
        let i1: InputBuf<u8> = InputBuf::new(b"in1");
        let i2: InputBuf<u8> = InputBuf::new(b"in2");

        let r1: ParseResult<_, u32, ()> = i1.ret::<_, ()>(23u32);
        let r2: ParseResult<_, i32, &str> = i2.ret::<_, &str>(23i32);

        assert_eq!(r1.into_inner(), (InputBuf::new(b"in1"), Ok(23u32)));
        assert_eq!(r2.into_inner(), (InputBuf::new(b"in2"), Ok(23i32)));
    }

    #[test]
    fn err() {
        let i1: InputBuf<u8> = InputBuf::new(b"in1");
        let i2: InputBuf<u8> = InputBuf::new(b"in2");

        let r1: ParseResult<_, (), u32>   = i1.err::<(), _>(23u32);
        let r2: ParseResult<_, &str, i32> = i2.err::<&str, _>(23i32);

        assert_eq!(r1.into_inner(), (InputBuf::new(b"in1"), Err(23u32)));
        assert_eq!(r2.into_inner(), (InputBuf::new(b"in2"), Err(23i32)));
    }

    #[test]
    fn from_result() {
        let i1: Result<u32, &str> = Ok(23);
        let i2: Result<&str, &str> = Err("foobar");

        let r1 = InputBuf::new(b"in1").from_result(i1);
        let r2 = InputBuf::new(b"in2").from_result(i2);

        assert_eq!(r1.into_inner(), (InputBuf::new(b"in1"), Ok(23u32)));
        assert_eq!(r2.into_inner(), (InputBuf::new(b"in2"), Err("foobar")));
    }
}
