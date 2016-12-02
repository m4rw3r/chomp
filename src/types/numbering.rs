//! Module containing tools for working with position aware parsers.
//!
//! ```
//! # #[macro_use] extern crate chomp;
//! # fn main() {
//! use chomp::types::{Input, ParseResult};
//! use chomp::types::numbering::{InputPosition, LineNumber, Numbering};
//! use chomp::combinators::many;
//! use chomp::parsers::{Error, any, take_while1, string};
//! use chomp::run_parser;
//!
//! // Let's count some lines
//! let i = InputPosition::new(&b"test a\ntest b\n\ntest c\n"[..], LineNumber::new());
//!
//! // We could use a concrete type P too if we want to restrict to a
//! // certain position-aware implementation
//! fn parser<I: Input<Token=u8>, P: Numbering<Token=u8>>(i: InputPosition<I, P>)
//!   -> ParseResult<InputPosition<I, P>, (char, P), Error<u8>> {
//!     parse!{i;
//!                      string(b"test");
//!                      take_while1(|c| c == b' ' || c == b'\t');
//!         let t_name = any();
//!         i -> {
//!             // Obtain current parser position
//!             let p = i.position();
//!
//!             i.ret((t_name as char, p))
//!             // We skip the take while below, because we want to determine the line right
//!             // after reading the t_name
//!         } <* take_while1(|c| c == b'\n');
//!     }
//! }
//!
//! let r = run_parser(i, |i| many(i, parser)).1;
//!
//! assert_eq!(r, Ok(vec![('a', LineNumber(0)),
//!                       ('b', LineNumber(1)),
//!                       // Note the two linebreaks in a row
//!                       ('c', LineNumber(3))]));
//! # }
//! ```

use primitives::{Guard, IntoInner};
use types::{Buffer, Input};

/// Trait for managing some kind of numbering over the parsed data.
pub trait Numbering: Clone {
    /// The token type accepted by the numbering.
    type Token: Copy + PartialEq;

    /// Updates the numbering based on the contents of the buffer, adding it to the current
    /// numbering.
    fn update<B>(&mut self, &B)
      where B: Buffer<Token=Self::Token>;

    /// Adds the token to the numbering.
    fn add(&mut self, Self::Token);
}

/// Struct counting the number of newlines (`b'\n'`).
#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct LineNumber(
    /// The current line, zero-indexed.
    pub u64,
);

impl LineNumber {
    /// Creates a new line-number counter with zero.
    pub fn new() -> Self {
        LineNumber(0)
    }
}

impl Default for LineNumber {
    fn default() -> Self {
        LineNumber::new()
    }
}

impl Numbering for LineNumber {
    type Token  = u8;

    fn update<B>(&mut self, b: &B)
      where B: Buffer<Token=Self::Token> {
        let mut n = 0;

        b.iterate(|c| if c == b'\n' {
            n += 1;
        });

        self.0 += n
    }

    fn add(&mut self, t: Self::Token) {
        if t == b'\n' {
            self.0 += 1
        }
    }
}

/// Wrapper around an `Input` implementation providing numbering support.
#[derive(Debug)]
pub struct InputPosition<I: Input, N: Numbering<Token=I::Token>> {
    input: I,
    num:   N,
}

impl<I: Input, N: Numbering<Token=I::Token>> InputPosition<I, N> {
    /// Creates a new input position instance.
    pub fn new(i: I, n: N) -> Self {
        InputPosition {
            input: i,
            num:   n,
        }
    }

    /// Obtains the current position of the numbering.
    pub fn position(&self) -> N {
        self.num.clone()
    }
}

impl<I: Input, N: Numbering<Token=I::Token>> IntoInner for InputPosition<I, N> {
    type Inner = (I, N);

    fn into_inner(self) -> Self::Inner {
        (self.input, self.num)
    }
}

impl<I: Input, N: Numbering<Token=I::Token>> Input for InputPosition<I, N> {
    type Token  = I::Token;
    type Marker = (N, I::Marker);
    type Buffer = I::Buffer;

    #[inline]
    fn _peek(&mut self, g: Guard) -> Option<Self::Token> {
        self.input._peek(g)
    }

    #[inline]
    fn _pop(&mut self, g: Guard) -> Option<Self::Token> {
        self.input._pop(g).map(|t| {
            self.num.add(t);

            t
        })
    }

    #[inline]
    fn _consume(&mut self, g: Guard, n: usize) -> Option<Self::Buffer> {
        self.input._consume(g, n).map(|b| {
            self.num.update(&b);

            b
        })
    }

    #[inline]
    fn _consume_while<F>(&mut self, g: Guard, f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        let b = self.input._consume_while(g, f);

        self.num.update(&b);

        b
    }

    #[inline]
    fn _consume_from(&mut self, g: Guard, m: Self::Marker) -> Self::Buffer {
        // We have already counted to current position, no need to update
        self.input._consume_from(g, m.1)
    }

    #[inline]
    fn _consume_remaining(&mut self, g: Guard) -> Self::Buffer {
        let b = self.input._consume_remaining(g);

        self.num.update(&b);

        b
    }

    #[inline]
    fn _mark(&self, g: Guard) -> Self::Marker {
        (self.num.clone(), self.input._mark(g))
    }

    #[inline]
    fn _restore(self, g: Guard, m: Self::Marker) -> Self {
        InputPosition {
            input: self.input._restore(g, m.1),
            num:   m.0,
        }
    }
}

#[cfg(test)]
mod test {
    use types::{Input, ParseResult};
    use super::{InputPosition, LineNumber};
    use primitives::IntoInner;

    #[test]
    fn basic_test() {
        use combinators::many;
        use parsers::{Error, any, take_while1, string};

        let i = InputPosition::new(&b"test a\ntest b\n\ntest c\n"[..], Default::default());

        fn parser<I: Input<Token=u8>>(i: InputPosition<I, LineNumber>)
          -> ParseResult<InputPosition<I, LineNumber>, (char, LineNumber), Error<u8>> {
            parse!{i;
                string(b"test");
                take_while1(|c| c == b' ' || c == b'\t');
                let t_name = any();
                i -> {
                    let p = i.position();

                    i.ret((t_name as char, p))
                    // We skip the take while below, because we want to determine the line right
                    // after reading the t_name
                } <* take_while1(|c| c == b'\n');
            }
        }

        assert_eq!(many(i, parser).into_inner().1, Ok(vec![
                                                      ('a', LineNumber(0)),
                                                      ('b', LineNumber(1)),
                                                      // Note the two linebreaks in a row
                                                      ('c', LineNumber(3))]));
    }
}
