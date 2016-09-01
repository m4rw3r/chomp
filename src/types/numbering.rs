//! Module containing tools for working with position aware parsers.
//!
//! ```
//! #![feature(conservative_impl_trait)]
//! # #[macro_use] extern crate chomp;
//! # fn main() {
//! use chomp::types::{Input, Parser, ret};
//! use chomp::types::numbering::{InputPosition, LineNumber, Numbering, position};
//! use chomp::combinators::many;
//! use chomp::parsers::{Error, any, take_while1, string};
//!
//! let i = InputPosition::new(&b"test a\ntest b\n\ntest c\n"[..], Default::default());
//!
//! fn parser<I: Input<Token=u8>>() -> impl Parser<InputPosition<I, LineNumber>, Output=(char, LineNumber), Error=Error<u8>> {
//!     parse!{
//!         string(b"test");
//!         take_while1(|c| c == b' ' || c == b'\t');
//!         let t_name = any();
//!         let p      = position();
//!
//!         ret((t_name as char, p))
//!         // We skip the take while below, because we want to determine the line right
//!         // after reading the t_name
//!          <* take_while1(|c| c == b'\n');
//!     }
//! }
//!
//! assert_eq!(many(parser).parse(i).1, Ok(vec![('a', LineNumber(0)),
//!                                             ('b', LineNumber(1)),
//!                                             // Note the two linebreaks in a row
//!                                             ('c', LineNumber(3))]));
//! # }
//! ```

use types::{Buffer, Input, Parser};

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
#[derive(Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct LineNumber(
    /// The current line, zero-indexed.
    pub u64,
);

impl Clone for LineNumber {
    fn clone(&self) -> Self {
        LineNumber(self.0)
    }
}

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

/// A parser which obtains the current position while inside of a `Parser` monad provided the input
/// generic of `Parser` is an `InputPosition`.
pub fn position<I: Input, N: Numbering<Token=I::Token>, E>() -> impl Parser<InputPosition<I, N>, Output=N, Error=E> {
    move |i: InputPosition<I, N>| {
        let p = i.position();

        (i, Ok(p))
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

impl<I: Input, N: Numbering<Token=I::Token>> Input for InputPosition<I, N> {
    type Token  = I::Token;
    type Marker = (N, I::Marker);
    type Buffer = I::Buffer;

    #[inline]
    fn peek(&mut self) -> Option<Self::Token> {
        self.input.peek()
    }

    #[inline]
    fn pop(&mut self) -> Option<Self::Token> {
        self.input.pop().map(|t| {
            self.num.add(t);

            t
        })
    }

    #[inline]
    fn consume(&mut self, n: usize) -> Option<Self::Buffer> {
        self.input.consume(n).map(|b| {
            self.num.update(&b);

            b
        })
    }

    #[inline]
    fn consume_while<F>(&mut self, f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        let b = self.input.consume_while(f);

        self.num.update(&b);

        b
    }

    #[inline]
    fn consume_from(&mut self, m: Self::Marker) -> Self::Buffer {
        // We have already counted to current position, no need to update
        self.input.consume_from(m.1)
    }

    #[inline]
    fn consume_remaining(&mut self) -> Self::Buffer {
        let b = self.input.consume_remaining();

        self.num.update(&b);

        b
    }

    #[inline]
    fn mark(&self) -> Self::Marker {
        (self.num.clone(), self.input.mark())
    }

    #[inline]
    fn restore(self, m: Self::Marker) -> Self {
        InputPosition {
            input: self.input.restore(m.1),
            num:   m.0,
        }
    }
}

#[cfg(test)]
mod test {
    use types::{Input, Parser, ret};
    use super::{InputPosition, LineNumber, position};

    #[test]
    fn basic_test() {
        use combinators::many;
        use parsers::{Error, any, take_while1, string};

        let i = InputPosition::new(&b"test a\ntest b\n\ntest c\n"[..], Default::default());

        fn parser<I: Input<Token=u8>>() -> impl Parser<InputPosition<I, LineNumber>, Output=(char, LineNumber), Error=Error<u8>> {
            parse!{
                string(b"test");
                take_while1(|c| c == b' ' || c == b'\t');
                let t_name = any();
                let p      = position();

                ret((t_name as char, p))
                // We skip the take while below, because we want to determine the line right
                // after reading the t_name
                 <* take_while1(|c| c == b'\n');
            }
        }

        assert_eq!(many(parser).parse(i).1, Ok(vec![('a', LineNumber(0)),
                                                    ('b', LineNumber(1)),
                                                    // Note the two linebreaks in a row
                                                    ('c', LineNumber(3))]));
    }
}
