//! Utilities for parsing streams of data.
//!
//! # Examples
//!
//! ```
//! # #[macro_use] extern crate chomp;
//! # fn main() {
//! use std::fs::File;
//!
//! use chomp::buffer;
//! use chomp::buffer::Stream;
//! use chomp::prelude::{token, take_while, take_while1};
//! use chomp::ascii::is_whitespace;
//!
//! let f = File::open("./README.md").unwrap();
//!
//! let mut b = buffer::Source::from_read(f, buffer::FixedSizeBuffer::new());
//!
//! let r = b.parse(parser!{
//!     take_while(|c| c != b'#');
//!     token(b'#');
//!     take_while1(is_whitespace);
//!     take_while1(|c| c != b'\r' && c != b'\n')
//! });
//!
//! assert_eq!(r, Ok(&b"Chomp"[..]));
//! # }
//! ```

mod stateful;
mod slice;

pub mod data_source;

use std::io;
use std::ops;
use std::ptr;

use std::cell::Cell;

use types::{Input, ParseResult};
use types::Buffer as InputBuffer;
use primitives::Guard;

pub use self::slice::SliceStream;
pub use self::data_source::{DataSource, RWDataSource};
pub use self::stateful::Source;

const DEFAULT_BUFFER_SIZE: usize = 6 * 1024;

/// Error type for parsing using the `Stream` trait.
#[derive(Debug)]
pub enum StreamError<B: InputBuffer, E> {
    /// An error occurred in the parser, the given slice indicates the part which failed.
    ParseError(B, E),
    /// Parser failed to complete with the available data.
    Incomplete,
    /// An IO-error occurred while attempting to fill the buffer.
    IoError(io::Error),
    /// The last parser completed successfully and there is no more input to parse.
    EndOfInput,
    /// The last parser failed with an incomplete state, fill the buffer and try again.
    ///
    /// Filling the buffer is automatic by default.
    Retry,
}

impl<B: InputBuffer, E: PartialEq<E>> PartialEq for StreamError<B, E> {
    #[inline]
    fn eq(&self, other: &StreamError<B, E>) -> bool {
        match (self, other) {
            (&StreamError::ParseError(ref b1, ref e1), &StreamError::ParseError(ref b2, ref e2)) => b1 == b2 && e1 == e2,
            (&StreamError::Incomplete, &StreamError::Incomplete)
              | (&StreamError::EndOfInput, &StreamError::EndOfInput)
              | (&StreamError::Retry, &StreamError::Retry)           => true,
            _ => false,
        }
    }
}

/// Trait wrapping the state management in reading from a data source while parsing.
pub trait Stream<'a, 'i> {
    /// The input item type, usually depending on which `DataSource` is used.
    type Input: Input + 'i;

    /// Attempts to run the supplied parser `F` once on the currently populated data in this
    /// stream, providing a borrow of the inner data storage.
    ///
    /// If a `StreamError::Retry` is returned the consuming code it should just retry the action
    /// (the implementation might require a separate call to refill the stream).
    #[inline]
    fn parse<F, T, E>(&'a mut self, f: F) -> Result<T, StreamError<<Self::Input as Input>::Buffer, E>>
      where F: FnOnce(Self::Input) -> ParseResult<Self::Input, T, E>,
            T: 'i,
            E: 'i;
}

/// Input buffer type which contains a flag which tells if we might need to read more data.
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct InputBuf<'a, I: 'a>(
    /// If this is set to true a parser has tried to read past the end of this buffer.
    bool,
    /// Current buffer slice
    &'a [I],
);

impl<'a, I: 'a> InputBuf<'a, I> {
    /// Creates a new input buffer with incomplete set to false.
    #[inline]
    pub fn new(buf: &'a [I]) -> Self {
        InputBuf(false, buf)
    }

    /// Returns true if parsers want to obtain more data.
    ///
    /// The result of the parsing is only accurate if this is false after completed parsing.
    #[inline]
    pub fn is_incomplete(&self) -> bool {
        self.0
    }

    /// Returns the length of the contained buffer, may be an incomplete buffer.
    #[inline]
    pub fn len(&self) -> usize {
        self.1.len()
    }

    /// Returns true if the contained buffer is empty, may return true even when incomplete.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, I: Copy + PartialEq> Input for InputBuf<'a, I> {
    type Token  = I;
    type Marker = &'a [I];
    type Buffer = &'a [I];

    #[inline]
    fn _peek(&mut self, _g: Guard) -> Option<Self::Token> {
        if let Some(c) = self.1.first() {
            Some(*c)
        } else {
            self.0 = true;

            None
        }
    }

    #[inline]
    fn _pop(&mut self, g: Guard) -> Option<Self::Token> {
        self._peek(g).map(|c| {
            self.1 = &self.1[1..];

            c
        })
    }

    #[inline]
    fn _consume(&mut self, _g: Guard, n: usize) -> Option<Self::Buffer> {
        if n > self.1.len() {
            self.0 = true;

            None
        } else {
            let b = &self.1[..n];

            self.1 = &self.1[n..];

            Some(b)
        }
    }

    #[inline]
    fn _consume_while<F>(&mut self, g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        if let Some(n) = self.1.iter().position(|c| !f(*c)) {
            let b = &self.1[..n];

            self.1 = &self.1[n..];

            b
        } else {
            self._consume_remaining(g)
        }
    }

    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.1.len()]
    }

    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        self.0 = true;

        let b = self.1;

        self.1 = &self.1[b.len()..];

        b
    }

    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        // Incomplete state is separate from the parsed state, no matter how we hit incomplete we
        // want to keep it.
        self.1
    }

    #[inline]
    fn _restore(mut self, _g: Guard, m: Self::Marker) -> Self {
        self.1 = m;

        self
    }
}

/// Trait all parser buffers implement.
///
/// Enables the consumer to request specific amounts of data and only consume partial parts of the
/// buffer.
pub trait Buffer<I: Copy + PartialEq>: ops::Deref<Target=[I]> {
    /// Attempt to fill the buffer using the closure `F`.
    ///
    /// The successful return from `F` should contain the number of items successfully written to
    /// the slice.
    ///
    /// # Notes
    ///
    /// * The returned value must *NOT* be larger than the length of the given slice.
    ///
    /// * Return `0` if no more data is available or if the slice is of zero length.
    ///
    /// * The slice might contain uninitialized memory, do not read from the slice.
    #[inline]
    fn fill<S: DataSource<Item=I>>(&mut self, &mut S) -> io::Result<usize>;

    /// Buffer attempts to clear space for additional items.
    #[inline]
    fn request_space(&mut self, usize);

    /// Consumes the given amount of bytes, must be less than or equal to `len()`.
    ///
    /// Does not invalidate any borrow of data from self.
    #[inline]
    fn consume(&self, items: usize);

    /// Returns the number of bytes left in the buffer.
    #[inline]
    fn len(&self) -> usize;

    /// If the buffer has no more data.
    #[inline]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the maximum amount of data which can be stored
    #[inline]
    fn capacity(&self) -> usize;
}

/// A fixed size buffer.
///
/// Only allocates when created.
// TODO: Tests
#[derive(Debug, Eq, PartialEq)]
pub struct FixedSizeBuffer<I: Copy + PartialEq> {
    /// Backing memory.
    buffer:    Vec<I>,
    /// Number of items of `buffer` which contain actual data.
    populated: usize,
    /// The number of bytes from the start of the buffer which are used.
    ///
    /// As long as used <= populated it is safe.
    used:      Cell<usize>,
}

impl<I: Copy + PartialEq> FixedSizeBuffer<I> {
    /// Creates a fixed-size buffer with the default buffer size.
    #[inline]
    pub fn new() -> Self {
        Self::with_size(DEFAULT_BUFFER_SIZE)
    }

    /// Creates a fixed-size buffer with the supplied buffer size.
    #[inline]
    pub fn with_size(size: usize) -> Self {
        assert!(size > 0);

        let mut buf = Vec::with_capacity(size);

        // TODO: Would it be better with a Default requirement on I?
        // We set the length here to allow fill() to hand out a slice of uninitialized memory
        // to be populated.
        // NOTE: We cannot actually expose this memory to the parser since self.populated will
        // be the upper limit for the deref to slice.
        unsafe {
            buf.set_len(size);
        }

        FixedSizeBuffer {
            buffer:    buf,
            populated: 0,
            used:      Cell::new(0),
        }
    }
}

impl<I: Copy + PartialEq> ops::Deref for FixedSizeBuffer<I> {
    type Target = [I];

    #[inline]
    fn deref(&self) -> &[I] {
        &self.buffer[self.used.get()..self.populated]
    }
}

impl<I: Copy + PartialEq> ops::DerefMut for FixedSizeBuffer<I> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [I] {
        &mut self.buffer[self.used.get()..self.populated]
    }
}

impl<I: Copy + PartialEq> Buffer<I> for FixedSizeBuffer<I> {
    #[inline]
    fn fill<S: DataSource<Item=I>>(&mut self, s: &mut S) -> io::Result<usize> {
        s.read(&mut self.buffer[self.populated..]).map(|n| {
            debug_assert!(self.populated + n <= self.buffer.len());

            self.populated += n;

            n
        })
    }

    #[inline]
    fn request_space(&mut self, items: usize) {
        use std::ptr;

        assert!(self.populated >= self.used.get());

        // Only copy if we actually need to free the space
        if self.buffer.len() - self.populated < items {
            unsafe {
                ptr::copy(self.buffer.as_ptr().offset(self.used.get() as isize), self.buffer.as_mut_ptr(), self.populated - self.used.get());
            }

            self.populated -= self.used.get();
            self.used.set(0);
        }
    }

    #[inline]
    fn consume(&self, items: usize) {
        debug_assert!(self.used.get() + items <= self.populated);

        self.used.set(self.used.get() + items)
    }

    #[inline]
    fn len(&self) -> usize {
        self.populated - self.used.get()
    }

    #[inline]
    fn capacity(&self) -> usize {
        self.buffer.len()
    }
}

/// A buffer which will reallocate to fit the requested amount of data.
///
/// # Note:
///
/// Will not decrease in size.
// TODO: Tests
#[derive(Debug)]
pub struct GrowingBuffer<I: Copy + PartialEq> {
    /// Backing memory.
    buffer:    Vec<I>,
    /// Number of items of `buffer` which contain actual data.
    populated: usize,
    /// Maximal size of the buffer, 0 means infinity.
    limit:     usize,
    /// The number of bytes from the start of the buffer which are used.
    ///
    /// As long as used <= populated it is safe.
    used:      Cell<usize>,
}

impl<I: Copy + PartialEq> GrowingBuffer<I> {
    /// Creates a new unlimited `GrowingBuffer`.
    #[inline]
    pub fn new() -> Self {
        Self::with_limit(0)
    }

    /// Creates a new `GrowingBuffer` with the specified limit.
    ///
    /// # Note
    ///
    /// The actual amount of allocated memory might be larger than the specified limit, depends on
    /// the allocator.
    #[inline]
    pub fn with_limit(limit: usize) -> Self {
        GrowingBuffer {
            buffer:    Vec::new(),
            populated: 0,
            limit:     limit,
            used:      Cell::new(0),
        }
    }
}

impl<I: Copy + PartialEq> ops::Deref for GrowingBuffer<I> {
    type Target = [I];

    #[inline]
    fn deref(&self) -> &[I] {
        &self.buffer[self.used.get()..self.populated]
    }
}

impl<I: Copy + PartialEq> ops::DerefMut for GrowingBuffer<I> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [I] {
        &mut self.buffer[self.used.get()..self.populated]
    }
}

impl<I: Copy + PartialEq> Buffer<I> for GrowingBuffer<I> {
    #[inline]
    fn fill<S: DataSource<Item=I>>(&mut self, s: &mut S) -> io::Result<usize> {
        s.read(&mut self.buffer[self.populated..]).map(|n| {
            debug_assert!(self.populated + n <= self.buffer.len());

            self.populated += n;

            n
        })
    }

    #[inline]
    fn request_space(&mut self, items: usize) {
        // If we are over the limit, refuse
        if self.limit != 0 && self.buffer.capacity() > self.limit {
            return;
        }

        if items + self.len() > self.buffer.capacity() {
            // We do not have enough space for the new items, reallocate
            self.buffer.reserve(items);

            let cap = self.buffer.capacity();

            // TODO: Would it be better with a Default requirement on I?
            // We set the length here to allow fill() to hand out a slice of uninitialized memory
            // to be populated.
            // NOTE: We cannot actually expose this memory to the parser since self.populated will
            // be the upper limit for the deref to slice.
            unsafe {
                self.buffer.set_len(cap);
            }
        }

        // Only copy if we actually need to free the space
        if self.buffer.len() - self.populated < items {
            unsafe {
                ptr::copy(self.buffer.as_ptr().offset(self.used.get() as isize), self.buffer.as_mut_ptr(), self.populated - self.used.get());
            }

            self.populated -= self.used.get();
            self.used.set(0);
        }
    }

    #[inline]
    fn consume(&self, items: usize) {
        debug_assert!(self.used.get() + items <= self.populated);

        self.used.set(self.used.get() + items)
    }

    #[inline]
    fn len(&self) -> usize {
        self.populated - self.used.get()
    }

    #[inline]
    fn capacity(&self) -> usize {
        self.buffer.len()
    }
}

#[cfg(test)]
mod test {
    use super::InputBuf;
    use types::{Input, ParseResult};
    use primitives::{IntoInner, Primitives};

    use types::test::run_primitives_test;

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
    fn test_input_buf() {

        run_primitives_test(InputBuf::new(b"abc"), |x| x);

        let mut b = InputBuf::new(b"a");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        b.peek();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        b.pop();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.peek(), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.pop(), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);
        b.consume(1);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        b.consume(1);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.consume(1), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.consume(3), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.consume_while(|_| true), &b"ab"[..]);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.consume_while(|c| c == b'a'), &b"a"[..]);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.consume_while(|c| c == b'b'), &b"b"[..]);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.consume_while(|c| c == b'b'), &b""[..]);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"abc");
        let m = b.mark();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);
        b.consume(3);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.consume_from(m), &b"abc"[..]);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"abc");
        let m = b.mark();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);
        b.consume(2);
        b.consume(2);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        let b = b.restore(m);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);

        let mut b = InputBuf::new(b"abc");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);
        b.consume_remaining();
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
    }

    #[test]
    fn test_consuming_whole_buffer_does_not_reset_the_pointer() {
        let slice = b"abc";
        let mut b = InputBuf::new(slice);
        b.consume(1);
        b.consume_while(|_| true);
        let consumed = b.1.as_ptr() as usize - slice.as_ptr() as usize;
        assert_eq!(consumed, 3);
    }
}
