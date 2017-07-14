//! Implementation of datasources for `Source`.

use std::io;

/// Abstraction over `io::Read`, `Iterator` and others.
pub trait DataSource {
    /// The type of items this data source produces.
    type Item: Copy + PartialEq;

    /// Populates the supplied buffer with data, returns the number of items written.
    ///
    /// # Notes
    ///
    /// * The number returned must not be larger than the length of the supplied slice.
    ///
    /// * If no data could be written (or is available), or if the slice is of zero-length, `Ok(0)`
    ///   should be returned (includes EOF).
    ///
    /// * The slice must not be read from, may contain uninitialized memory.
    #[inline]
    fn read(&mut self, &mut [Self::Item]) -> io::Result<usize>;
}

/// Implementation of `DataSource` for `io::Read` instances.
// TODO: Tests
#[derive(Debug)]
pub struct ReadDataSource<R: io::Read>(R);

impl<R: io::Read> ReadDataSource<R> {
    /// Creates a new `ReadDataSource` from a `Read` instance.
    #[inline]
    pub fn new(inner: R) -> Self {
        ReadDataSource(inner)
    }

    /// Consumes self to reveal the underlying `Read` instance.
    #[inline]
    pub fn into_inner(self) -> R {
        self.0
    }
}

impl<R: io::Read> DataSource for ReadDataSource<R> {
    type Item = u8;

    #[inline]
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        self.0.read(buffer)
    }
}


/// Implementation of `DataSource` for streams (e.g. network connections) that you can `Read` and
/// `Write`. It's really helpful to have the ability to write through the `DataSource` and `Source`
/// objects, because once created, often they take full ownership of your input stream, and when
/// working with bidirectional connections you still need a way to write to them.
#[derive(Debug)]
pub struct RWDataSource<RW: io::Read + io::Write>(RW);

impl<RW: io::Read + io::Write> RWDataSource<RW> {
    /// Creates a new `RWDataSource` from a stream (e.g. network connection).
    pub fn new(inner: RW) -> Self {
        RWDataSource(inner)
    }

    /// Consumes self to reveal the underlying stream.
    #[inline]
    pub fn into_inner(self) -> RW {
        self.0
    }
}

impl<RW: io::Read + io::Write> DataSource for RWDataSource<RW> {
    type Item = u8;

    #[inline]
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        self.0.read(buffer)
    }
}

impl<RW: io::Read + io::Write> io::Write for RWDataSource<RW> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
    }
}

/// Implementation of `DataSource` for `Iterator`.
// TODO: Tests
#[derive(Debug)]
pub struct IteratorDataSource<I: Iterator>(I);

impl<I: Iterator> IteratorDataSource<I> {
    /// Creates a new `IteratorDataSource` from an `Iterator` instance.
    #[inline]
    pub fn new(inner: I) -> Self {
        IteratorDataSource(inner)
    }

    /// Consumes self to reveal the underlying `Iterator` instance.
    #[inline]
    pub fn into_inner(self) -> I {
        self.0
    }
}

impl<I: Iterator> DataSource for IteratorDataSource<I>
  where I::Item: Copy + PartialEq {
    type Item = I::Item;

    #[inline]
    fn read(&mut self, buffer: &mut [I::Item]) -> io::Result<usize> {
        let mut n = 0;

        while buffer.len() > n {
            if let Some(i) = self.0.next() {
                buffer[n] = i;
            } else {
                break;
            }

            n += 1;
        }

        Ok(n)
    }
}
