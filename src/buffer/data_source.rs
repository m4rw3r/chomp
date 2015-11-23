//! Implementation of datasources for `Source`.

use std::io;

/// Abstraction over `io::Read`, `Iterator` and others.
pub trait DataSource {
    type Item;

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
    fn read(&mut self, &mut [Self::Item]) -> io::Result<usize>;
}

/// Implementation of `DataSource` for `io::Read` instances.
// TODO: Tests
pub struct ReadDataSource<R: io::Read>(R);

impl<R: io::Read> ReadDataSource<R> {
    pub fn new(inner: R) -> Self {
        ReadDataSource(inner)
    }

    pub fn into_inner(self) -> R {
        self.0
    }
}

impl<R: io::Read> DataSource for ReadDataSource<R> {
    type Item = u8;

    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        self.0.read(buffer)
    }
}

/// Implementation of `DataSource` for `Iterator`.
// TODO: Tests
pub struct IteratorDataSource<I: Iterator>(I);

impl<I: Iterator> IteratorDataSource<I> {
    pub fn new(inner: I) -> Self {
        IteratorDataSource(inner)
    }

    pub fn into_inner(self) -> I {
        self.0
    }
}

impl<I: Iterator> DataSource for IteratorDataSource<I> {
    type Item = I::Item;

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
