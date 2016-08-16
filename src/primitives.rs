//! Module used to construct fundamental parsers and combinators.
//!
//! The `Primitives` trait allows access to the primitive methods of the `Input` trait. These
//! methods are hidden in the documentation to make it easier to read the documentation since the
//! methods are not useful when using the library or writing primitive parsers.

use types::Input;

/// **Primitive:** Consumes self and reveals the inner state.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
pub trait IntoInner {
    /// The inner type to be revealed.
    type Inner;

    /// **Primitive:** Consumes self and reveals the inner state.
    ///
    /// # Primitive
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn into_inner(self) -> Self::Inner;
}

/// This is a zero-sized type used by the `Primitives` trait implementation to guarantee that
/// access to primitive methods on `Input` only happens when the `Primitives` trait has been
/// imported.
///
/// It cannot be instantiated outside of the `Primitives` trait blanket implementation.
pub struct Guard(());

/// Trait enabling primitive actions on an `Input` type.
// FIXME: Rename and documentation
pub trait Primitives: Input {
    #[inline(always)]
    fn peek(&mut self) -> Option<Self::Token> {
        self._peek(Guard(()))
    }

    #[inline(always)]
    fn pop(&mut self) -> Option<Self::Token> {
        self._pop(Guard(()))
    }

    #[inline(always)]
    fn consume(&mut self, n: usize) -> Option<Self::Buffer> {
        self._consume(Guard(()), n)
    }

    #[inline(always)]
    fn consume_while<F>(&mut self, f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        self._consume_while(Guard(()), f)
    }

    /// Returns the buffer from the marker `m` to the current position, discarding the
    /// backtracking position carried by `m`.
    #[inline(always)]
    fn consume_from(&mut self, m: Self::Marker) -> Self::Buffer {
        self._consume_from(Guard(()), m)
    }

    #[inline(always)]
    fn consume_remaining(&mut self) -> Self::Buffer {
        self._consume_remaining(Guard(()))
    }

    /// Marks the current position to be able to backtrack to it using `restore`.
    #[inline(always)]
    fn mark(&self) -> Self::Marker {
        self._mark(Guard(()))
    }

    #[inline(always)]
    fn restore(self, m: Self::Marker) -> Self {
        self._restore(Guard(()), m)
    }
}

impl<I: Input> Primitives for I {}
