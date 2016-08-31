//! Module used to construct fundamental parsers and combinators.
//!
//! The `Primitives` trait allows access to the primitive methods of the `Input` trait. These
//! methods are hidden in the documentation to make it easier to read the documentation since the
//! methods are not useful when using the library or writing primitive parsers.

use types::Input;

/// Consumes self and reveals the inner state.
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
///
/// This trait is automatically implemented for all types implementing `Input` and acts as a
/// gatekeeper to the state-modifying methods of `Input`.
pub trait Primitives: Input {
    /// Peeks at the next token in the input without consuming it. `None` if no more input is
    /// available.
    ///
    /// Note: Is allowed to refill automatically or any other appropriate action if the input does
    /// not contain any more data.
    #[inline(always)]
    fn peek(&mut self) -> Option<Self::Token> {
        self._peek(Guard(()))
    }

    /// Pops a token off the start of the input. `None` if no more input is available.
    ///
    /// Note: Is allowed to refill automatically or any other appropriate action if the input does
    /// not contain any more data.
    #[inline(always)]
    fn pop(&mut self) -> Option<Self::Token> {
        self._pop(Guard(()))
    }

    /// Attempt to consume `n` tokens, if it fails do not advance the position but return `None`.
    ///
    /// Note: Is allowed to refill automatically or any other appropriate action if the input does
    /// not contain any more data.
    #[inline(always)]
    fn consume(&mut self, n: usize) -> Option<Self::Buffer> {
        self._consume(Guard(()), n)
    }

    /// Runs the closure `F` on the tokens *in order* until it returns false, all tokens up to that
    /// token will be returned as a buffer and discarded from the current input. MUST never run the
    /// closure more than once on the exact same token.
    ///
    /// If the end of the input is reached, the whole input is returned.
    ///
    /// Note: Is allowed to refill automatically or any other appropriate action if the input does
    /// not contain any more data.
    #[inline(always)]
    fn consume_while<F>(&mut self, f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        self._consume_while(Guard(()), f)
    }

    /// Returns the buffer from the marker to the current position, discarding the
    /// backtracking position carried by the marker.
    #[inline(always)]
    fn consume_from(&mut self, m: Self::Marker) -> Self::Buffer {
        self._consume_from(Guard(()), m)
    }

    /// Returns the remainder of the input in a buffer.
    ///
    /// Note: Will refill the intenal buffer until no more data is available if the underlying
    /// implementation supports it.
    #[inline(always)]
    fn consume_remaining(&mut self) -> Self::Buffer {
        self._consume_remaining(Guard(()))
    }

    /// Runs the closure `F` on the tokens *in order* until it returns false, all tokens up to that
    /// token will be discarded from the current input.
    ///
    /// MUST never run the closure more than once on the exact same token.
    ///
    /// If the end of the input is reached, the whole input is discarded.
    ///
    /// Note: Default implementation uses `consume_while` and makes the assumption that it will
    /// optimize away the resulting `Self::Buffer`.
    #[inline(always)]
    fn skip_while<F>(&mut self, f: F)
      where F: FnMut(Self::Token) -> bool {
        self._skip_while(Guard(()), f)
    }

    /// Marks the current position to be able to backtrack to it using `restore`.
    #[inline(always)]
    fn mark(&self) -> Self::Marker {
        self._mark(Guard(()))
    }

    /// Resumes from a previously marked state.
    #[inline(always)]
    fn restore(self, m: Self::Marker) -> Self {
        self._restore(Guard(()), m)
    }
}

impl<I: Input> Primitives for I {}
