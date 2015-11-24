//! Module used to construct fundamental parsers and combinators.
//!
//! # Internal
//!
//! Only used by fundamental parsers and combinators.

pub mod iter;

use Input;

/// Internal inner type containing the parse-state.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum State<'a, I: 'a, T, E>
  where I: 'a,
        T: 'a,
        E: 'a {
    Data(Input<'a, I>, T),
    Error(&'a [I], E),
    /// The number of additional items requested
    Incomplete(usize),
}

pub trait IntoInner {
    type Inner;

    /// Consumes self and reveals the inner state.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn into_inner(self) -> Self::Inner;
}

pub trait InputClone {
    /// Creates a clone of the instance.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn clone(&self) -> Self;
}

pub trait InputBuffer<'a> {
    type Item: 'a;

    /// Reveals the internal buffer containig the remainder of the input.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn buffer(&self) -> &'a [Self::Item];

    /// Modifies the inner data without leaving the `Input` context.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn replace(self, &'a [Self::Item]) -> Self;

    /// Returns true if this is the last available slice of the input.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn is_last_slice(&self) -> bool;
}

/// Input utilities.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
pub mod input {
    pub use input::{DEFAULT, END_OF_INPUT, new};
}

/// ParseResult utilities.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
///
/// # Note
///
/// Prefer to use ``Input::ret``, ``Input::err`` or ``Input::incomplete`` instead of using
/// ``parse_result::new``.
pub mod parse_result {
    pub use parse_result::new;
}
