//! Module used to construct fundamental parsers and combinators.
//!
//! # Internal
//!
//! Only used by fundamental parsers and combinators.

use Input;

pub use input::InputClone;
pub use input::InputBuffer;

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

/// **Internal:** Consumes self and reveals the inner state.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
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
