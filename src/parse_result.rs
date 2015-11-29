use std::fmt;

use parsers;
use input::Input;

/// Result for dealing with the basic parsers when parsing a stream of `u8`.
pub type U8Result<'a, T>        = ParseResult<'a, u8, T, parsers::Error<u8>>;
/// Result returned from the basic parsers.
pub type SimpleResult<'a, I, T> = ParseResult<'a, I, T, parsers::Error<I>>;

/// **Primitive:** Primitive inner type containing the parse-state.
///
/// # Primitive
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

/// **Primitive:** Consumes self and reveals the inner state.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
pub trait IntoInner {
    type Inner;

    /// **Primitive:** Consumes self and reveals the inner state.
    ///
    /// # Primitive
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn into_inner(self) -> Self::Inner;
}

/// The basic return type of a parser.
///
/// This type satisfies a variant of the ``Monad`` typeclass. Due to the limitations of Rust's
/// return types closures cannot be returned without boxing which has an unacceptable performance
/// impact.
///
/// To get around this issue and still provide a simple to use and safe (as in hard to accidentally
/// violate the monad laws or the assumptions taken by the parser type) an `Input` wrapper is
/// provided which ensures that the parser state is carried properly through every call to `bind`.
/// This is also known as a Linear Type (emulated through hiding destructors and using the
/// annotation ``#[must_use]``).
///
/// Do-notation is provided by the macro ``parse!``.
///
/// # Equivalence with Haskell's ``Monad`` typeclass:
///
/// ```text
/// f >>= g   ≡  f(m).bind(g)
/// f >> g    ≡  f(m).then(g)
/// return a  ≡  m.ret(a)
/// fail a    ≡  m.err(a)
/// ```
///
/// It also satisfies the monad laws:
///
/// ```text
/// return a >>= f   ≡  f a
/// m >>= return     ≡  m
/// (m >>= f) >>= g  ≡  m >>= (\x -> f x >>= g)
/// ```
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ParseResult<'a, I: 'a, T: 'a, E: 'a>(State<'a, I, T, E>);

/// **Primitive:** Creates a new `ParseResult`.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
///
/// # Note
///
/// Prefer to use ``Input::ret``, ``Input::err`` or ``Input::incomplete`` instead of using
pub fn new<I, T, E>(s: State<I, T, E>) -> ParseResult<I, T, E> {
    ParseResult(s)
}

impl<'a, I, T, E> ParseResult<'a, I, T, E> {
    /// Sequentially composes the result with a parse action ``f``, passing any produced value as
    /// the second parameter.
    ///
    /// The first parameter to the supplied function ``f`` is the parser state (``Input``). This
    /// state is then passed on to other parsers or used to return a value or an error.
    ///
    /// # Automatic conversion of ``E``
    ///
    /// The error value ``E`` will automatically be converted using the ``From`` trait to the
    /// desired type. The downside with this using the current stable version of Rust (1.4) is that
    /// the type inferrence will currently not use the default value for the generic ``V`` and will
    /// therefore require extra type hint for the error.
    ///
    /// # Examples
    ///
    /// ```
    /// use chomp::{Input, Error};
    ///
    /// let p = Input::new(b"test").ret("data".to_owned());
    /// // Explicitly state the error type
    /// let r = p.bind::<_, _, ()>(|i, x| i.ret(x + " here!"));
    ///
    /// assert_eq!(r.unwrap(), "data here!");
    /// ```
    ///
    /// Using a function which wraps the expression will both make it easier to compose and also
    /// provides the type-hint for the error in the function signature:
    ///
    /// ```
    /// use chomp::{Input, ParseResult};
    ///
    /// fn parser(i: Input<u8>, n: i32) -> ParseResult<u8, i32, ()> {
    ///     i.ret(n + 10)
    /// }
    ///
    /// let p = Input::new(b"test").ret(23);
    ///
    /// assert_eq!(p.bind(parser).unwrap(), 33);
    /// ```
    #[inline]
    pub fn bind<F, U, V = E>(self, f: F) -> ParseResult<'a, I, U, V>
      where F: FnOnce(Input<'a, I>, T) -> ParseResult<'a, I, U, V>,
            V: From<E> {
        match self.0 {
            State::Data(i, t) => f(i, t).map_err(From::from),
            State::Error(i, e)   => ParseResult(State::Error(i, From::from(e))),
            State::Incomplete(n) => ParseResult(State::Incomplete(n)),
        }
    }

    /// Sequentially composes the result with a parse action ``f``, discarding any produced value.
    ///
    /// The first parameter to the supplied function ``f`` is the parser state (``Input``). This
    /// state is then passed on to other parsers or used to return a value or an error.
    ///
    /// # Relation to ``bind``
    ///
    /// ```text
    /// ParseResult::then(g)  ≡  ParseResult::bind(|i, _| g(i))
    /// ```
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::{Input, U8Result};
    ///
    /// fn g(i: Input<u8>) -> U8Result<&'static str> {
    ///     i.ret("testing!")
    /// }
    ///
    /// let p1 = Input::new(b"data").ret("initial state");
    /// let p2 = Input::new(b"data").ret("initial state");
    ///
    /// assert_eq!(p1.bind(|i, _| g(i)).unwrap(), "testing!");
    /// assert_eq!(p2.then(g).unwrap(), "testing!");
    /// ```
    #[inline]
    pub fn then<F, U, V = E>(self, f: F) -> ParseResult<'a, I, U, V>
      where F: FnOnce(Input<'a, I>) -> ParseResult<'a, I, U, V>,
            V: From<E> {
        self.bind(|i, _| f(i))
    }

    /// Applies the function `f` on the contained data if the parser is in a success state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::{Input, any};
    ///
    /// let i = Input::new(b"abc");
    ///
    /// let r = any(i).map(|c| c + 12);
    ///
    /// assert_eq!(r.unwrap(), b'm');
    /// ```
    #[inline]
    pub fn map<U, F>(self, f: F) -> ParseResult<'a, I, U, E>
      where F: FnOnce(T) -> U {
        match self.0 {
            State::Data(i, t) => ParseResult(State::Data(i, f(t))),
            State::Error(i, e)   => ParseResult(State::Error(i, e)),
            State::Incomplete(n) => ParseResult(State::Incomplete(n)),
        }
    }

    /// Applies the function `f` on the contained error if the parser is in an error state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::Input;
    ///
    /// let i = Input::new(b"foo");
    ///
    /// let r = i.err::<(), _>("this is")
    ///          .map_err(|e| e.to_owned() + " an error");
    ///
    /// assert_eq!(r.unwrap_err(), "this is an error");
    /// ```
    #[inline]
    pub fn map_err<V, F>(self, f: F) -> ParseResult<'a, I, T, V>
      where F: FnOnce(E) -> V {
        match self.0 {
            State::Data(i, t) => ParseResult(State::Data(i, t)),
            State::Error(i, e)   => ParseResult(State::Error(i, f(e))),
            State::Incomplete(n) => ParseResult(State::Incomplete(n)),
        }
    }

    /// Calls the function `f` with a reference of the contained data if the parser is in a success
    /// state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::{Input, take_while};
    ///
    /// let i = Input::new(b"test and more");
    ///
    /// let r = take_while(i, |c| c != b' ').inspect(|b| {
    ///     println!("{:?}", b); // Prints "test"
    /// });
    /// ```
    #[inline]
    pub fn inspect<F>(self, f: F) -> ParseResult<'a, I, T, E>
      where F: FnOnce(&T) {
        if let State::Data(_, ref t) = self.0 {
             f(t)
        }

        self
    }
}

impl<'a, I, T, E: fmt::Debug> ParseResult<'a, I, T, E> {
    /// Unwraps a parse result, yielding the content of the success-state.
    ///
    /// # Panics
    ///
    /// Panics if the parse result is in an error-state or if the parsing is incomplete. Will
    /// provide a panic message based on the value of the error.
    ///
    /// # Examples
    ///
    /// ```
    /// use chomp::{Input, token};
    ///
    /// let r = token(Input::new(b"a"), b'a');
    ///
    /// assert_eq!(r.unwrap(), b'a');
    /// ```
    ///
    /// ```{.should_panic}
    /// use chomp::{Input, token};
    ///
    /// let r = token(Input::new(b"a"), b'b');
    ///
    /// // Panics with "called `ParseResult::unwrap` on an error: Expected (98)"
    /// assert_eq!(r.unwrap(), b'a');
    /// ```
    ///
    /// ```{.should_panic}
    /// use chomp::{Input, take};
    ///
    /// let r = take(Input::new(b"a"), 2);
    ///
    /// // Panics with "called `ParseResult::unwrap` on an incomplete state (requested 1 tokens)"
    /// assert_eq!(r.unwrap(), b"a");
    /// ```
    #[inline]
    pub fn unwrap(self) -> T {
        match self.0 {
            State::Data(_, t)    => t,
            State::Error(_, e)   => panic!("called `ParseResult::unwrap` on an error: {:?}", e),
            State::Incomplete(n) => panic!(
                "called `ParseResult::unwrap` on an incomplete state (requested {} tokens)",
                n),
        }
    }

    /// Unwraps a parse result, yielding the contents of the success state.
    ///
    /// # Panics
    ///
    /// Panics if the parse result is in an error-state or if the parsing is incomplete. Will
    /// provide a panic message based on the supplied message and the value of the error.
    ///
    /// # Examples
    ///
    /// ```{.should_panic}
    /// use chomp::{Input, token};
    ///
    /// let r = token(Input::new(b"a"), b'b');
    ///
    /// // Panics with "Wanted character b: Expected(98)"
    /// assert_eq!(r.expect("Wanted character b"), b'a');
    /// ```
    #[inline]
    pub fn expect(self, msg: &str) -> T {
        match self.0 {
            State::Data(_, t)    => t,
            State::Error(_, e)   => panic!("{}: {:?}", msg, e),
            State::Incomplete(_) => panic!("{}: Parser in an incomplete state", msg),
        }
    }
}

impl<'a, I, T: fmt::Debug, E> ParseResult<'a, I, T, E> {
    /// Unwraps a parse result, yielding the contents of the error state.
    ///
    /// # Panics
    ///
    /// Panics if the parse result is in a success-state or if the parsing is incomplete. Will
    /// provide a panic message based on the value of the success or incomplete state.
    ///
    #[cfg_attr(feature = "verbose_error", doc = "

 # Examples

 ```
 use chomp::{Error, Input, token};

 let r = token(Input::new(b\"a\"), b'b');

 assert_eq!(r.unwrap_err(), Error::Expected(98));
 ```

 ```{.should_panic}
 use chomp::{Error, Input, token};

 let r = token(Input::new(b\"a\"), b'a');

 // Panics with \"called `ParseResult::unwrap_err` on a success state: 97\"
 assert_eq!(r.unwrap_err(), Error::Expected(98));
 ```
    ")]
    #[inline]
    pub fn unwrap_err(self) -> E {
        match self.0 {
            State::Data(_, t)    => panic!(
                "called `ParseResult::unwrap_err` on a success state: {:?}",
                t),
            State::Error(_, e)   => e,
            State::Incomplete(n) => panic!(
                "called `ParseResult::unwrap_err` on an incomplete state (requested {} tokens)",
                n),
        }
    }
}

/// **Primitive:** Consumes the `ParseResult` and exposes the internal state.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
///
/// # Motivation
///
/// The `ParseResult` type is a semi-linear type, supposed to act like a linear type while used in
/// a parsing context to carry the state. Normally it should be as restrictive as the `Input` type
/// in terms of how much it exposes its internals, but to make it easier to use the parsers
/// `unwrap`, `unwrap_err` and `expect` were introduced which breaks the linearity guarantee when
/// used early.
///
/// The `IntoInner` trait implementation allows fundamental parsers and combinators to expose the
/// inner `State` of the `ParseResult` and act on this.
///
/// # Example
///
/// ```
/// use chomp::{Input, ParseResult, take};
/// use chomp::primitives::{InputClone, IntoInner, State};
///
/// // Version of option() which also catches incomplete
/// fn my_combinator<'a, I, T, E, F>(i: Input<'a, I>, f: F, default: T) -> ParseResult<'a, I, T, E>
///   where F: FnOnce(Input<'a, I>) -> ParseResult<'a, I, T, E> {
///     match f(i.clone()).into_inner() {
///         // Data, preserve the buffer and return
///         State::Data(b, d) => b.ret(d),
///         // Not data, use original buffer and return default
///         _                 => i.ret(default),
///     }
/// }
///
/// let i = Input::new(b"foo");
///
/// let r = my_combinator(i, |i| take(i, 10), &b"test"[..]);
///
/// assert_eq!(r.unwrap(), b"test");
/// ```
impl<'a, I, T, E> IntoInner for ParseResult<'a, I, T, E> {
    type Inner = State<'a, I, T, E>;

    #[inline(always)]
    fn into_inner(self) -> Self::Inner {
        self.0
    }
}

#[cfg(test)]
mod test {
    use input;
    use input::{Input, DEFAULT, END_OF_INPUT};
    use primitives::State;

    use super::ParseResult;

    #[test]
    fn monad_left_identity() {
        fn f<I: Copy>(i: Input<I>, n: u32) -> ParseResult<I, u32, ()> {
            i.ret(n + 1)
        }

        let m1 = input::new(END_OF_INPUT, b"test");
        let m2 = input::new(END_OF_INPUT, b"test");

        let a = 123;
        // return a >>= f
        let lhs = m1.ret(a).bind(f);
        // f a
        let rhs = f(m2, a);

        assert_eq!(lhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 124));
        assert_eq!(rhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 124));
    }

    #[test]
    fn monad_right_identity() {
        let m1 = input::new(END_OF_INPUT, b"test").ret::<_, ()>(1);
        let m2 = input::new(END_OF_INPUT, b"test").ret::<_, ()>(1);

        // m1 >>= ret === m2
        let lhs = m1.bind::<_, _, ()>(Input::ret);
        let rhs = m2;

        assert_eq!(lhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 1));
        assert_eq!(rhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 1));
    }

    #[test]
    fn monad_associativity() {
         fn f<I: Copy>(i: Input<I>, num: u32) -> ParseResult<I, u64, ()> {
            i.ret((num + 1) as u64)
        }

        fn g<I: Copy>(i: Input<I>, num: u64) -> ParseResult<I, u64, ()> {
            i.ret(num * 2)
        }

        let lhs_m = input::new(END_OF_INPUT, b"test").ret::<_, ()>(2);
        let rhs_m = input::new(END_OF_INPUT, b"test").ret::<_, ()>(2);

        // (m >>= f) >>= g
        let lhs = lhs_m.bind(f).bind(g);
        // m >>= (\x -> f x >>= g)
        let rhs = rhs_m.bind(|i, x| f(i, x).bind(g));

        assert_eq!(lhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 6));
        assert_eq!(rhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 6));
    }

    #[test]
    fn parse_result_inspect() {
        use primitives::IntoInner;

        let mut n1 = 0;
        let mut n2 = 0;
        let i1     = input::new(DEFAULT, b"test ").ret::<u32, ()>(23);
        let i2     = input::new(END_OF_INPUT, b"test ").ret::<u32, ()>(23);

        let r1 = i1.inspect(|d: &u32| {
            assert_eq!(d, &23);

            n1 += 1;
        });
        let r2 = i2.inspect(|d: &u32| {
            assert_eq!(d, &23);

            n2 += 1;
        });

        assert_eq!(r1.into_inner(), State::Data(input::new(DEFAULT, b"test "), 23));
        assert_eq!(n1, 1);
        assert_eq!(r2.into_inner(), State::Data(input::new(END_OF_INPUT, b"test "), 23));
        assert_eq!(n2, 1);
    }

    #[test]
    fn input_propagation() {
        let mut n1_calls = 0;
        let mut n2_calls = 0;

        let i1 = input::new(DEFAULT, b"test1").ret::<_, ()>(23);
        let i2 = input::new(END_OF_INPUT, b"test2").ret::<_, ()>(24);

        let r1: ParseResult<_, _, ()> = i1.bind(|i, t| { n1_calls += 1; i.ret(t) });
        let r2: ParseResult<_, _, ()> = i2.bind(|i, t| { n2_calls += 1; i.ret(t) });

        assert_eq!(r1.0, State::Data(input::new(DEFAULT, b"test1"), 23));
        assert_eq!(r2.0, State::Data(input::new(END_OF_INPUT, b"test2"), 24));
        assert_eq!(n1_calls, 1);
        assert_eq!(n2_calls, 1);
    }

    #[test]
    fn error_propagation() {
        let mut n1_calls = 0;
        let mut n2_calls = 0;

        let i1 = input::new(DEFAULT, b"test1").err::<(), _>(23);
        let i2 = input::new(END_OF_INPUT, b"test2").err::<(), _>(24);

        let r1 = i1.bind(|i, t| { n1_calls += 1; i.ret(t) });
        let r2 = i2.bind(|i, t| { n2_calls += 1; i.ret(t) });

        assert_eq!(r1.0, State::Error(b"test1", 23));
        assert_eq!(r2.0, State::Error(b"test2", 24));
        assert_eq!(n1_calls, 0);
        assert_eq!(n2_calls, 0);
    }

    #[test]
    fn incomplete_propagation() {
        let mut n1_calls = 0;
        let mut n2_calls = 0;

        let i1 = input::new(DEFAULT, b"test1").incomplete::<(), ()>(23);
        let i2 = input::new(END_OF_INPUT, b"test2").incomplete::<(), ()>(24);

        let r1: ParseResult<_, _, ()> = i1.bind(|i, t| { n1_calls += 1; i.ret(t) });
        let r2: ParseResult<_, _, ()> = i2.bind(|i, t| { n2_calls += 1; i.ret(t) });

        assert_eq!(r1.0, State::Incomplete(23));
        assert_eq!(r2.0, State::Incomplete(24));
        assert_eq!(n1_calls, 0);
        assert_eq!(n2_calls, 0);
    }
}
