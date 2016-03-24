use types::Input;
use primitives::{IntoInner, State};

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
pub struct ParseResult<I: Input, T, E>(State<I, T, E>);

/// **Primitive:** Creates a new `ParseResult`.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
///
/// # Note
///
/// Prefer to use ``Input::ret``, ``Input::err`` or ``Input::incomplete`` instead of using
pub fn new<I: Input, T, E>(s: State<I, T, E>) -> ParseResult<I, T, E> {
    ParseResult(s)
}

impl<I: Input, T, E> ParseResult<I, T, E> {
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
    /// use chomp::parse_only;
    ///
    /// let r = parse_only(|i| {
    ///         i.ret("data".to_owned())
    ///         // Explicitly state the error type
    ///          .bind::<_, _, ()>(|i, x| i.ret(x + " here!"))
    ///     },
    ///     b"test");
    ///
    /// assert_eq!(r, Ok("data here!".to_owned()));
    /// ```
    ///
    /// Wrapping the expression in a function will both make it easier to compose and also provides
    /// the type-hint for the error in the function signature:
    ///
    /// ```
    /// use chomp::{Input, ParseResult, parse_only};
    ///
    /// fn parser(i: Input<u8>, n: i32) -> ParseResult<u8, i32, ()> {
    ///     i.ret(n + 10)
    /// }
    ///
    /// let r = parse_only(|i| i.ret(23).bind(parser), b"test");
    ///
    /// assert_eq!(r, Ok(33));
    /// ```
    #[inline]
    pub fn bind<F, U, V>(self, f: F) -> ParseResult<I, U, V>
      where F: FnOnce(I, T) -> ParseResult<I, U, V>,
            V: From<E> {
        match self.0 {
            State::Data(i, t)       => f(i, t).map_err(From::from),
            State::Error(i, e)      => ParseResult(State::Error(i, From::from(e))),
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
    /// use chomp::{Input, U8Result, parse_only};
    ///
    /// fn g(i: Input<u8>) -> U8Result<&'static str> {
    ///     i.ret("testing!")
    /// }
    ///
    /// let r1 = parse_only(|i| i.ret("initial state").bind(|i, _| g(i)), b"data");
    /// let r2 = parse_only(|i| i.ret("initial state").then(g), b"data");
    ///
    /// assert_eq!(r1, Ok("testing!"));
    /// assert_eq!(r2, Ok("testing!"));
    /// ```
    #[inline]
    pub fn then<F, U, V>(self, f: F) -> ParseResult<I, U, V>
      where F: FnOnce(I) -> ParseResult<I, U, V>,
            V: From<E> {
        self.bind(|i, _| f(i))
    }

    /// Applies the function `f` on the contained data if the parser is in a success state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::{parse_only, any};
    ///
    /// let r = parse_only(|i| any(i).map(|c| c + 12), b"abc");
    ///
    /// assert_eq!(r, Ok(b'm'));
    /// ```
    #[inline]
    pub fn map<U, F>(self, f: F) -> ParseResult<I, U, E>
      where F: FnOnce(T) -> U {
        match self.0 {
            State::Data(i, t)       => ParseResult(State::Data(i, f(t))),
            State::Error(i, e)      => ParseResult(State::Error(i, e)),
        }
    }

    /// Applies the function `f` on the contained error if the parser is in an error state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::{ParseError, parse_only};
    ///
    /// let r = parse_only(|i| i.err::<(), _>("this is")
    ///          .map_err(|e| e.to_owned() + " an error"),
    ///          b"foo");
    ///
    /// assert_eq!(r, Err(ParseError::Error(b"foo", "this is an error".to_owned())));
    /// ```
    #[inline]
    pub fn map_err<V, F>(self, f: F) -> ParseResult<I, T, V>
      where F: FnOnce(E) -> V {
        match self.0 {
            State::Data(i, t)       => ParseResult(State::Data(i, t)),
            State::Error(i, e)      => ParseResult(State::Error(i, f(e))),
        }
    }

    /// Calls the function `f` with a reference of the contained data if the parser is in a success
    /// state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::{parse_only, take_while};
    ///
    /// let r = parse_only(|i| take_while(i, |c| c != b' ').inspect(|b| {
    ///     println!("{:?}", b); // Prints "test"
    /// }), b"test and more");
    ///
    /// assert_eq!(r, Ok(&b"test"[..]));
    /// ```
    #[inline]
    pub fn inspect<F>(self, f: F) -> ParseResult<I, T, E>
      where F: FnOnce(&T) {
        if let State::Data(_, ref t) = self.0 {
             f(t)
        }

        self
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
/// in terms of how much it exposes its internals, but the `IntoInner` trait implementation
/// allows fundamental parsers and combinators to expose the inner `State` of the `ParseResult`
/// and act on this.
///
/// # Example
///
/// ```
/// use chomp::{Input, ParseResult, parse_only, take};
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
/// let r = parse_only(|i| my_combinator(i, |i| take(i, 10), &b"test"[..]), b"foo");
///
/// assert_eq!(r, Ok(&b"test"[..]));
/// ```
impl<I: Input, T, E> IntoInner for ParseResult<I, T, E> {
    type Inner = State<I, T, E>;

    #[inline(always)]
    fn into_inner(self) -> Self::Inner {
        self.0
    }
}

/*
#[cfg(test)]
mod test {
    use input;
    use input::{Input, DEFAULT, END_OF_INPUT};
    use primitives::State;

    use super::ParseResult;

    #[test]
    fn monad_left_identity() {
        fn f<I: Input>(i: I, n: u32) -> ParseResult<I, u32, ()> {
            i.ret(n + 1)
        }

        let m1 = input::new_buf(END_OF_INPUT, b"test");
        let m2 = input::new_buf(END_OF_INPUT, b"test");

        let a = 123;
        // return a >>= f
        let lhs = m1.ret(a).bind(f);
        // f a
        let rhs = f(m2, a);

        assert_eq!(lhs.0, State::Data(input::new_buf(END_OF_INPUT, b"test"), 124));
        assert_eq!(rhs.0, State::Data(input::new_buf(END_OF_INPUT, b"test"), 124));
    }

    #[test]
    fn monad_right_identity() {
        let m1 = input::new_buf(END_OF_INPUT, b"test").ret::<_, ()>(1);
        let m2 = input::new_buf(END_OF_INPUT, b"test").ret::<_, ()>(1);

        // m1 >>= ret === m2
        let lhs = m1.bind::<_, _, ()>(Input::ret);
        let rhs = m2;

        assert_eq!(lhs.0, State::Data(input::new_buf(END_OF_INPUT, b"test"), 1));
        assert_eq!(rhs.0, State::Data(input::new_buf(END_OF_INPUT, b"test"), 1));
    }

    #[test]
    fn monad_associativity() {
         fn f<I: Input>(i: I, num: u32) -> ParseResult<I, u64, ()> {
            i.ret((num + 1) as u64)
        }

        fn g<I: Input>(i: I, num: u64) -> ParseResult<I, u64, ()> {
            i.ret(num * 2)
        }

        let lhs_m = input::new_buf(END_OF_INPUT, b"test").ret::<_, ()>(2);
        let rhs_m = input::new_buf(END_OF_INPUT, b"test").ret::<_, ()>(2);

        // (m >>= f) >>= g
        let lhs = lhs_m.bind(f).bind(g);
        // m >>= (\x -> f x >>= g)
        let rhs = rhs_m.bind(|i, x| f(i, x).bind(g));

        assert_eq!(lhs.0, State::Data(input::new_buf(END_OF_INPUT, b"test"), 6));
        assert_eq!(rhs.0, State::Data(input::new_buf(END_OF_INPUT, b"test"), 6));
    }

    #[test]
    fn parse_result_inspect() {
        use primitives::IntoInner;

        let mut n1 = 0;
        let mut n2 = 0;
        let i1     = input::new_buf(DEFAULT, b"test ").ret::<u32, ()>(23);
        let i2     = input::new_buf(END_OF_INPUT, b"test ").ret::<u32, ()>(23);

        let r1 = i1.inspect(|d: &u32| {
            assert_eq!(d, &23);

            n1 += 1;
        });
        let r2 = i2.inspect(|d: &u32| {
            assert_eq!(d, &23);

            n2 += 1;
        });

        assert_eq!(r1.into_inner(), State::Data(input::new_buf(DEFAULT, b"test "), 23));
        assert_eq!(n1, 1);
        assert_eq!(r2.into_inner(), State::Data(input::new_buf(END_OF_INPUT, b"test "), 23));
        assert_eq!(n2, 1);
    }

    #[test]
    fn input_propagation() {
        let mut n1_calls = 0;
        let mut n2_calls = 0;

        let i1 = input::new_buf(DEFAULT, b"test1").ret::<_, ()>(23);
        let i2 = input::new_buf(END_OF_INPUT, b"test2").ret::<_, ()>(24);

        let r1: ParseResult<_, _, ()> = i1.bind(|i, t| { n1_calls += 1; i.ret(t) });
        let r2: ParseResult<_, _, ()> = i2.bind(|i, t| { n2_calls += 1; i.ret(t) });

        assert_eq!(r1.0, State::Data(input::new_buf(DEFAULT, b"test1"), 23));
        assert_eq!(r2.0, State::Data(input::new_buf(END_OF_INPUT, b"test2"), 24));
        assert_eq!(n1_calls, 1);
        assert_eq!(n2_calls, 1);
    }

    #[test]
    fn error_propagation() {
        let mut n1_calls = 0;
        let mut n2_calls = 0;

        let i1 = input::new_buf(DEFAULT, b"test1").err::<(), _>(23);
        let i2 = input::new_buf(END_OF_INPUT, b"test2").err::<(), _>(24);

        let r1 = i1.bind(|i, t| { n1_calls += 1; i.ret(t) });
        let r2 = i2.bind(|i, t| { n2_calls += 1; i.ret(t) });

        assert_eq!(r1.0, State::Error(input::new_buf(DEFAULT, b"test1"), 23));
        assert_eq!(r2.0, State::Error(input::new_buf(END_OF_INPUT, b"test2"), 24));
        assert_eq!(n1_calls, 0);
        assert_eq!(n2_calls, 0);
    }

    #[test]
    fn slice() {
        fn f<I: Input>(i: I, n: u32) -> ParseResult<I, u32, ()> { i.ret(n + 1) }

        let lhs = (&b"test"[..]).ret(123).bind(f);
        let rhs = f(&b"test"[..], 123);

        assert_eq!(lhs.0, State::Data(&b"test"[..], 124));
        assert_eq!(rhs.0, State::Data(&b"test"[..], 124));
    }
}
*/
