use input::Input;
use parse_result::ParseResult;

    // Applies the function in the parser to the argument produced by `rhs`, returning the result
    // of the function.
    //
    // # Automatic conversion of ``E``
    //
    // The error value ``E`` will automatically be converted using the ``From`` trait to the
    // desired type. The downside with this using the current stable version of Rust (1.4) is that
    // the type inferrence will currently not use the default value for the generic ``V`` and will
    // therefore require extra type hint for the error.
    //
    // # Examples
    //
    // ```
    // use chomp::Input;
    // use chomp::ascii::decimal;
    //
    // fn square(n: u32) -> u32 {
    //     n * n
    // }
    //
    // let i = Input::new(b"3 test");
    //
    // // parse a decimal number and apply the square function
    // let r = i.ret(square).apply(decimal);
    //
    // assert_eq!(r.unwrap(), 9);
    // ```
    // The below code has the issue that it cannot allow inference of the closures because it is
    // using two traits (type of `apply.rhs` -> ApplyArgs -> FnOnce -> Concrete closure), which
    // will make it impossible to infer the type of the closure since there are a potentially
    // infinite implementations of ApplyArgs which can be satisfied by the closure.
    //
    // Using functions or type-annotations on both parameter and return types will make it work
    // properly:
    //
    // ```
    // i.ret(|x| 2 * x).apply(|i: Input<_>| -> ParseResult<_, _, _> string(i, b"foobar"))
    // ```
    // #[inline]
    // pub fn apply<Args>(self, rhs: Args) -> ParseResult<'a, I, Args::Return, Args::Error>
    //   where Args:        ApplyArgs<'a, I, T> + 'a,
    //         Args::Error: From<E> {
    //     self.bind(|i, f| rhs.apply(i, f))
    // }

    // This is an attempt to stack up a tuple T -> (T, U) -> (T, U, V) and then invoking a supplied
    // closure with |T, U, V| once the parsers for the individual values have been run. Essentially
    // reversing the order of the Applicative operations in Haskell.
    //
    // We have issues with the general form of trying to use a generic over `T`, `(T,)`, `(T, U)`,
    // `(T, U, V)` and so on since the implementation of a trait over T.
    //
    // Once we have a `(T,)` in the ParseResult we can continue to construct the tuple-list of
    // values, the issue here is that the `Input + ParseResult` is no longer an applicative at all
    // times it is a monad. Generally `T => Applicative for all T: T => Monad` which is not true in
    // this case.
    //
    // Was suggested that an initial `ap` method on `Input` can solve the syntactic issues:
    //
    // ```
    // struct IP(u8, u8, u8, u8);
    //
    // fn dot(i: Input<u8>) -> U8Result<u8> {
    //     token(i, b'.')
    // }
    //
    // let ip = i.ap(digit).skip(dot).ap(digit).skip(dot).ap(digit).skip(dot).ap(digit).apply(IP);
    // ```
    //
    // Technically `apply` in the code-example above is a special version of `map`, where the
    // parameters are lifted out of the tuple and passed as parameters to the supplied function.
    //#[inline]
    //pub fn ap<F, U, V = E>(self, f: F) -> ParseResult<'a, I, T::Result, V>
    //  where F: FnOnce(Input<'a, I>) -> ParseResult<'a, I, U, V>,
    //        V: From<E>,
    //        U: 'a,
    //        T: TupleCons<U> {
    //    self.bind(|i, t| f(i).map(|u| t.cons(u)))
    //}

/// Runs a monadic action on a container grouping its result with the existing contained results in
/// a tuple.
pub trait Ap<'a, ToMerge: 'a, Error> {
    type Input;
    type Merged;

    fn ap<F>(self, f: F) -> ParseResult<'a, Self::Input, Self::Merged, Error>
      where F: FnOnce(Input<'a, Self::Input>) -> ParseResult<'a, Self::Input, ToMerge, Error>;
}

/// Trait for running a function on a contained tuple.
pub trait Apply<'a, ApplyFn, Error> {
    type Input;
    type Result;

    fn apply(self, ApplyFn) -> ParseResult<'a, Self::Input, Self::Result, Error>;
}

pub trait Applicative<'a, ApplyFn, ToMerge: 'a, Error>: Ap<'a, ToMerge, Error> + Apply<'a, ApplyFn, Error> {}

impl<'a, I, F, T, E> Apply<'a, F, E> for Input<'a, I>
  where F: FnOnce() -> T {
    type Input  = I;
    type Result = T;

    fn apply(self, f: F) -> ParseResult<'a, Self::Input, Self::Result, E> {
        self.ret(f())
    }
}

impl<'a, I, T: 'a, E> Ap<'a, T, E> for Input<'a, I> {
    type Input  = I;
    type Merged = (T,);

    fn ap<F>(self, f: F) -> ParseResult<'a, Self::Input, Self::Merged, E>
      where F: FnOnce(Input<'a, Self::Input>) -> ParseResult<'a, Self::Input, T, E> {
        f(self).map(|t| (t,))
    }
}

impl<'a, I, T: 'a, E, ApplyFn> Applicative<'a, ApplyFn, T, E> for Input<'a, I>
  where ApplyFn: FnOnce() -> T {}

macro_rules! impl_applicative {
    ($($r:ident),+) => {
        impl<'a, In, FunctionReturn, Error, $($r),+>
            Ap<'a, FunctionReturn, Error> for
                ParseResult<'a, In, ($($r),+ ,), Error>
          where FunctionReturn: 'a, $($r : 'a),+ {
            type Input  = In;
            type Merged = ($($r),+ , FunctionReturn);

            #[allow(non_snake_case)]
            fn ap<ApFn>(self, f: ApFn) -> ParseResult<'a, Self::Input, Self::Merged, Error>
              where ApFn: FnOnce(Input<'a, Self::Input>) -> ParseResult<'a, Self::Input, FunctionReturn, Error> {
                self.bind(|input, tuple| f(input).map(move |extra| {
                    let ($($r),+ ,) = tuple;

                    ($($r),+ , extra)
                }))
            }
        }

        impl<'a, Input, Error, ApplyFn, FunctionReturn, $($r),+>
            Apply<'a, ApplyFn, Error> for
                ParseResult<'a, Input, ($($r),+ ,), Error>
          where ApplyFn: FnOnce($($r),+) -> FunctionReturn {
            type Input  = Input;
            type Result = FunctionReturn;

            #[allow(non_snake_case)]
            fn apply(self, f: ApplyFn) -> ParseResult<'a, Self::Input, Self::Result, Error> {
                self.map(|inner| {
                    let ($($r),+ ,) = inner;

                    f($($r),+)
                })
            }
        }

        impl<'a, In, ApplyFn, FunctionReturn, Error, $($r),+> Applicative<'a, ApplyFn, FunctionReturn, Error> for ParseResult<'a, In, ($($r),+ ,), Error>
          where ApplyFn: FnOnce($($r),+) -> FunctionReturn,
                FunctionReturn: 'a,
                $($r : 'a),+ {}
    };
}

impl_applicative!{A}
impl_applicative!{A, B}
impl_applicative!{A, B, C}
impl_applicative!{A, B, C, D}
impl_applicative!{A, B, C, D, E}
impl_applicative!{A, B, C, D, E, F}
impl_applicative!{A, B, C, D, E, F, G}
impl_applicative!{A, B, C, D, E, F, G, H}
impl_applicative!{A, B, C, D, E, F, G, H, I}
impl_applicative!{A, B, C, D, E, F, G, H, I, J}
impl_applicative!{A, B, C, D, E, F, G, H, I, J, K}
impl_applicative!{A, B, C, D, E, F, G, H, I, J, K, L}
impl_applicative!{A, B, C, D, E, F, G, H, I, J, K, L, M}

#[cfg(test)]
mod test {
    use {Input, ParseResult};
    use primitives::input::*;
    use primitives::{IntoInner, State};
    use super::*;

    #[test]
    fn ap_test() {
        let m = new(END_OF_INPUT, b"test");

        fn f<I: Copy>(i: Input<I>) -> ParseResult<I, u64, ()> {
            i.ret(123)
        }

        assert_eq!(m.ap(f).ap(f).into_inner(), State::Data(new(END_OF_INPUT, b"test"), (123, 123)));
    }

    #[test]
    fn applicative_identity() {
        fn f<I: Copy>(i: Input<I>) -> ParseResult<I, u64, ()> {
            i.ret(123)
        }

        let lhs_m = input::new(END_OF_INPUT, b"test");
        let rhs_m = input::new(END_OF_INPUT, b"test");

        // pure id <*> v
        let lhs = lhs_m.ap(f).apply(|x| x); // let lhs = lhs_m.ret(|x| x).apply(f);
        // v
        let rhs = f(rhs_m);

        assert_eq!(lhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 123));
        assert_eq!(rhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 123));
    }

    // We need FnBox here to be able to run this test
    #[cfg(all(test, feature = "unstable"))]
    #[test]
    fn applicative_composition() {
        use std::boxed::FnBox;

        let lhs_m = input::new(END_OF_INPUT, b"test");
        let rhs_m = input::new(END_OF_INPUT, b"test");

        // compose :: (c -> b) -> (a -> b) -> (a -> c)
        // curried version of compose
        fn compose<'a, F, G, A, B, C>(f: F) -> Box<FnBox(G) -> Box<FnBox(A) -> C + 'a> + 'a>
          where F: FnOnce(B) -> C + 'a,
                G: FnOnce(A) -> B + 'a {
            Box::new(move |g: G| -> Box<FnBox(A) -> C + 'a> {
                Box::new(move |x: A| -> C { f(g(x)) })
            })
        };

        // u :: Parser (u32 -> i32)
        fn u<I: Copy>(i: Input<I>) -> ParseResult<I, Box<FnBox(u32) -> i32>, ()> {
            i.ret(Box::new(|x| (x + 3) as i32))
        }
        // v :: Parser (u8 -> u32)
        fn v<I: Copy>(i: Input<I>) -> ParseResult<I, Box<FnBox(u8) -> u32>, ()> {
            i.ret(Box::new(|x| (x * 2) as u32))
        }
        // w :: Parser u8
        fn w<I: Copy>(i: Input<I>) -> ParseResult<I, u8, ()> {
            i.ret(2)
        }

        // pure (.) <*> u <*> v <*> w
        let lhs: ParseResult<_, _, ()> = lhs_m.ret(compose).apply(u).apply(v).apply(w);
        // u <*> (v <*> w)
        let rhs: ParseResult<_, _, ()> = u(rhs_m).apply(|i| v(i).apply(w));

        assert_eq!(lhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 7i32));
        assert_eq!(rhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 7i32));
    }

    #[test]
    fn applicative_homomorphism() {
        let lhs_m = input::new(END_OF_INPUT, b"test");
        let rhs_m = input::new(END_OF_INPUT, b"test");

        fn f(n: u32) -> i32 {
            (n * 2) as i32
        }

        let x = 3;

        // pure f <*> pure x

        // Line below does not manage to figure out what `i` is, if type annotated that it is an
        // Input it is fine
        //let lhs: ParseResult<_, _, ()> = lhs_m.ret(f).apply(|i| i.ret(x));
        //let lhs: ParseResult<_, _, ()> = lhs_m.ret(f).apply(|i: Input<_>| -> ParseResult<_, _, _> {i.ret(x)});
        let lhs: ParseResult<_, _, ()> = lhs_m.ret(f).apply(|i| Input::ret(i, x));
        // pure (f x)
        let rhs: ParseResult<_, _, ()> = rhs_m.ret(f(x));

        assert_eq!(lhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 6i32));
        assert_eq!(rhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 6i32));
    }

    // We need FnBox here to be able to run this test
    #[cfg(all(test, feature = "unstable"))]
    #[test]
    fn applicative_interchange() {
        use std::boxed::FnBox;

        let lhs_m = input::new(END_OF_INPUT, b"test");
        let rhs_m = input::new(END_OF_INPUT, b"test");

        let y = 3u32;

        // u :: Parser (u32 -> i32)
        fn u<I: Copy>(i: Input<I>) -> ParseResult<I, Box<FnBox(u32) -> i32>, ()> {
            i.ret(Box::new(|x| (x + 4) as i32))
        }

        // $ :: (a -> b) -> a -> b
        // we're interested in the form ($ x) which is of type :: b -> (a -> b) -> b
        fn apply_arg<'a, A, B, F>(a: A) -> Box<FnBox(F) -> B + 'a>
          where A: 'a,
                F: FnOnce(A) -> B {
            Box::new(move |f: F| f(a))
        }

        // u <*> pure y
        let lhs: ParseResult<_, _, ()> = u(lhs_m).apply(|i| i.ret(y));
        // pure ($ y) <*> u
        let rhs: ParseResult<_, _, ()> = rhs_m.ret(apply_arg(y)).apply(u);

        assert_eq!(lhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 7i32));
        assert_eq!(rhs.0, State::Data(input::new(END_OF_INPUT, b"test"), 7i32));
    }
}
