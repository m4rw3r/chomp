use input::Input;
use parse_result::ParseResult;

/*
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
*/

pub trait Applicative<'a, ApplyFn, ToMerge: 'a, Error> {
    type Input;
    type Result;
    type Merged;

    fn ap<F>(self, f: F) -> ParseResult<'a, Self::Input, Self::Merged, Error>
      where F: FnOnce(Input<'a, Self::Input>) -> ParseResult<'a, Self::Input, ToMerge, Error>;

    fn apply(self, ApplyFn) -> ParseResult<'a, Self::Input, Self::Result, Error>;
}

impl<'a, I, T: 'a, E, ApplyFn = fn() -> T> Applicative<'a, ApplyFn, T, E> for Input<'a, I>
  where ApplyFn: FnOnce() -> T {
    type Input  = I;
    type Result = T;
    type Merged = (T,);

    fn apply(self, f: ApplyFn) -> ParseResult<'a, Self::Input, Self::Result, E> {
        self.ret(f())
    }

    fn ap<F>(self, f: F) -> ParseResult<'a, Self::Input, Self::Merged, E>
      where F: FnOnce(Input<'a, Self::Input>) -> ParseResult<'a, Self::Input, T, E> {
        f(self).map(|t| (t,))
    }
}

macro_rules! impl_applicative {
    ($($r:ident),+) => {
        /*
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
        */

        impl<'a, In, FunctionReturn, Error, $($r),+, ApplyFn = fn($($r),+) -> FunctionReturn> Applicative<'a, ApplyFn, FunctionReturn, Error> for ParseResult<'a, In, ($($r),+ ,), Error>
          where ApplyFn: FnOnce($($r),+) -> FunctionReturn,
                FunctionReturn: 'a,
                $($r : 'a),+ {

            type Input  = In;
            type Result = FunctionReturn;
            type Merged = ($($r),+ , FunctionReturn);

            #[allow(non_snake_case)]
            fn ap<ApFn>(self, f: ApFn) -> ParseResult<'a, Self::Input, Self::Merged, Error>
              where ApFn: FnOnce(Input<'a, Self::Input>) -> ParseResult<'a, Self::Input, FunctionReturn, Error> {
                self.bind(|input, tuple| f(input).map(move |extra| {
                    let ($($r),+ ,) = tuple;

                    ($($r),+ , extra)
                }))
            }

            #[allow(non_snake_case)]
            fn apply(self, f: ApplyFn) -> ParseResult<'a, Self::Input, Self::Result, Error> {
                self.map(|inner| {
                    let ($($r),+ ,) = inner;

                    f($($r),+)
                })
            }
        }
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
}
