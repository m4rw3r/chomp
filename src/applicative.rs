use input::Input;
use parse_result::ParseResult;

pub trait TupleCons<U> {
    type Result;

    fn cons(self, U) -> Self::Result;
}

macro_rules! impl_tuple_cons {
    ( $($t:ident),+ : $n:ident ) => {
        impl<$($t),+ , $n> TupleCons<$n> for ($($t),+,) {
            type Result = ($($t),+ , $n);

            #[allow(non_snake_case)]
            fn cons(self, $n: $n) -> Self::Result {
                let ($($t),+ , ) = self;

                ($($t),+ , $n)
            }
        }
    };
}

impl_tuple_cons!{A: B}
impl_tuple_cons!{A, B: C}
impl_tuple_cons!{A, B, C: D}
impl_tuple_cons!{A, B, C, D: E}
impl_tuple_cons!{A, B, C, D, E: F}
impl_tuple_cons!{A, B, C, D, E, F: G}
impl_tuple_cons!{A, B, C, D, E, F, G: H}
impl_tuple_cons!{A, B, C, D, E, F, G, H: I}
impl_tuple_cons!{A, B, C, D, E, F, G, H, I: J}
impl_tuple_cons!{A, B, C, D, E, F, G, H, I, J: K}
impl_tuple_cons!{A, B, C, D, E, F, G, H, I, J, K: L}
impl_tuple_cons!{A, B, C, D, E, F, G, H, I, J, K, L: M}
impl_tuple_cons!{A, B, C, D, E, F, G, H, I, J, K, L, M: N}

pub trait Applicative<'a, T, E> {
    type Input;
    type Merged;

    fn ap<F>(self, f: F) -> ParseResult<'a, Self::Input, Self::Merged, E>
      where T: 'a,
            F: FnOnce(Input<'a, Self::Input>) -> ParseResult<'a, Self::Input, T, E>;
}

pub trait ApplicativeApply<'a, F> {
    type Input;
    type Error;
    type Result;

    fn apply(self, f: F) -> ParseResult<'a, Self::Input, Self::Result, Self::Error>;
}

macro_rules! impl_applicative_apply {
    ($($r:ident),+) => {
        impl<'a, Input, Error, Function, FunctionReturn, $($r),+>
            ApplicativeApply<'a, Function> for
                ParseResult<'a, Input, ($($r),+ ,), Error>
          where Function: FnOnce($($r),+) -> FunctionReturn {
            type Input  = Input;
            type Error  = Error;
            type Result = FunctionReturn;

            #[allow(non_snake_case)]
            fn apply(self, f: Function) -> ParseResult<'a, Self::Input, Self::Result, Self::Error> {
                self.map(|inner| {
                    let ($($r),+ ,) = inner;

                    f($($r),+)
                })
            }
        }
    };
}

impl_applicative_apply!{A}
impl_applicative_apply!{A, B}
impl_applicative_apply!{A, B, C}
impl_applicative_apply!{A, B, C, D}
impl_applicative_apply!{A, B, C, D, E}
impl_applicative_apply!{A, B, C, D, E, F}
impl_applicative_apply!{A, B, C, D, E, F, G}
impl_applicative_apply!{A, B, C, D, E, F, G, H}
impl_applicative_apply!{A, B, C, D, E, F, G, H, I}
impl_applicative_apply!{A, B, C, D, E, F, G, H, I, J}
impl_applicative_apply!{A, B, C, D, E, F, G, H, I, K, L}
impl_applicative_apply!{A, B, C, D, E, F, G, H, I, J, K, L}
impl_applicative_apply!{A, B, C, D, E, F, G, H, I, J, K, L, M}
impl_applicative_apply!{A, B, C, D, E, F, G, H, I, J, K, L, M, N}

impl<'a, I, T: 'a, E> Applicative<'a, T, E> for Input<'a, I> {
    type Input  = I;
    type Merged = (T,);

    fn ap<F>(self, f: F) -> ParseResult<'a, Self::Input, Self::Merged, E>
      where F: FnOnce(Input<'a, Self::Input>) -> ParseResult<'a, Self::Input, T, E> {
        f(self).map(|t| (t,))
    }
}

impl<'a, I, T, E, U, V> Applicative<'a, U, V> for ParseResult<'a, I, T, E>
  where T: TupleCons<U> + 'a,
        U: 'a,
        V: From<E> {
    type Input  = I;
    type Merged = T::Result;

    fn ap<F>(self, f: F) -> ParseResult<'a, Self::Input, Self::Merged, V>
      where F: FnOnce(Input<'a, Self::Input>) -> ParseResult<'a, Self::Input, U, V> {
        self.bind(|i, t| f(i).map(|u| t.cons(u)))
    }
}

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
