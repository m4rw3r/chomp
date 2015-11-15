use ::{ParseResult, Error};

pub type U8Result<'a, T>        = ParseResult<'a, u8, T, Error<u8>>;
pub type SimpleResult<'a, I, T> = ParseResult<'a, I, T, Error<I>>;
