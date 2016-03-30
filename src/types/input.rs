use types::{Buffer, Input};
use primitives::Guard;

impl<'a, I: Copy + PartialEq> Buffer for &'a [I] {
    type Token = I;

    fn fold<B, F>(self, init: B, f: F) -> B
      where F: FnMut(B, Self::Token) -> B {
        (&self[..]).iter().cloned().fold(init, f)
    }

    fn len(&self) -> usize {
        // Slice to reach inherent method to prevent infinite recursion
        (&self[..]).len()
    }

    fn to_vec(self) -> Vec<Self::Token> {
        (&self[..]).iter().cloned().collect()
    }
}

impl<'a> Buffer for &'a str {
    type Token = char;

    fn fold<B, F>(self, init: B, f: F) -> B
      where F: FnMut(B, Self::Token) -> B {
        self.chars().fold(init, f)
    }

    fn len(&self) -> usize {
        self.chars().count()
    }

    fn is_empty(&self) -> bool {
        (&self[..]).is_empty()
    }

    fn to_vec(self) -> Vec<Self::Token> {
        (&self[..]).chars().collect()
    }
}

impl<'a, I: Copy + PartialEq> Input for &'a [I] {
    type Token  = I;
    type Marker = &'a [I];
    type Buffer = &'a [I];

    #[inline]
    fn _peek(&mut self, _g: Guard) -> Option<Self::Token> {
        self.first().cloned()
    }

    #[inline]
    fn _pop(&mut self, _g: Guard) -> Option<Self::Token> {
        self.first().cloned().map(|c| {
            *self = &self[1..];

            c
        })
    }

    #[inline]
    fn _consume(&mut self, _g: Guard, n: usize) -> Option<Self::Buffer> {
        if n > self.len() {
            None
        } else {
            let b = &self[..n];

            *self = &self[n..];

            Some(b)
        }
    }

    #[inline]
    fn _consume_while<F>(&mut self, _g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        match self.iter().position(|c| !f(*c)) {
            Some(n) => {
                let b = &self[..n];

                *self = &self[n..];

                b
            },
            None => {
                let b = &self[..];

                *self = &self[..0];

                b
            }
        }
    }

    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.len()]
    }

    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        let b = &self[..];

        *self = &self[..0];

        b
    }

    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        &self
    }

    #[inline]
    fn _restore(self, _g: Guard, m: Self::Marker) -> Self {
        m
    }
}

// FIXME: Docs
/// Input buffer type which contains a flag which tells if we might have more data to read.
// TODO: Move to buffer module and make public?
// TODO: Replace mode with boolean
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct InputBuf<'a, I: 'a>(
    /// If this is set to true a parser has tried to read past the end of this buffer.
    pub bool,
    /// Current buffer slice
    pub &'a [I],
);

// FIXME: Docs
impl<'a, I: 'a> InputBuf<'a, I> {
    #[inline]
    pub fn new(buf: &'a [I]) -> Self {
        InputBuf(false, buf)
    }

    #[inline]
    pub fn is_incomplete(&self) -> bool {
        self.0
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.1.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, I: Copy + PartialEq> Input for InputBuf<'a, I> {
    type Token  = I;
    type Marker = &'a [I];
    type Buffer = &'a [I];

    #[inline]
    fn _peek(&mut self, _g: Guard) -> Option<Self::Token> {
        match self.1.first() {
            Some(c) => Some(*c),
            None    => {
                self.0 = true;

                None
            },
        }
    }

    #[inline]
    fn _pop(&mut self, g: Guard) -> Option<Self::Token> {
        self._peek(g).map(|c| {
            self.1 = &self.1[1..];

            c
        })
    }

    #[inline]
    fn _consume(&mut self, _g: Guard, n: usize) -> Option<Self::Buffer> {
        if n > self.1.len() {
            self.0 = true;

            None
        } else {
            let b = &self.1[..n];

            self.1 = &self.1[n..];

            Some(b)
        }
    }

    #[inline]
    fn _consume_while<F>(&mut self, g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        match self.1.iter().position(|c| !f(*c)) {
            Some(n) => {
                let b = &self.1[..n];

                self.1 = &self.1[n..];

                b
            },
            None    => self._consume_remaining(g),
        }
    }

    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.1.len()]
    }

    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        let b = self.1;

        self.1 = &self.1[..0];

        b
    }

    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        // Incomplete state is separate from the parsed state, no matter how we hit incomplete we
        // want to keep it.
        &self.1
    }

    #[inline]
    fn _restore(mut self, _g: Guard, m: Self::Marker) -> Self {
        self.1 = m;

        self
    }
}

impl<'a> Input for &'a str {
    type Token  = char;
    type Marker = &'a str;
    type Buffer = &'a str;

    #[inline]
    fn _peek(&mut self, _g: Guard) -> Option<Self::Token> {
        self.chars().next()
    }

    #[inline]
    fn _pop(&mut self, _g: Guard) -> Option<Self::Token> {
        let mut iter = self.char_indices();

        iter.next().map(|(_, c)| {
            match iter.next().map(|(p, _)| p) {
                Some(n) => *self = &self[n..],
                None    => *self = &self[..0],
            }

            c
        })
    }

    #[inline]
    fn _consume(&mut self, _g: Guard, n: usize) -> Option<Self::Buffer> {
        match self.char_indices().enumerate().take(n + 1).last() {
            // n always less than num if self contains more than n characters
            Some((num, (pos, _))) if n < num => {
                let b = &self[..pos];

                *self = &self[pos..];

                Some(b)
            },
            _ => None,
        }
    }

    #[inline]
    fn _consume_while<F>(&mut self, _g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        // We need to find the character following the one which did not match
        match self.char_indices().skip_while(|&(_, c)| f(c)).next() {
            Some((pos, _)) => {
                let b = &self[..pos];

                *self = &self[pos..];

                b
            },
            None => {
                let b = &self[..];

                *self = &self[..0];

                b
            }
        }
    }

    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.len()]
    }

    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        let b = &self[..];

        *self = &self[..0];

        b
    }

    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        &self
    }

    #[inline]
    fn _restore(self, _g: Guard, m: Self::Marker) -> Self {
        m
    }
}

/*
#[cfg(test)]
mod test {
    use std::fmt::Debug;

    use super::{new_buf, Input, InputBuf, DEFAULT, END_OF_INPUT};
    use parse_result::ParseResult;
    use primitives::{IntoInner, State};

    #[test]
    fn make_ret() {
        let i1: InputBuf<u8> = new_buf(END_OF_INPUT, b"in1");
        let i2: InputBuf<u8> = new_buf(DEFAULT,      b"in2");

        let r1: ParseResult<_, u32, ()> = i1.ret::<_, ()>(23u32);
        let r2: ParseResult<_, i32, ()> = i2.ret::<_, ()>(23i32);

        assert_eq!(r1.into_inner(), State::Data(InputBuf(END_OF_INPUT, b"in1"), 23u32));
        assert_eq!(r2.into_inner(), State::Data(InputBuf(DEFAULT, b"in2"), 23i32));
    }

    #[test]
    fn make_err() {
        let i1: InputBuf<u8> = new_buf(END_OF_INPUT, b"in1");
        let i2: InputBuf<u8> = new_buf(DEFAULT,      b"in2");

        let r1: ParseResult<_, (), u32> = i1.err::<(), _>(23u32);
        let r2: ParseResult<_, (), i32> = i2.err::<(), _>(23i32);

        assert_eq!(r1.into_inner(), State::Error(new_buf(END_OF_INPUT, b"in1"), 23u32));
        assert_eq!(r2.into_inner(), State::Error(new_buf(DEFAULT, b"in2"), 23i32));
    }

    /*
    #[test]
    fn primitives_slice() {
        use primitives::Primitives;
        run_primitives_test(&b"abc"[..], true);

        let mut s = &b"abc"[..];
        let m = s.mark();
        s.discard(2);
        assert_eq!(s.consume_from(m), &b"ab"[..]);
        assert_eq!(s, &b"c"[..]);
    }

    #[test]
    fn primitives_input_buf_default() {
        use primitives::Primitives;
        run_primitives_test(new_buf(DEFAULT, b"abc"), false);

        let mut s = new_buf(DEFAULT, b"abc");
        let m = s.mark();
        s.discard(2);
        assert_eq!(s.consume_from(m), &b"ab"[..]);
        assert_eq!(s, new_buf(DEFAULT, b"c"));
    }

    #[test]
    fn primitives_input_buf_end() {
        use primitives::Primitives;
        run_primitives_test(new_buf(END_OF_INPUT, b"abc"), true);

        let mut s = new_buf(END_OF_INPUT, b"abc");
        let m = s.mark();
        s.discard(2);
        assert_eq!(s.consume_from(m), &b"ab"[..]);
        assert_eq!(s, new_buf(END_OF_INPUT, b"c"));
    }

    fn run_primitives_test<B: Debug + for<'a> PartialEq<&'a [u8]>, I: Input<Token=u8, Buffer=B>>(mut s: I, last: bool) {
        use primitives::Primitives;

        assert_eq!(s.min_remaining(), 3);
        let m = s.mark();
        assert_eq!(s.min_remaining(), 3);
        assert_eq!(s.first(), Some(b'a'));
        assert_eq!(s.min_remaining(), 3);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![b'a', b'b', b'c']);
        assert_eq!(s.min_remaining(), 3);
        assert_eq!(s.consume(2), &b"ab"[..]);
        assert_eq!(s.min_remaining(), 1);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![b'c']);
        assert_eq!(s.consume(1), &b"c"[..]);
        assert_eq!(s.min_remaining(), 0);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![]);
        let mut s = s.restore(m);
        assert_eq!(s.min_remaining(), 3);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![b'a', b'b', b'c']);
        s.discard(1);
        assert_eq!(s.first(), Some(b'b'));
        assert_eq!(s.min_remaining(), 2);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![b'b', b'c']);
    }
    */
}*/
