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
        if let Some(n) = self.iter().position(|c| !f(*c)) {
            let b = &self[..n];

            *self = &self[n..];

            b
        }  else {
            let b = &self[..];

            *self = &self[..0];

            b
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
/// Input buffer type which contains a flag which tells if we might need to read more data.
// TODO: Move to buffer module and make public?
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
        if let Some(c) = self.1.first() {
            Some(*c)
        } else {
            self.0 = true;

            None
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
        if let Some(n) = self.1.iter().position(|c| !f(*c)) {
            let b = &self.1[..n];

            self.1 = &self.1[n..];

            b
        } else {
            self._consume_remaining(g)
        }
    }

    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.1.len()]
    }

    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        self.0 = true;

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
            // num always equal to n if self contains more than n characters
            Some((num, (pos, _))) if n == num => {
                let b = &self[..pos];

                *self = &self[pos..];

                Some(b)
            },
            // num always equal to n - 1 if self contains exactly n characters
            Some((num, _)) if n == num + 1 => {
                let b = &self[..];

                *self = &self[..0];

                Some(b)
            },
            _ => None,
        }
    }

    #[inline]
    fn _consume_while<F>(&mut self, _g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        // We need to find the character following the one which did not match
        if let Some((pos, _)) = self.char_indices().skip_while(|&(_, c)| f(c)).next() {
            let b = &self[..pos];

            *self = &self[pos..];

            b
        } else {
            let b = &self[..];

            *self = &self[..0];

            b
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

#[cfg(test)]
mod test {
    use std::fmt::Debug;

    use types::{Buffer, Input, InputBuf};

    #[test]
    fn test_slice() {
        run_primitives_test(&b"abc"[..], |x| x);
    }

    #[test]
    fn test_string() {
        run_primitives_test(&"abc"[..], |c| c as char);
    }

    #[test]
    fn test_input_buf() {
        use primitives::Primitives;

        run_primitives_test(InputBuf::new(b"abc"), |x| x);

        let mut b = InputBuf::new(b"a");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        b.peek();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        b.pop();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.peek(), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.pop(), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);
        b.consume(1);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        b.consume(1);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.consume(1), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.consume(3), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.consume_while(|_| true), &b"ab"[..]);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.consume_while(|c| c == b'a'), &b"a"[..]);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.consume_while(|c| c == b'b'), &b"b"[..]);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.consume_while(|c| c == b'b'), &b""[..]);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"abc");
        let m = b.mark();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);
        b.consume(3);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.consume_from(m), &b"abc"[..]);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"abc");
        let m = b.mark();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);
        b.consume(2);
        b.consume(2);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        let b = b.restore(m);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);

        let mut b = InputBuf::new(b"abc");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);
        b.consume_remaining();
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
    }

    /// Should recieve an Input with the tokens 'a', 'b' and 'c' remaining.
    pub fn run_primitives_test<I: Input, F: Fn(u8) -> I::Token>(mut s: I, f: F)
      where I::Token:  Debug,
            I::Buffer: Clone {
        use primitives::Primitives;

        fn buffer_eq_slice<B: Buffer + Clone, F: Fn(u8) -> B::Token>(b: B, s: &[u8], f: F)
          where B::Token: Debug, {
            assert_eq!(b.len(), s.len());
            assert_eq!(b.is_empty(), s.is_empty());
            assert_eq!(b.clone().fold(0, |n, c| {
                assert_eq!(c, f(s[n]));

                n + 1
            }), s.iter().count());
            assert_eq!(b.to_vec(), s.iter().cloned().map(f).collect::<Vec<_>>());
        }

        let m = s.mark();
        assert_eq!(s.peek(), Some(f(b'a')));
        assert_eq!(s.pop(),  Some(f(b'a')));
        assert_eq!(s.peek(), Some(f(b'b')));
        assert_eq!(s.pop(),  Some(f(b'b')));
        assert_eq!(s.peek(), Some(f(b'c')));
        assert_eq!(s.pop(),  Some(f(b'c')));
        assert_eq!(s.peek(), None);
        assert_eq!(s.pop(),  None);
        assert_eq!(s.peek(), None);
        assert_eq!(s.pop(),  None);
        assert!(s.consume(1).is_none());
        buffer_eq_slice(s.consume_remaining(), &b""[..], &f);

        {
            let mut n = 0;

            let b = s.consume_while(|_| { n += 1; true });

            assert_eq!(n, 0);
            buffer_eq_slice(b, &b""[..], &f);
        }

        let mut s = s.restore(m);
        assert_eq!(s.peek(), Some(f(b'a')));
        let m = s.mark();
        buffer_eq_slice(s.consume_remaining(), &b"abc"[..], &f);
        assert_eq!(s.peek(), None);
        let mut s = s.restore(m);
        assert_eq!(s.peek(), Some(f(b'a')));
        let m = s.mark();

        {
            let b = s.consume(2);

            assert_eq!(b.is_some(), true);
            buffer_eq_slice(b.unwrap(), &b"ab"[..], &f);
        }

        assert_eq!(s.peek(), Some(f(b'c')));

        let mut s = s.restore(m);
        assert_eq!(s.peek(), Some(f(b'a')));
        let m = s.mark();

        {
            let b = s.consume(3);

            assert_eq!(b.is_some(), true);
            buffer_eq_slice(b.unwrap(), &b"abc"[..], &f);
        }

        assert_eq!(s.peek(), None);
        let mut s = s.restore(m);
        assert_eq!(s.peek(), Some(f(b'a')));
        let m = s.mark();

        {
            let mut n = 0;

            let b = s.consume_while(|c| {
                assert_eq!(c, f(b"abc"[n]));

                n += 1;

                n < 3
            });

            assert_eq!(n, 3);
            buffer_eq_slice(b, &b"ab"[..], &f);
        }

        assert_eq!(s.peek(), Some(f(b'c')));
        assert_eq!(s.pop(),  Some(f(b'c')));
        assert_eq!(s.peek(), None);
        assert_eq!(s.pop(),  None);

        buffer_eq_slice(s.consume_from(m), &b"abc"[..], &f);
    }
}
