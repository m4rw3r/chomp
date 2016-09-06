//! Support for the tendril type, this is probably a bad idea since it is actually not a rope and
//! will probably cause excessive reallocations while parsing.

use std::mem;

use tendril::ByteTendril;
use primitives::Guard;
use types::{Buffer, Input};

// TODO: Impl for more than byte tendril
impl Input for ByteTendril {
    type Token  = u8;
    type Marker = ByteTendril;
    type Buffer = ByteTendril;

    #[inline]
    fn _peek(&mut self, _g: Guard) -> Option<Self::Token> {
        self.as_ref().first().cloned()
    }

    #[inline]
    fn _pop(&mut self, _g: Guard) -> Option<Self::Token> {
        if self.len32() > 0 {
            let t = self.as_ref()[0];

            self.pop_front(1);

            Some(t)
        } else {
            None
        }
    }

    #[inline]
    fn _consume(&mut self, _g: Guard, n: usize) -> Option<Self::Buffer> {
        if n > self.len32() as usize {
            None
        } else {
            let b = self.subtendril(0, n as u32);

            self.pop_front(n as u32);

            Some(b)
        }
    }

    #[inline]
    fn _consume_while<F>(&mut self, g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        match self.iter().position(|c| !f(*c)) {
            Some(n) => {
                let b = self.subtendril(0, n as u32);

                self.pop_front(n as u32);

                b
            },
            None    => self._consume_remaining(g),
        }
    }

    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        // Just the tendril analogue of the slice version:
        m.subtendril(0, m.len32() - self.len32())
    }

    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        let b = self.subtendril(0, 0);

        mem::replace(self, b)
    }

    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        self.clone()
    }

    #[inline]
    fn _restore(self, _g: Guard, m: Self::Marker) -> Self {
        m
    }
}

impl Buffer for ByteTendril {
    type Token = u8;

    fn fold<B, F>(self, init: B, f: F) -> B
      where F: FnMut(B, Self::Token) -> B {
        (&self[..]).iter().cloned().fold(init, f)
    }

    fn iterate<F>(&self, mut f: F)
      where F: FnMut(Self::Token) {
        for i in (&self[..]).iter().cloned() {
            f(i)
        }
    }

    fn len(&self) -> usize {
        self.len32() as usize
    }

    #[cfg(not(feature = "core"))]
    fn to_vec(&self) -> Vec<Self::Token> {
        (&self[..]).iter().cloned().collect()
    }

    #[cfg(not(feature = "core"))]
    fn into_vec(self) -> Vec<Self::Token> {
        (&self[..]).iter().cloned().collect()
    }
}

#[cfg(test)]
mod test {
    use tendril::Tendril;

    #[test]
    fn basic() {
        use ascii::decimal;
        use primitives::IntoInner;

        assert_eq!(decimal(Tendril::from_slice(&b"123"[..])).into_inner(), (Tendril::from_slice(&b""[..]), Ok(123i32)));
    }

    #[test]
    fn primitives() {
        ::types::test::run_primitives_test(Tendril::from_slice(&b"abc"[..]), |x| x);
    }
}
