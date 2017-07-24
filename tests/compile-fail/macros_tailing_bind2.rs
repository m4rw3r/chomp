// error-pattern:error: no rules expected the token `x`

#[macro_use]
extern crate chomp;

use chomp::{ParseResult, Input, parse_only};

fn parser(i: Input<u8>) -> ParseResult<u8, u8, ()> {
    fn f(i: Input<u8>) -> ParseResult<u8, u8, ()> {
        i.ret(3)
    }

    parse!{i;
        let x = s -> s.ret::<u8, ()>(3)
    }
}

fn main() {
    let r = parse_only(parser, b"5");
}
