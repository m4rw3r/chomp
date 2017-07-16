#[macro_use]
extern crate chomp;

use chomp::prelude::*;
use chomp::buffer::{Source, Stream};

use std::net::TcpStream;


fn main() {
    let tcp = TcpStream::connect("faumail.fau.de:143").unwrap();
    let mut src = Source::new(tcp);

    let p = src.parse(parser!{take_till(|c| c == b'\r') <* string(b"\r\n")});
    println!("{:?}", p);
}
