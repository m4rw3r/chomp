//! http parser comparable to the http-parser found in attoparsec's examples.
//! 
//! Reads data in the following format:
//! 
//! ```text
//! GET /robot.txt HTTP/1.1
//! Host: localhost
//! Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8
//! 
//! ```
use std::fs::File;
use std::env;

#[macro_use]
extern crate chomp;

use chomp::*;

#[derive(Debug)]
struct Request<'a> {
    method:  &'a [u8],
    uri:     &'a [u8],
    version: &'a [u8],
}

#[derive(Debug)]
struct Header<'a> {
    name:  &'a [u8],
    value: Vec<&'a [u8]>,
}

/*
fn is_token(c: u8) -> bool {
    c < 128 && c > 31 && b"()<>@,;:\\\"/[]?={} \t".iter().position(|&i| i == c).is_none()
}
*/

fn is_token(c: u8) -> bool {
    match c {
        128...255 => false,
        0...31    => false,
        b'('      => false,
        b')'      => false,
        b'<'      => false,
        b'>'      => false,
        b'@'      => false,
        b','      => false,
        b';'      => false,
        b':'      => false,
        b'\\'     => false,
        b'"'      => false,
        b'/'      => false,
        b'['      => false,
        b']'      => false,
        b'?'      => false,
        b'='      => false,
        b'{'      => false,
        b'}'      => false,
        b' '      => false,
        _         => true,
    }
}

fn is_horizontal_space(c: u8) -> bool { c == b' ' || c == b'\t' }
fn is_space(c: u8)            -> bool { c == b' ' }
fn is_not_space(c: u8)        -> bool { c != b' ' }
fn is_end_of_line(c: u8)      -> bool { c == b'\r' || c == b'\n' }
fn is_http_version(c: u8)     -> bool { c >= b'0' && c <= b'9' || c == b'.' }

fn end_of_line(i: Input<u8>) -> U8Result<u8> {
    or(i, |i| parse!{i;
               token(b'\r');
               token(b'\n');
               ret b'\r'},
          |i| token(i, b'\n'))
    /*or(i, |i| token(i, b'\r').bind(|i, _| token(i, b'\n').bind(|i, _| i.ret(b'\r'))),
          |i| token(i, b'\n'))*/
}

fn http_version(i: Input<u8>) -> U8Result<&[u8]> {
    /*string(i, b"HTTP/")              . bind(|i, _|
    take_while1(i, is_http_version))*/
    parse!{i;
        string(b"HTTP/");
        take_while1(is_http_version)
    }
}

#[inline(always)]
fn request_line(i: Input<u8>) -> U8Result<Request> {
    /*take_while1(i, is_token)     . bind(|i, method|
    take_while1(i, is_space)     . bind(|i, _|
    take_while1(i, is_not_space) . bind(|i, uri|
    take_while(i, is_space)      . bind(|i, _|
    http_version(i)              . bind(|i, version|
    i                            . ret(Request {
        method:  method,
        uri:     uri,
        version: version,
    }))))))*/
    parse!{i;
        let method  = take_while1(is_token);
                      take_while1(is_space);
        let uri     = take_while1(is_not_space);
                      take_while1(is_space);
        let version = http_version();

        ret Request {
            method:  method,
            uri:     uri,
            version: version,
        }
    }
}

fn message_header_line(i: Input<u8>) -> U8Result<&[u8]> {
    /*take_while1(i, is_horizontal_space) . bind(|i, _|
    take_till(i, is_end_of_line)        . bind(|i, line|
    end_of_line(i)                      . bind(|i, _| i  . ret(line))))*/
    parse!{i;
                   take_while1(is_horizontal_space);
        let line = take_till(is_end_of_line);
                   end_of_line();

        ret line
    }
}

fn message_header(i: Input<u8>) -> U8Result<Header> {
    /*take_while1(i, is_token)      . bind(|i, name|
    token(i, b':')                . bind(|i, _|
    many1(i, message_header_line) . bind(|i, lines|
    i                             . ret(Header {
        name:  name,
        value: lines,
    }))))*/
    parse!{i;
        let name  = take_while1(is_token);
                    token(b':');
        let lines = many1(message_header_line);

        ret Header {
            name:  name,
            value: lines,
        }
    }
}

#[inline(always)]
fn request(i: Input<u8>) -> U8Result<(Request, Vec<Header>)> {
    /*request_line(i)         .bind(|i, r|
    end_of_line(i)          .bind(|i, _|
    many(i, message_header) .bind(|i, h|
    end_of_line(i)          .bind(|i, _|
        i                   .ret((r, h))))))*/
    parse!{i;
        let r = request_line();
                end_of_line();
        let h = many(message_header);
                end_of_line();

        ret (r, h)
    }
}

fn main() {
    let mut contents: Vec<u8> = Vec::new();

    {
        use std::io::Read;

        let mut file = File::open(env::args().nth(1).expect("File to read")).ok().expect("Failed to open file");

        let _ = file.read_to_end(&mut contents).unwrap();
    }

    let i = Iter::new(&contents, request);

    println!("num: {}", i.count());
}
