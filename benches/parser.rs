#![feature(test)]

extern crate nom_bibtex;
extern crate test;

use std::fs::File;
use std::io::prelude::*;

#[bench]
fn bench_parser(b: &mut test::Bencher) {
    let mut file = File::open("samples/test.bib").unwrap();
    let mut bib_content = String::new();

    file.read_to_string(&mut bib_content).unwrap();

    b.iter(|| nom_bibtex::Bibtex::parse(&bib_content));
}
