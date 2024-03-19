extern crate nom_bibtex;

use nom_bibtex::Bibtex;
use std::fs::File;
use std::io::prelude::*;

fn read_file(filename: &str) -> String {
    let mut file = File::open(filename).unwrap();
    let mut bib_content = String::new();

    file.read_to_string(&mut bib_content).unwrap();
    bib_content
}

#[test]
fn test_bib() {
    let bib_str = read_file("samples/test.bib");
    let bibtex = Bibtex::parse(&bib_str).unwrap();

    let vars = bibtex.variables();
    assert_eq!(vars["donald"], "Donald Knuth");
    assert_eq!(vars["mass"], "Massachusetts");

    assert_eq!(bibtex.preambles()[0], "Why not a preamble".to_string());

    let b0 = &bibtex.bibliographies()[0];
    assert_eq!(b0.entry_type(), "article");
    assert_eq!(b0.citation_key(), "einstein");
    assert_eq!(b0.tags()["author"], "Albert Einstein");
    assert_eq!(b0.tags()["number"], "10");

    let b1 = &bibtex.bibliographies()[1];
    assert_eq!(b1.citation_key(), "latexcompanion");
    assert_eq!(b1.tags()["address"], "Reading, Massachusetts");

    let b2 = &bibtex.bibliographies()[2];
    assert_eq!(b2.citation_key(), "knuthwebsite");
    assert_eq!(b2.tags()["author"], "Donald Knuth");
}

#[test]
fn test_lowercase() {
    let bib_str = read_file("samples/test.bib");
    let bibtex = Bibtex::parse(&bib_str).unwrap();

    let entry = &bibtex.bibliographies()[3];
    let tags = entry.tags();

    assert_eq!(entry.citation_key(), "kobayashi2014differential");
    // The sample entry uses "Author" rather than "author".
    assert_eq!(tags["author"], "Kobayashi, Shoshichi");
    assert!(tags.get("Author").is_none());
    assert_eq!(
        tags["title"],
        "Differential geometry of complex vector bundles"
    );
}

#[test]
fn test_huge_file() {
    // file borrowed from the CryptoBib project https://cryptobib.di.ens.fr/ as
    // a realistic example of a huge bibtex file
    let bib_str = read_file("samples/crypto.bib");
    let bibtex = Bibtex::parse(&bib_str);
    // test just that the parsing goes through
    assert!(bibtex.is_ok());
}

#[test]
fn test_concat() {
    let bib_str = read_file("samples/test.bib");
    let bibtex = Bibtex::parse(&bib_str).unwrap();

    let entry = &bibtex.bibliographies()[4];
    let tags = entry.tags();

    assert_eq!(entry.citation_key(), "neukirch1999ant");
    assert_eq!(
        tags["title"],
        "Algebraic Number Theory"
    );
}
