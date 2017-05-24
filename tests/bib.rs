extern crate nom_bibtex;

use std::fs::File;
use std::io::prelude::*;
use nom_bibtex::Bibtex;

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
    assert_eq!(vars[0], ("donald".into(), "Donald Knuth".into()));
    assert_eq!(vars[1], ("mass".into(), "Massachusetts".into()));

    assert_eq!(bibtex.preambles()[0], "Why not a preamble".to_string());

    let b0 = &bibtex.bibliographies()[0];
    assert_eq!(b0.entry_type(), "article");
    assert_eq!(b0.citation_key(), "einstein");
    assert_eq!(b0.tags()[0], ("author".into(), "Albert Einstein".into()));
    assert_eq!(b0.tags()[4], ("number".into(), "10".into()));

    let b1 = &bibtex.bibliographies()[1];
    assert_eq!(b1.citation_key(), "latexcompanion");
    assert_eq!(b1.tags()[4],
               ("address".into(), "Reading, Massachusetts".into()));

    let b2 = &bibtex.bibliographies()[2];
    assert_eq!(b2.citation_key(), "knuthwebsite");
    assert_eq!(b2.tags()[0], ("author".into(), "Donald Knuth".into()));
}
