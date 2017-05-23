# nom-bibtex
[![Build Status](https://travis-ci.org/charlesvdv/nom-bibtex.svg?branch=master)](https://travis-ci.org/charlesvdv/nom-bibtex)
[![Docs Badge](https://docs.rs/nom-bibtex/badge.svg)](https://docs.rs/nom-bibtex)
[![crates.io](http://meritbadge.herokuapp.com/nom-bibtex)](https://crates.io/crates/nom-bibtex)

A nearly feature complete *BibTeX* zero-copy parser using [nom](https://github.com/Geal/nom).

**nom-bibtex** can parse the four different type of entries listed in the
[BibTeX format description](http://www.bibtex.org/Format/):

- Preamble which allows to call *LaTeX* command inside your *BibTeX*.
- String which defines abbreviations in a key-value format.
- Comment
- Entry which defines a bibliography entry.

## Code example

```rust
extern crate nom_bibtex;
use nom_bibtex::*;

const BIBFILE_DATA: &str = "
    @preamble{
        A bibtex preamble
    }

    @misc{my_citation_key,
        author= {Charles Vandevoorde},
        title = \"nom-bibtex\"
    }
";

fn main() {
    let biblio = Bibtex::parse(BIBFILE_DATA).unwrap();
    let entries = biblio.entries();

    assert_eq!(entries[0], Entry::Preamble("A bibtex preamble".into()));
    assert_eq!(entries[1], Entry::Bibliography(BibliographyEntry::new(
        "misc",
        "my_citation_key",
        vec![
            ("author".into(), "Charles Vandevoorde".into()),
            ("title".into(), "nom-bibtex".into())
        ]
    )));
}
```

## TODO

- The string variable are not yet used.
