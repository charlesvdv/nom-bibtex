//! A feature complete *BibTeX* parser using [nom](https://github.com/Geal/nom).
//!
//! **nom-bibtex** can parse the four differents types of entries listed in the
//! [BibTeX format description](http://www.bibtex.org/Format/):
//!
//! - Preambles which allows to call *LaTeX* command inside your *BibTeX*.
//! - Strings which defines abbreviations in a key-value format.
//! - Comments.
//! - Bibliography entries.
//!
//! ## Example
//!
//! ```
//! extern crate nom_bibtex;
//! use nom_bibtex::*;
//!
//! const BIBFILE_DATA: &str = "@preamble{
//!         A bibtex preamble
//!     }
//!
//!     @Comment{
//!         Here is a comment.
//!     }
//!
//!     Another comment!
//!
//!     @string ( name= \"Charles Vandevoorde\")
//!     @string (github = \"https://github.com/charlesvdv\")
//!
//!     @misc {my_citation_key,
//!         author= name,
//!         title = \"nom-bibtex\",
//!         note = \"Github: \" # github
//!     }
//! ";
//!
//! fn main() {
//!     let bibtex = Bibtex::parse(BIBFILE_DATA).unwrap();
//!
//!     let preambles = bibtex.preambles();
//!     assert_eq!(preambles[0], "A bibtex preamble");
//!
//!     let comments = bibtex.comments();
//!     assert_eq!(comments[0], "Here is a comment.");
//!     assert_eq!(comments[1], "Another comment!");
//!
//!     let variables = bibtex.variables();
//!     assert_eq!(variables[0], ("name".into(), "Charles Vandevoorde".into()));
//!     assert_eq!(variables[1], ("github".into(), "https://github.com/charlesvdv".into()));
//!
//!     let biblio = &bibtex.bibliographies()[0];
//!     assert_eq!(biblio.entry_type(), "misc");
//!     assert_eq!(biblio.citation_key(), "my_citation_key");
//!
//!     let bib_tags = biblio.tags();
//!     assert_eq!(bib_tags[0], ("author".into(), "Charles Vandevoorde".into()));
//!     assert_eq!(bib_tags[1], ("title".into(), "nom-bibtex".into()));
//!     assert_eq!(bib_tags[2], ("note".into(), "Github: https://github.com/charlesvdv".into()));
//! }
//! ```
//!
#[macro_use]
extern crate nom;
#[macro_use]
extern crate quick_error;

pub mod error;
mod parser;
pub mod model;

pub use model::{Bibtex, Bibliography};
pub use parser::Entry;
