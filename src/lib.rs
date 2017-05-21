//! *nom-bibtex* is a bibtex parser.
//! The library handles many specials features of bibtex such as:
//!
//! - Preambles
//! - Variables
//! - Comments
//!
//! Here is a sample of code using nom-bibtex.
//!
//! ```
//! extern crate nom_bibtex;
//! use nom_bibtex::*;
//!
//! const BIBFILE_DATA: &str = "
//!     @preamble{
//!         A bibtex preamble
//!     }
//!
//!     @misc{my_citation_key,
//!         author= {Charles Vandevoorde},
//!         title = \"nom-bibtex\"
//!     }
//! ";
//!
//! fn main() {
//!     let biblio = Bibtex::parse(BIBFILE_DATA).unwrap();
//!     let entries = biblio.entries();
//!
//!     assert_eq!(entries[0], Entry::Preamble("A bibtex preamble".into()));
//!     assert_eq!(entries[1], Entry::Bibliography(BibliographyEntry::new(
//!         "misc",
//!         "my_citation_key",
//!         vec![
//!             ("author".into(), "Charles Vandevoorde".into()),
//!             ("title".into(), "nom-bibtex".into())
//!         ]
//!     )));
//! }
//! ```
//!
#[macro_use]
extern crate nom;

pub mod error;
mod parser;
mod model;

pub use model::{Bibtex, Entry, BibliographyEntry};
