#[macro_use]
extern crate nom;

pub mod error;
mod parser;
mod model;

pub use model::{Bibtex, Entry, BibliographyEntry};
