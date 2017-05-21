use std::str;
use nom::IError;
use error::ParsingError;
use parser;

#[cfg(features="nightly")]
use std::convert::TryFrom;

#[derive(Debug, PartialEq, Eq)]
/// A high-level definition of a bibtex file that contains
/// multiples entries.
pub struct Bibtex {
    entries: Vec<Entry>,
}

impl Bibtex {
    pub fn new(entries: Vec<Entry>) -> Self {
        Self { entries }
    }


    pub fn parse(bibtex: &str) -> Result<Self, ParsingError> {
        match parser::bibtex(bibtex.as_bytes()).to_full_result() {
            Ok(v) => Ok(v),
            Err(e) => Err(convert_nom_ierror(e)),
        }
    }

    pub fn entries(&self) -> &Vec<Entry> {
        &self.entries
    }
}

#[cfg(features="nightly")]
impl<'a> TryFrom<&'a str> for Bibtex {
    type Error = ParsingError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Bibtex::parse(value)
    }
}

/// Describe an entry in the bibtex file.
/// We can have 4 types of entries:
///
/// - A comment.
/// - A preamble is a comment which will be kept in the generated
/// Bibtex file.
/// - A string variable.
/// - A bibliograpy entry.
///
/// More information can be found
/// [here](http://maverick.inria.fr/~Xavier.Decoret/resources/xdkbibtex/bibtex_summary.html)
#[derive(Debug, PartialEq, Eq)]
pub enum Entry {
    Preamble(String),
    Comment(String),
    Variable(String, String),
    Bibliography(BibliographyEntry),
}

/// An entry of a bibtex bibliography.
#[derive(Debug, PartialEq, Eq)]
pub struct BibliographyEntry {
    /// The type of the bibtex entry.
    ///
    /// Example: *misc*, *article*, *manual*, ...
    pub entry_type: String,
    /// The citation key used to reference the bibliography in the LaTeX
    /// file.
    pub citation_key: String,
    /// Defines the characteristics of the bibliography such as *author*,
    /// *title*, *year*, ...
    tags: Vec<(String, String)>,
}

impl BibliographyEntry {
    pub fn new(entry_type: &str, citation_key: &str, tags: Vec<(String, String)>) -> Self {
        BibliographyEntry {
            entry_type: entry_type.into(),
            citation_key: citation_key.into(),
            tags,
        }
    }

    pub fn tags(&self) -> &Vec<(String, String)> {
        &self.tags
    }
}

/// Convert str to a ```BibliographyEntry```.
#[cfg(features="nightly")]
impl<'a> TryFrom<&'a str> for BibliographyEntry {
    type Error = ParsingError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match parser::bibliography_entry(value.as_bytes()).to_full_result() {
            Ok(v) => {
                if let Entry::Bibliography(entry) = v {
                    Ok(entry)
                }
                unreachable!();
            }
            Err(e) => Err(handle_nom_ierror),
        }
    }
}

/// Helper function to convert a IError from nom to
/// custom ParsingError.
fn convert_nom_ierror(err: IError) -> ParsingError {
    match err {
        IError::Incomplete(e) => {
            let msg = format!("Incomplete: {:?}", e);
            ParsingError::new(&msg)
        }
        IError::Error(e) => ParsingError::new(e.description()),
    }
}
