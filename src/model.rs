use crate::error::BibtexError;
use crate::parser;
use crate::parser::{Entry, mkspan, Span};
use std::result;
use std::str;
use nom::error::VerboseError;

type Result<T> = result::Result<T, BibtexError>;

/// A high-level definition of a bibtex file.
#[derive(Debug, PartialEq, Eq, Default)]
pub struct Bibtex<'a> {
    comments: Vec<&'a str>,
    preambles: Vec<String>,
    variables: Vec<(String, String)>,
    bibliographies: Vec<Bibliography<'a>>,
}

impl<'a> Bibtex<'a> {
    /// Create a new Bibtex instance from a *BibTeX* file content.
    pub fn parse(bibtex: &'a str) -> Result<Self> {
        let entries = Self::raw_parse(bibtex)?;

        let mut bibtex = Bibtex::default();

        Self::fill_variables(&mut bibtex, &entries)?;

        for entry in entries {
            match entry {
                Entry::Variable(_) => continue, // Already handled.
                Entry::Comment(v) => bibtex.comments.push(v),
                Entry::Preamble(v) => {
                    let new_val = Self::expand_str_abbreviations(v, &bibtex)?;
                    bibtex.preambles.push(new_val);
                }
                Entry::Bibliography(entry_t, citation_key, tags) => {
                    let mut new_tags = vec![];
                    for tag in tags {
                        new_tags.push((
                            tag.key.into(),
                            Self::expand_str_abbreviations(tag.value, &bibtex)?,
                        ))
                    }
                    bibtex
                        .bibliographies
                        .push(Bibliography::new(entry_t, citation_key, new_tags));
                }
            }
        }
        Ok(bibtex)
    }

    /// Get a raw vector of entries in order from the files.
    pub fn raw_parse(bibtex: &'a str) -> Result<Vec<Entry<'a>>> {
        let span = mkspan(bibtex);
        match parser::entries::<VerboseError<Span<'a>>>(span) {
            Ok((_, v)) => Ok(v),
            Err(e) => {
                Err(BibtexError::with_context(bibtex, e))
            },
        }
    }

    /// Get preambles with expanded variables.
    pub fn preambles(&self) -> &Vec<String> {
        &self.preambles
    }

    /// Get comments.
    pub fn comments(&self) -> &Vec<&str> {
        &self.comments
    }

    /// Get string variables with a tuple of key and expanded value.
    pub fn variables(&self) -> &Vec<(String, String)> {
        &self.variables
    }

    /// Get bibliographies entry with variables expanded.
    pub fn bibliographies(&self) -> &Vec<Bibliography> {
        &self.bibliographies
    }

    fn fill_variables(bibtex: &mut Bibtex, entries: &[Entry]) -> Result<()> {
        let variables = entries
            .iter()
            .filter_map(|v| match v {
                &Entry::Variable(ref v) => Some(v),
                _ => None,
            }).collect::<Vec<_>>();

        for var in &variables {
            bibtex.variables.push((
                var.key.into(),
                Self::expand_variables_value(&var.value, &variables)?,
            ));
        }

        Ok(())
    }

    fn expand_variables_value(
        var_values: &Vec<StringValueType>,
        variables: &Vec<&KeyValue>,
    ) -> Result<String> {
        let mut result_value = String::new();

        for chunck in var_values {
            match *chunck {
                StringValueType::Str(v) => result_value.push_str(v),
                StringValueType::Abbreviation(v) => {
                    let var = variables
                        .iter()
                        .find(|&&x| v == x.key)
                        .ok_or_else(|| BibtexError::StringVariableNotFound(v.into()))?;
                    result_value.push_str(&Self::expand_variables_value(&var.value, &variables)?);
                }
            }
        }
        Ok(result_value)
    }

    fn expand_str_abbreviations(value: Vec<StringValueType>, bibtex: &Bibtex) -> Result<String> {
        let mut result = String::new();

        for chunck in value {
            match chunck {
                StringValueType::Str(v) => result.push_str(v),
                StringValueType::Abbreviation(v) => {
                    let var = bibtex
                        .variables
                        .iter()
                        .find(|&x| v == x.0)
                        .ok_or_else(|| BibtexError::StringVariableNotFound(v.into()))?;
                    result.push_str(&var.1);
                }
            }
        }
        Ok(result)
    }
}

/// This is the main representation of a bibliography.
#[derive(Debug, PartialEq, Eq)]
pub struct Bibliography<'a> {
    entry_type: &'a str,
    citation_key: &'a str,
    tags: Vec<(String, String)>,
}

impl<'a> Bibliography<'a> {
    /// Create a new bibliography.
    pub fn new(
        entry_type: &'a str,
        citation_key: &'a str,
        tags: Vec<(String, String)>,
    ) -> Bibliography<'a> {
        Bibliography {
            entry_type,
            citation_key,
            tags,
        }
    }

    /// Get the entry type.
    ///
    /// It represents the type of the publications such as article, book, ...
    pub fn entry_type(&self) -> &str {
        self.entry_type
    }

    /// Get the citation key.
    ///
    /// The citation key is the the keyword used to reference the bibliography
    /// in a LaTeX file for example.
    pub fn citation_key(&self) -> &str {
        self.citation_key
    }

    /// Get the tags.
    ///
    /// Tags are the specifics information about a bibliography
    /// such as author, date, title, ...
    pub fn tags(&self) -> &Vec<(String, String)> {
        &self.tags
    }
}

/// Represent a Bibtex value which is composed of
///
/// - strings value
/// - string variable/abbreviation which will be expanded after parsing.
#[derive(Debug, PartialEq, Eq)]
pub enum StringValueType<'a> {
    /// Just a basic string.
    Str(&'a str),
    /// An abbreviation that should match some string variable.
    Abbreviation(&'a str),
}

/// Representation of a key-value.
///
/// Only used by parsing.
#[derive(Debug, PartialEq, Eq)]
pub struct KeyValue<'a> {
    pub key: &'a str,
    pub value: Vec<StringValueType<'a>>,
}

impl<'a> KeyValue<'a> {
    pub fn new(key: &'a str, value: Vec<StringValueType<'a>>) -> KeyValue<'a> {
        Self { key, value: value }
    }
}
