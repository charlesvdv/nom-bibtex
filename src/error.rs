use std::error::Error;
use std::fmt;
use std::fmt::Display;

/// An error describing a problem when a parsing problem occur.
#[derive(Debug)]
pub struct ParsingError {
    description: String,
}

impl ParsingError {
    /// `description`: description of the error that has occured.
    pub fn new(description: &str) -> Self {
        ParsingError { description: description.into() }
    }
}

impl Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parsing error. Reason: {}", self.description)
    }
}

impl Error for ParsingError {
    fn description(&self) -> &str {
        &self.description
    }

    fn cause(&self) -> Option<&Error> {
        None
    }
}
