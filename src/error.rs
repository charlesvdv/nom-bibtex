use nom::Err;
use nom::error::{ErrorKind, VerboseError, convert_error};
use std::error::Error;

quick_error! {
    #[derive(Debug, PartialEq, Eq)]
    pub enum BibtexError {
        Parsing (descr: String) {
            description(descr)
            display(me) -> ("Parsing error. Reason: {}", me.description())
        }
        StringVariableNotFound (var: String) {
            description("String variable not found.")
            display(me) -> ("{}: {}", me.description(), var)
        }
    }
}

// We cannot use the from() from quick_error, because we need to put lifetimes that we didn't
// define.
impl<'a> From<Err<(&str, ErrorKind)>> for BibtexError {
    fn from(err: Err<(&str, ErrorKind)>) -> BibtexError {
        let descr = match err {
            Err::Incomplete(e) => format!("Incomplete: {:?}", e),
            Err::Error((_, e)) | Err::Failure((_, e)) => {
                e.description().into()
            },
        };
        BibtexError::Parsing(descr)
    }
}

impl BibtexError {
    pub fn with_context(input: &str, err: Err<VerboseError<&str>>) -> BibtexError {
        let descr = match err {
            Err::Incomplete(e) => format!("Incomplete: {:?}", e),
            Err::Error(e) | Err::Failure(e) => {
                convert_error(input, e)
            },
        };
        BibtexError::Parsing(descr)
    }
}
