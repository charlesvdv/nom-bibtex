use nom::Err;
use nom::error::{ErrorKind, VerboseError, convert_error};
use quick_error::quick_error;
use crate::parser::Span;

quick_error! {
    #[derive(Debug, PartialEq, Eq)]
    pub enum BibtexError {
        Parsing (descr: String) {
            description(descr)
            display(me) -> ("Parsing error. Reason: {}", me.to_string())
        }
        StringVariableNotFound (var: String) {
            description("String variable not found.")
            display(me) -> ("{}: {}", me.to_string(), var)
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
    pub fn with_context(input: &str, err: Err<VerboseError<Span>>) -> BibtexError {
        let descr = match err {
            Err::Incomplete(e) => format!("Incomplete: {:?}", e),
            Err::Error(e) | Err::Failure(e) => {
                // Convert_error does not like spans, so we need to
                // convert the error
                let e_ = VerboseError {
                    errors: e.errors.into_iter()
                        .map(|(span, kind)| (*span.fragment(), kind))
                        .collect()
                };
                convert_error(input, e_)
            },
        };
        BibtexError::Parsing(descr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_display_impls() {
        let err = BibtexError::Parsing("<some reason>".into());
        assert_eq!(format!("{}", err), "Parsing error. Reason: <some reason>");

        let err = BibtexError::StringVariableNotFound("<variable>".into());
        assert_eq!(format!("{}", err), "String variable not found: <variable>");
    }
}
