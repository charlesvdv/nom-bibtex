use nom::Err;
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
impl<T> From<Err<T>> for BibtexError {
    fn from(err: Err<T>) -> BibtexError {
        let descr = match err {
            Err::Incomplete(e) => format!("Incomplete: {:?}", e),
            Err::Error(e) | Err::Failure(e) => e.into_error_kind().description().into(),
        };
        BibtexError::Parsing(descr)
    }
}
