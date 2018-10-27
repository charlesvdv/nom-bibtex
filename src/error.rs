use std::error::Error;
use nom::Err;
use nom::types::CompleteByteSlice;

quick_error! {
    #[derive(Debug, PartialEq, Eq)]
    pub enum BibtexError {
        Parsing (descr: String) {
            description(descr)
            display(me) -> ("Parsing error. Reason: {}", me.description())
            // TODO: how can we group the below two?
            from(err: Err<CompleteByteSlice<'_>>) -> (
                match err {
                    Err::Incomplete(e) => format!("Incomplete: {:?}", e),
                    Err::Error(e) | Err::Failure(e) => e.into_error_kind().description().into(),
                }
            )
            from(err: Err<&[u8]>) -> (
                match err {
                    Err::Incomplete(e) => format!("Incomplete: {:?}", e),
                    Err::Error(e) | Err::Failure(e) => e.into_error_kind().description().into(),
                }
            )
            from(err: Err<&str>) -> (
                match err {
                    Err::Incomplete(e) => format!("Incomplete: {:?}", e),
                    Err::Error(e) | Err::Failure(e) => e.into_error_kind().description().into(),
                }
            )
        }
        StringVariableNotFound (var: String) {
            description("String variable not found.")
            display(me) -> ("{}: {}", me.description(), var)
        }
    }
}
