use std::error::Error;
use nom::IError;

quick_error! {
    #[derive(Debug, PartialEq, Eq)]
    pub enum BibtexError {
        Parsing (descr: String) {
            description(descr)
            display(me) -> ("Parsing error. Reason: {}", me.description())
            from(err: IError) -> (
                match err {
                    IError::Incomplete(e) => format!("Incomplete: {:?}", e),
                    IError::Error(e) => e.description().into()
                }
            )
        }
        StringVariableNotFound (var: String) {
            description("String variable not found.")
            display(me) -> ("{}: {}", me.description(), var)
        }
    }
}
