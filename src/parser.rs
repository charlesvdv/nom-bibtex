// //! In this module reside all the parsers need for the bibtex format.
// //!
// //! All the parsers are using the *nom* crates.
//
// // Required because the compiler don't seems do recognize
// // that macros are use inside of each others..
//
use crate::model::{KeyValue, StringValueType};
use nom::character::complete::char as _char;
use nom::error::ParseError;
use nom::IResult;
use nom::{
    branch::alt,
    bytes::complete::{is_not, take_until, take_while1},
    character::complete::{digit1, multispace0},
    combinator::{map, opt, peek},
    multi::{separated_list0, separated_list1},
    sequence::{delimited, preceded, separated_pair, tuple},
    AsChar, Slice,
};
use nom_locate::LocatedSpan;
#[cfg(feature = "trace")]
use nom_tracable::tracable_parser;
use nom_tracable::TracableInfo;
use std::num::NonZeroUsize;
use std::str;

const NEEDED_ONE: nom::Needed = nom::Needed::Size(unsafe { NonZeroUsize::new_unchecked(1) });

pub type Span<'a> = LocatedSpan<&'a str, TracableInfo>;
pub fn mkspan(s: &str) -> Span<'_> {
    Span::new_extra(s, TracableInfo::new())
}

#[derive(Debug, PartialEq, Eq)]
pub enum Entry {
    Preamble(Vec<StringValueType>),
    Comment(String),
    Variable(KeyValue),
    Bibliography(String, String, Vec<KeyValue>),
}

// Defines a parser with a common type signature
macro_rules! def_parser {
    ($vis:vis $name:ident(
        $input_name:ident$(,)? $($arg:ident, $type:ty),*
    ) -> $ret:ty; $body:tt) => {
        // NOTE: Hidden behind feature gate because error messages are terrible
        // with this directive included
        #[cfg_attr(feature = "trace", tracable_parser)]
        $vis fn $name<'a, E> (
            $input_name: Span<'a>, $($arg: $ty),*
        ) -> IResult<Span<'a>, $ret, E>
            where E: ParseError<Span<'a>>,
        {
            $body
        }
    }
}

// Makes a parser whitespace insensitive before the content
macro_rules! pws {
    ($inner:expr) => {
        preceded(multispace0, $inner)
    };
}
// Makes a parser whitespace insensitive before and after the content
macro_rules! dws {
    ($inner:expr) => {
        delimited(multispace0, $inner, multispace0)
    };
}

// Helper macro for the chain_parsers macro.
macro_rules! optional_ident {
    () => {
        _
    };
    ($name:ident) => {
        $name
    };
}
/**
    Applies a series of parsers, and stores results from some of them

    The first two arguments are the name of the input string, followed
    by the name to store the rest of the input in after all parsers have
    been applied

    Example:
    chain_parsers!{input, rest;
        parser1 => name1,
        parser2,
        parser3 => name3
    }
    Ok((rest, (name1, name3)))
*/
macro_rules! chain_parsers {
    ($input:ident, $rest:ident; $( $parser:expr $(=> $name:ident)? ),+) => {
        let mut parser = tuple(( $( $parser ),* ));
        let (
            $rest,
            ( $( optional_ident!($($name)?) ),* )
        ) = parser($input)?;
    };
}

// Converts a span into a raw string
fn span_to_str(span: Span<'_>) -> &str {
    span.fragment()
}

// Parses a single identifier
def_parser!(ident(input) -> &str; {
    map(
        take_while1(|c: char| c.is_alphanum() || c == '_' || c == '-'),
        span_to_str
    )(input)
});

// Parses an abbreviation: An identifier that can be surrounded by whitespace
def_parser!(abbreviation_only(input) -> StringValueType; {
    map(
        dws!(ident),
        |v| StringValueType::Abbreviation(v.into())
    )(input)
});

// Only used for bibliography tags.
def_parser!(bracketed_string(input) -> &str; {
    // We are not in a bracketed_string.
    match input.fragment().chars().next() {
        Some('{') => {},
        Some(_) => {
            return Err(nom::Err::Error(E::from_char(input, '{')));
        }
        None => {
            return Err(nom::Err::Incomplete(NEEDED_ONE));
        }
    }

    let mut brackets_queue = 0;

    let mut last_idx = 0;
    for (i, c) in input.fragment().char_indices().skip(1) {
        last_idx = i+1;
        match c {
            '{' => brackets_queue += 1,
            '}' => if brackets_queue == 0 {
                break;
            } else {
                brackets_queue -= 1;
            },
            _ => continue,
        }
    }
    Ok((
        input.slice(last_idx..),
        span_to_str(input.slice(1..last_idx-1)).trim()
    ))
});

def_parser!(quoted_string(input) -> &str; {
    match input.fragment().chars().next() {
        Some('"') => {},
        Some(_) => {
            return Err(nom::Err::Error(E::from_char(input, '"')));
        }
        None => {
            return Err(nom::Err::Incomplete(NEEDED_ONE));
        }
    }
    let mut brackets_queue = 0;
    let mut last_idx = 0;
    for (i, c) in input.fragment().char_indices().skip(1) {
        last_idx = i+1;
        match c {
            '{' => brackets_queue += 1,
            '}' => {
                brackets_queue -= 1;
                if brackets_queue < 0 {
                    return Err(nom::Err::Error(E::from_char(input, '"')));
                }
            }
            '"' => if brackets_queue == 0 {
                break;
            },
            _ => continue,
        }
    }
    Ok((
        input.slice(last_idx..),
        span_to_str(input.slice(1..last_idx-1))
    ))
});

def_parser!(pub abbreviation_string(input) -> Vec<StringValueType>; {
    separated_list1(
        pws!(_char('#')),
        pws!(
            alt((
                abbreviation_only,
                map(quoted_string, |v: &str| StringValueType::Str(v.into()))
            ))
        )
    )(input)
});

// Parse a bibtex entry type which looks like:
// @type{ ...
//
// But don't consume the last bracket.
def_parser!(entry_type(input) -> &str; {
    delimited(
        pws!(_char('@')),
        pws!(ident),
        pws!(peek(alt((_char('{'), _char('(')))))
    )(input)
});

// Parse key value pair which has the form:
// key="value"
def_parser!(variable_key_value_pair(input) -> KeyValue; {
    map(
        separated_pair(
            pws!(ident),
            dws!(_char('=')),
            alt((
                map(quoted_string, |v: &str| vec!(StringValueType::Str(v.into()))),
                abbreviation_string,
                map(abbreviation_only, |v| vec!(v)),
            ))
        ),
        |v: (&str, Vec<StringValueType>)| KeyValue::new(v.0.into(), v.1)
    )(input)
});

// String variable can be delimited by brackets or parenthesis.
def_parser!(handle_variable(input) -> KeyValue; {
    alt((
        delimited(
            pws!(_char('{')),
            dws!(variable_key_value_pair),
            peek(_char('}'))
        ),
        delimited(
            pws!(_char('(')),
            dws!(variable_key_value_pair),
            peek(_char(')'))
        )
    ))(input)
});

// Handle a string variable from the bibtex format:
// @String (key = "value") or @String {key = "value"}
def_parser!(variable(input) -> Entry; {
    chain_parsers!(input, rest;
        entry_type,
        handle_variable => key_val,
        alt((_char('}'), _char(')')))
    );
    Ok((rest, Entry::Variable(key_val)))
});

// Handle a preamble of the format:
// @Preamble { "my preamble" }
def_parser!(preamble(input) -> Entry; {
    chain_parsers!(input, rest;
        entry_type,
        pws!(_char('{')),
        abbreviation_string => preamble,
        pws!(_char('}'))
    );
    Ok((rest, Entry::Preamble(preamble)))
});

// Parse all the tags used by one bibliography entry separated by a comma.
def_parser!(bib_tags(input) -> Vec<KeyValue>; {
    separated_list0(
        dws!(_char(',')),
        map(
            separated_pair(
                ident,
                dws!(_char('=')),
                alt((
                    map(digit1, |v| vec!(StringValueType::Str(span_to_str(v).into()))),
                    abbreviation_string,
                    map(quoted_string, |v| vec![StringValueType::Str(v.into())]),
                    map(bracketed_string, |v| vec![StringValueType::Str(v.into())]),
                    map(abbreviation_only, |v| vec![v]),
                ))
            ),
            |v: (&str, Vec<StringValueType>)| KeyValue::new(v.0.into(), v.1)
        )
    )(input)
});

// Handle a bibliography entry of the format:
// @entry_type { citation_key,
//     tag1,
//     tag2
// }
def_parser!(bibliography_entry(input) -> Entry; {
    chain_parsers! (input, rem;
        entry_type => entry_t ,
        dws!(_char('{')),
        map(take_until(","), span_to_str) => citation_key,
        dws!(_char(',')),
        bib_tags => tags ,
        opt(pws!(_char(','))),
        pws!(_char('}'))
    );
    Ok((rem, Entry::Bibliography(entry_t.into(), citation_key.into(), tags)))
});

// Handle a comment of the format:
// @Comment { my comment }
def_parser!(type_comment(input) -> Entry; {
    chain_parsers!(input, rem;
        entry_type,
        bracketed_string => comment
    );
    Ok((rem, Entry::Comment(comment.into())))
});

// Same as entry_type but with peek so it doesn't consume the
// entry type.
def_parser!(peeked_entry_type(input) -> &str; {
    peek(entry_type)(input)
});

// Parse any entry which starts with a @.
def_parser!(entry_with_type(input) -> Entry; {
    let entry_type = peeked_entry_type::<E>(input)?;

    match entry_type.1.to_lowercase().as_ref() {
        "comment" => type_comment(input),
        "string" => variable(input),
        "preamble" => preamble(input),
        _ => bibliography_entry(input),
    }
});

// Handle data beginning without an @ which are considered comments.
def_parser!(no_type_comment(input) -> &str; {
    map(is_not("@"), span_to_str)(input)
});

// Parse any entry in a bibtex file.
// A good entry starts with a @ otherwise, it's
// considered as a comment.
def_parser!(entry(input) -> Entry; {
    pws!(
        alt((
            entry_with_type,
            map(no_type_comment, |v| Entry::Comment(v.to_string().trim().into()))
        ))
    )(input)
});

// Parses a whole bibtex file to yield a list of entries
def_parser!(pub entries(input) -> Vec<Entry>; {
    if input.fragment().trim().is_empty() {
        Ok((input, vec!()))
    }
    else {
        let (rest_slice, new_entry) = entry(input)?;
        let (remaining_slice, mut rest_entries) = entries(rest_slice)?;
        // NOTE: O(n) insertions, could cause issues in the future
        rest_entries.insert(0, new_entry);
        Ok((remaining_slice, rest_entries))
    }
});

#[cfg(test)]
mod tests {
    // Each time we are using `separated_list`, we need to add a trailing
    // character otherwise the parser will return `IResult::Incomplete`.
    // Relevant nom issue: https://github.com/Geal/nom/issues/505

    use super::*;

    use nom::error::ErrorKind;

    type Error<'a> = (Span<'a>, ErrorKind);

    // Convenience macro to convert a Span<&str> to an &str which is required
    // because `PartialEq` on spans differenciate between offsets. For asserts
    // to work as expected, this macro can be used instead
    macro_rules! str_err {
        ($val:expr) => {
            $val.map(|(span, parse)| (span_to_str(span), parse))
        };
    }

    #[test]
    fn test_entry() {
        assert_eq!(
            str_err!(entry::<Error>(mkspan(" comment"))),
            Ok(("", Entry::Comment("comment".to_string())))
        );

        let kv = KeyValue::new(
            "key".to_string(),
            vec![StringValueType::Str("value".to_string())],
        );
        assert_eq!(
            str_err!(entry::<Error>(mkspan(" @ StrIng { key = \"value\" }"))),
            Ok(("", Entry::Variable(kv)))
        );

        let bib_str = "@misc{ patashnik-bibtexing,
           author = \"Oren Patashnik\",
           title = \"BIBTEXing\",
           year = \"1988\" }";

        let tags = vec![
            KeyValue::new(
                "author".to_string(),
                vec![StringValueType::Str("Oren Patashnik".to_string())],
            ),
            KeyValue::new(
                "title".to_string(),
                vec![StringValueType::Str("BIBTEXing".to_string())],
            ),
            KeyValue::new(
                "year".to_string(),
                vec![StringValueType::Str("1988".to_string())],
            ),
        ];
        assert_eq!(
            str_err!(entry_with_type::<Error>(mkspan(bib_str))),
            Ok((
                "",
                Entry::Bibliography("misc".to_string(), "patashnik-bibtexing".to_string(), tags)
            ))
        );
    }

    #[test]
    fn test_entry_with_journal() {
        assert_eq!(
            str_err!(entry::<Error>(mkspan(" comment"))),
            Ok(("", Entry::Comment("comment".to_string())))
        );

        let kv = KeyValue::new(
            "key".to_string(),
            vec![StringValueType::Str("value".to_string())],
        );
        assert_eq!(
            str_err!(entry::<Error>(mkspan(" @ StrIng { key = \"value\" }"))),
            Ok(("", Entry::Variable(kv)))
        );

        let bib_str = "@misc{ patashnik-bibtexing,
           author = \"Oren Patashnik\",
           title = \"BIBTEXing\",
           journal = SOME_ABBREV,
           year = \"1988\" }";

        let tags = vec![
            KeyValue::new(
                "author".to_string(),
                vec![StringValueType::Str("Oren Patashnik".to_string())],
            ),
            KeyValue::new(
                "title".to_string(),
                vec![StringValueType::Str("BIBTEXing".to_string())],
            ),
            KeyValue::new(
                "journal".to_string(),
                vec![StringValueType::Abbreviation("SOME_ABBREV".to_string())],
            ),
            KeyValue::new(
                "year".to_string(),
                vec![StringValueType::Str("1988".to_string())],
            ),
        ];
        assert_eq!(
            str_err!(entry_with_type::<Error>(mkspan(bib_str))),
            Ok((
                "",
                Entry::Bibliography("misc".to_string(), "patashnik-bibtexing".to_string(), tags)
            ))
        );
    }

    #[test]
    fn test_no_type_comment() {
        assert_eq!(
            str_err!(no_type_comment::<Error>(mkspan("test@"))),
            Ok(("@", "test"))
        );
        assert_eq!(
            str_err!(no_type_comment::<Error>(mkspan("test"))),
            Ok(("", "test"))
        );
    }

    #[test]
    fn test_entry_with_type() {
        assert_eq!(
            str_err!(entry_with_type::<Error>(mkspan("@Comment{test}"))),
            Ok(("", Entry::Comment("test".to_string())))
        );

        let kv = KeyValue::new(
            "key".to_string(),
            vec![StringValueType::Str("value".to_string())],
        );
        assert_eq!(
            str_err!(entry_with_type::<Error>(mkspan("@String{key=\"value\"}"))),
            Ok(("", Entry::Variable(kv)))
        );

        assert_eq!(
            str_err!(entry_with_type::<Error>(mkspan(
                "@preamble{name # \"'s preamble\"}"
            ))),
            Ok((
                "",
                Entry::Preamble(vec![
                    StringValueType::Abbreviation("name".to_string()),
                    StringValueType::Str("'s preamble".to_string())
                ])
            ))
        );

        let bib_str = "@misc{ patashnik-bibtexing,
           author = \"Oren Patashnik\",
           title = \"BIBTEXing\",
           year = \"1988\" }";

        let tags = vec![
            KeyValue::new(
                "author".to_string(),
                vec![StringValueType::Str("Oren Patashnik".to_string())],
            ),
            KeyValue::new(
                "title".to_string(),
                vec![StringValueType::Str("BIBTEXing".to_string())],
            ),
            KeyValue::new(
                "year".to_string(),
                vec![StringValueType::Str("1988".to_string())],
            ),
        ];
        assert_eq!(
            str_err!(entry_with_type::<Error>(mkspan(bib_str))),
            Ok((
                "",
                Entry::Bibliography("misc".to_string(), "patashnik-bibtexing".to_string(), tags)
            ))
        );
    }

    #[test]
    fn test_entry_with_type_and_spaces() {
        let kv = KeyValue::new(
            "key".to_string(),
            vec![StringValueType::Str("value".to_string())],
        );
        assert_eq!(
            str_err!(entry_with_type::<Error>(mkspan("@ String{key=\"value\"}"))),
            Ok(("", Entry::Variable(kv)))
        );
    }

    #[test]
    fn test_type_comment() {
        let parse = type_comment::<Error>(mkspan("@Comment{test}"));

        assert_eq!(
            str_err!(parse),
            Ok(("", Entry::Comment("test".to_string())))
        );
    }

    #[test]
    fn test_preamble() {
        assert_eq!(
            str_err!(preamble::<Error>(mkspan("@preamble{\"my preamble\"}"))),
            Ok((
                "",
                Entry::Preamble(vec![StringValueType::Str("my preamble".to_string())])
            ))
        );
    }

    #[test]
    fn test_variable() {
        let kv1 = KeyValue::new(
            "key".to_string(),
            vec![StringValueType::Str("value".to_string())],
        );
        let kv2 = KeyValue::new(
            "key".to_string(),
            vec![StringValueType::Str("value".to_string())],
        );
        let kv3 = KeyValue::new(
            "key".to_string(),
            vec![
                StringValueType::Abbreviation("varone".to_string()),
                StringValueType::Abbreviation("vartwo".to_string()),
            ],
        );

        assert_eq!(
            str_err!(variable::<Error>(mkspan("@string{key=\"value\"}"))),
            Ok(("", Entry::Variable(kv1)))
        );

        assert_eq!(
            str_err!(variable::<Error>(mkspan("@string( key=\"value\" )"))),
            Ok(("", Entry::Variable(kv2)))
        );

        assert_eq!(
            str_err!(variable::<Error>(mkspan("@string( key=varone # vartwo)"))),
            Ok(("", Entry::Variable(kv3)))
        );
    }

    #[test]
    fn test_variable_key_value_pair() {
        let kv = KeyValue::new(
            "key".to_string(),
            vec![
                StringValueType::Abbreviation("varone".to_string()),
                StringValueType::Abbreviation("vartwo".to_string()),
            ],
        );

        assert_eq!(
            str_err!(variable_key_value_pair::<Error>(mkspan(
                "key = varone # vartwo,"
            ))),
            Ok((",", kv))
        );
    }

    #[test]
    fn test_bibliography_entry() {
        let bib_str = "@misc{ patashnik-bibtexing,
           author = \"Oren Patashnik\",
           title = \"BIBTEXing\",
           year = \"1988\", }";

        let tags = vec![
            KeyValue::new(
                "author".to_string(),
                vec![StringValueType::Str("Oren Patashnik".to_string())],
            ),
            KeyValue::new(
                "title".to_string(),
                vec![StringValueType::Str("BIBTEXing".to_string())],
            ),
            KeyValue::new(
                "year".to_string(),
                vec![StringValueType::Str("1988".to_string())],
            ),
        ];
        assert_eq!(
            str_err!(bibliography_entry::<Error>(mkspan(bib_str))),
            Ok((
                "",
                Entry::Bibliography("misc".to_string(), "patashnik-bibtexing".to_string(), tags)
            ))
        );
    }
    #[test]
    fn test_bibliography_entry_works_with_bracketed_strings_at_end() {
        let bib_str = "@misc{ patashnik-bibtexing,
           year = {1988}}";

        let tags = vec![KeyValue::new(
            "year".to_string(),
            vec![StringValueType::Str("1988".to_string())],
        )];
        assert_eq!(
            str_err!(bibliography_entry::<Error>(mkspan(bib_str))),
            Ok((
                "",
                Entry::Bibliography("misc".to_string(), "patashnik-bibtexing".to_string(), tags)
            ))
        );
    }

    #[test]
    fn test_bib_tags() {
        let tags_str = "author= \"Oren Patashnik\",
            year=1988,
            note= var # \"str\",
            title= { My new book }}";

        let result = vec![
            KeyValue::new(
                "author".to_string(),
                vec![StringValueType::Str("Oren Patashnik".to_string())],
            ),
            KeyValue::new(
                "year".to_string(),
                vec![StringValueType::Str("1988".to_string())],
            ),
            KeyValue::new(
                "note".to_string(),
                vec![
                    StringValueType::Abbreviation("var".to_string()),
                    StringValueType::Str("str".to_string()),
                ],
            ),
            KeyValue::new(
                "title".to_string(),
                vec![StringValueType::Str("My new book".to_string())],
            ),
        ];
        assert_eq!(
            str_err!(bib_tags::<Error>(mkspan(tags_str))),
            Ok(("}", result))
        );
    }

    #[test]
    fn test_abbreviation_string() {
        assert_eq!(
            str_err!(abbreviation_string::<Error>(mkspan("var # \"string\","))),
            Ok((
                ",",
                vec![
                    StringValueType::Abbreviation("var".to_string()),
                    StringValueType::Str("string".to_string()),
                ]
            ))
        );
        assert_eq!(
            str_err!(abbreviation_string::<Error>(mkspan("\"string\" # var,"))),
            Ok((
                ",",
                vec![
                    StringValueType::Str("string".to_string()),
                    StringValueType::Abbreviation("var".to_string()),
                ]
            ))
        );
        assert_eq!(
            str_err!(abbreviation_string::<Error>(mkspan("string # var,"))),
            Ok((
                ",",
                vec![
                    StringValueType::Abbreviation("string".to_string()),
                    StringValueType::Abbreviation("var".to_string()),
                ]
            ))
        );
    }

    #[test]
    fn test_abbreviation_string_does_not_match_multiple_bare_words() {
        assert_eq!(
            str_err!(abbreviation_string::<()>(mkspan("var string"))),
            Ok((
                "string",
                vec![StringValueType::Abbreviation("var".to_string())]
            ))
        );
    }

    #[test]
    fn test_abbreviation_only() {
        assert_eq!(
            str_err!(abbreviation_only::<Error>(mkspan(" var "))),
            Ok(("", StringValueType::Abbreviation("var".to_string())))
        );
    }

    #[test]
    fn test_abbreviation_with_underscore() {
        assert_eq!(
            str_err!(abbreviation_only::<Error>(mkspan(" IEEE_J_CAD "))),
            Ok(("", StringValueType::Abbreviation("IEEE_J_CAD".to_string())))
        );
    }

    #[test]
    fn test_bracketed_string() {
        assert_eq!(
            str_err!(bracketed_string::<Error>(mkspan("{ test }"))),
            Ok(("", "test"))
        );
        assert_eq!(
            str_err!(bracketed_string::<Error>(mkspan("{ test word}"))),
            Ok(("", "test word"))
        );
        assert_eq!(
            str_err!(bracketed_string::<Error>(mkspan("{ {test} }"))),
            Ok(("", "{test}"))
        );
        // assert!(bracketed_string::<Error>(mkspan("{ @{test} }")).is_err());

        assert_eq!(
            str_err!(bracketed_string::<Error>(mkspan("{True: love and @jlo}"))),
            Ok(("", "True: love and @jlo"))
        );

        assert_eq!(
            str_err!(bracketed_string::<Error>(mkspan(
                "{True: love and \"Trump\"}"
            ))),
            Ok(("", "True: love and \"Trump\""))
        );
    }

    #[test]
    fn test_bracketed_string_takes_the_correct_amount_of_brackets() {
        assert_eq!(
            str_err!(bracketed_string::<Error>(mkspan("{ test }} } }"))),
            Ok(("} } }", "test"))
        );
    }

    #[test]
    fn test_quoted_string() {
        assert_eq!(
            str_err!(quoted_string::<Error>(mkspan("\"test\""))),
            Ok(("", "test"))
        );
        assert_eq!(
            str_err!(quoted_string::<Error>(mkspan("\"test \""))),
            Ok(("", "test "))
        );
        assert_eq!(
            str_err!(quoted_string::<Error>(mkspan("\"{\"test\"}\""))),
            Ok(("", "{\"test\"}"))
        );
        assert_eq!(
            str_err!(quoted_string::<Error>(mkspan(
                "\"A {bunch {of} braces {in}} title\""
            ))),
            Ok(("", "A {bunch {of} braces {in}} title"))
        );
        assert_eq!(
            str_err!(quoted_string::<Error>(mkspan(
                "\"Simon {\"}the {saint\"} Templar\""
            ))),
            Ok(("", "Simon {\"}the {saint\"} Templar"))
        );
    }

    #[test]
    fn test_variable_with_underscore() {
        let kv1 = KeyValue::new(
            "IEEE_J_ANNE".to_string(),
            vec![StringValueType::Str(
                "{IEEE} Trans. Aeronaut. Navig. Electron.".to_string(),
            )],
        );

        assert_eq!(
            str_err!(variable::<Error>(mkspan(
                "@string{IEEE_J_ANNE       = \"{IEEE} Trans. Aeronaut. Navig. Electron.\"}"
            ))),
            Ok(("", Entry::Variable(kv1)))
        );
    }

    #[test]
    fn test_dashes_in_variables_are_supported() {
        let kv1 = KeyValue::new(
            "IEEE_J_B-ME".to_string(),
            vec![StringValueType::Str(
                "{IEEE} Trans. Bio-Med. Eng.".to_string(),
            )],
        );

        assert_eq!(
            str_err!(variable::<Error>(mkspan(
                "@STRING{IEEE_J_B-ME       = \"{IEEE} Trans. Bio-Med. Eng.\"}"
            ))),
            Ok(("", Entry::Variable(kv1)))
        );

        assert_eq!(
            str_err!(abbreviation_only::<Error>(mkspan(" IEE_j_B-ME "))),
            Ok(("", StringValueType::Abbreviation("IEE_j_B-ME".to_string())))
        );
    }

    #[test]
    fn malformed_entries_produce_errors() {
        let bib_str = "
            @Article{coussy_et_al_word_length_HLS,
              author    = {Philippe Coussy and Ghizlane Lhairech-Lebreton and Dominique Heller},
              title     = {Multiple Word-Length High-Level Synthesis},
              journal   = {{EURASIP} Journal on Embedded Systems},
              year      = {2008},
              volume    = {2008},
              number    = {1},
              pages     = {916867},
              month     = jul,
              issn      = {1687-3963},
              day       = {29},
              doi       = {10.1155/2008/916867},
              publisher = {Springer Nature},
            }

            @Article{constantinides_word_length_optimization,
              author     = {Constantinides, George A.},
              title      = {Word-length Optimization for Differentiable Nonlinear Systems},
              journal    = {ACM Trans. Des. Autom. Electron. Syst.},
              year       = {2006},
              volume     = {11},
              number     = {1},
              pages      = {26--43},
              month      = jan,
              issn       = {1084-4309},
              acmid      = {1124716},
              address    = {New York, NY, USA},
              doi        = {http://dx.doi.org/10.1145/1124713.1124716},
              issue_d
              keywords   = {Signal processing, bitwidth, synthesis,
              numpages   = {18},
              publisher  = {ACM},
            }";

        assert!(
            entries::<Error>(mkspan(bib_str)).is_err(),
            "Malformed entries list parsed correctly"
        );
    }

    #[test]
    fn months_file_parses_without_error() {
        let file = "
            @STRING{ dec = \"December\" }
            ";
        entries::<Error>(mkspan(file)).unwrap();
    }
}
