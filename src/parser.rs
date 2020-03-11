// //! In this module reside all the parsers need for the bibtex format.
// //!
// //! All the parsers are using the *nom* crates.
//
// // Required because the compiler don't seems do recognize
// // that macros are use inside of each others..
// #![allow(dead_code)]
//
use model::{KeyValue, StringValueType};
use nom::types::CompleteByteSlice;
use nom::{alpha, is_digit, Err, ErrorKind, IResult};
use std::str;

#[derive(Debug, PartialEq, Eq)]
pub enum Entry<'a> {
    Preamble(Vec<StringValueType<'a>>),
    Comment(&'a str),
    Variable(KeyValue<'a>),
    Bibliography(&'a str, &'a str, Vec<KeyValue<'a>>),
}

named!(pub entries<CompleteByteSlice, Vec<Entry>>,
    many1!(entry)
);

// Parse any entry in a bibtex file.
// A good entry normally starts with a @ otherwise, it's
// considered as a comment.
named!(pub entry<CompleteByteSlice, Entry>,
    ws!(
        alt!(
            do_parse!(
                peek!(char!('@')) >>
                entry: entry_with_type >>
                (entry)
            ) | do_parse!(
                comment: no_type_comment >>
                (Entry::Comment(comment))
            )
        )
    )
);

// Handle data beginning without an @ which are considered comments.
named!(no_type_comment<CompleteByteSlice, &str>,
    map!(
        map_res!(
            is_not!("@"),
            complete_byte_slice_to_str
        ),
        str::trim
    )
);

fn complete_byte_slice_to_str<'a>(s: CompleteByteSlice<'a>) -> Result<&'a str, str::Utf8Error> {
    str::from_utf8(s.0)
}

// Parse any entry which starts with a @.
fn entry_with_type<'a>(input: CompleteByteSlice<'a>) -> IResult<CompleteByteSlice<'a>, Entry> {
    let entry_type = peeked_entry_type(input).unwrap();

    match entry_type.1.to_lowercase().as_ref() {
        "comment" => type_comment(input),
        "string" => variable(input),
        "preamble" => preamble(input),
        _ => bibliography_entry(input),
    }
}

// Handle a comment of the format:
// @Comment { my comment }
named!(type_comment<CompleteByteSlice, Entry>, do_parse!(
    entry_type >>
    comment: call!(bracketed_string) >>
    (Entry::Comment(comment))
));

// Handle a preamble of the format:
// @Preamble { my preamble }
named!(preamble<CompleteByteSlice, Entry>, do_parse!(
    entry_type >>
    ws!(char!('{')) >>
    preamble: alt!(
        // Required because otherwise the `mixed_abbreviation_string` will match for
        // a single value like there were only one variable.
        do_parse!(
            val: call!(abbreviation_string) >>
            peek!(ws!(char!('}'))) >>
            (val)
        ) |
        map!(
            map!(map_res!(take_until!("}"), complete_byte_slice_to_str), str::trim),
            |v| vec![StringValueType::Str(v)]
        )
    ) >>
    ws!(char!('}')) >>
    (Entry::Preamble(preamble))
));

// Handle a string variable from the bibtex format:
// @String (key = "value") or @String {key = "value"}
named!(variable<CompleteByteSlice, Entry>, do_parse!(
    entry_type >>
    key_val: call!(handle_variable) >>
    alt!(char!('}') | char!(')')) >>
    (Entry::Variable(key_val))
));

// String variable can be delimited by brackets or parenthesis.
named!(handle_variable<CompleteByteSlice, KeyValue>,
    ws!(
        alt!(
           delimited!(
               char!('{'),
               call!(variable_key_value_pair),
               peek!(char!('}'))
           ) | delimited!(
               char!('('),
               call!(variable_key_value_pair),
               peek!(char!(')'))
           )
        )
    )
);

// Parse key value pair which has the form:
// key="value"
named!(variable_key_value_pair<CompleteByteSlice, KeyValue>,
    map!(
        separated_pair!(
            map_res!(call!(alpha), complete_byte_slice_to_str),
            ws!(char!('=')),
            alt_complete!(
                map!(call!(quoted_string), |v| vec![StringValueType::Str(v)]) |
                call!(abbreviation_string) |
                call!(abbreviation_only)
            )
        ),
        |v: (&str, Vec<StringValueType<'_>>)| KeyValue::new(v.0, v.1)
    )
);

// Handle a bibliography entry of the format:
// @entry_type { citation_key,
//     tag1,
//     tag2
// }
named!(pub bibliography_entry<CompleteByteSlice, Entry>, do_parse!(
    entry_t: entry_type >>
    ws!(char!('{')) >>
    citation_key: ws!(map_res!(take_until_and_consume!(","), complete_byte_slice_to_str)) >>
    tags: bib_tags >>
    opt!(ws!(tag!(","))) >>
    ws!(char!('}')) >>
    (Entry::Bibliography(entry_t, citation_key, tags))
));

// Parse all the tags used by one bibliography entry separated by a comma.
named!(bib_tags<CompleteByteSlice, Vec<KeyValue<'_>>>,
    separated_list!(
        ws!(char!(',')),
        map!(
            separated_pair!(
                // The key.
                map_res!(call!(alpha), complete_byte_slice_to_str),
                ws!(char!('=')),
                alt_complete!(
                    call!(abbreviation_string) |
                    map!(call!(quoted_string), |v| vec![StringValueType::Str(v)]) |
                    map!(call!(bracketed_string), |v| vec![StringValueType::Str(v)]) |
                    map!(
                        map_res!(take_while1!(is_digit), complete_byte_slice_to_str),
                        |v| vec![StringValueType::Str(v)]
                    ) |
                    call!(abbreviation_only)
                )
            ),
            |v: (&str, Vec<StringValueType<'_>>)| KeyValue::new(v.0, v.1)
        )
    )
);

// Parse a bibtex entry type which looks like:
// @type{ ...
//
// But don't consume the last bracket.
named!(entry_type<CompleteByteSlice, &str>,
    delimited!(
        char!('@'),
        map_res!(ws!(alpha), complete_byte_slice_to_str),
        peek!(
            alt!(
                char!('{') |
                // Handling for variable string.
                char!('(')
            )
        )

    )
);

// Same as entry_type but with peek so it doesn't consume the
// entry type.
named!(peeked_entry_type<CompleteByteSlice, &str>,
    peek!(
        entry_type
    )
);

named!(abbreviation_string<CompleteByteSlice, Vec<StringValueType>>,
    complete!(separated_nonempty_list!(
        ws!(char!('#')),
        alt!(
            map!(map_res!(call!(alpha), complete_byte_slice_to_str), |v| StringValueType::Abbreviation(v)) |
            map!(call!(quoted_string), |v| StringValueType::Str(v))
        )
    ))
);

named!(abbreviation_only<CompleteByteSlice, Vec<StringValueType>>,
    ws!(map!(map_res!(call!(alpha), complete_byte_slice_to_str), |v| vec![StringValueType::Abbreviation(v)]))
);

// Only used for bibliography tags.
fn bracketed_string<'a>(input: CompleteByteSlice<'a>) -> IResult<CompleteByteSlice<'a>, &str> {
    let input = &input;
    // We are not in a bracketed_string.
    if input[0] as char != '{' {
        return Err(Err::Error(error_position!(
            CompleteByteSlice(input),
            ErrorKind::Custom(0)
        )));
    }
    let mut brackets_queue = 0;

    let mut i = 0;
    loop {
        i += 1;
        match input[i] as char {
            '{' => brackets_queue += 1,
            '}' => if brackets_queue == 0 {
                break;
            } else {
                brackets_queue -= 1;
            },
            '"' => if brackets_queue == 0 {
                return Err(Err::Error(error_position!(
                    CompleteByteSlice(input),
                    ErrorKind::Custom(0)
                )));
            },
            '@' => {
                return Err(Err::Error(error_position!(
                    CompleteByteSlice(input),
                    ErrorKind::Custom(0)
                )))
            }
            _ => continue,
        }
    }
    let value = str::from_utf8(&input[1..i]).expect("Unable to parse char sequence");
    Ok((CompleteByteSlice(&input[i + 1..]), str::trim(value)))
}

fn quoted_string<'a>(input: CompleteByteSlice<'a>) -> IResult<CompleteByteSlice<'a>, &str> {
    let input = input.as_ref();
    if input[0] as char != '"' {
        return Err(Err::Error(error_position!(
            CompleteByteSlice(input),
            ErrorKind::Custom(0)
        )));
    }

    let mut brackets_queue = 0;
    let mut i = 0;
    loop {
        i += 1;
        match input[i] as char {
            '{' => brackets_queue += 1,
            '}' => {
                brackets_queue -= 1;
                if brackets_queue < 0 {
                    return Err(Err::Error(error_position!(
                        CompleteByteSlice(input),
                        ErrorKind::Custom(0)
                    )));
                }
            }
            '"' => if brackets_queue == 0 {
                break;
            },
            _ => continue,
        }
    }
    let value = str::from_utf8(&input[1..i]).expect("Unable to parse char sequence");
    Ok((CompleteByteSlice(&input[i + 1..]), value))
}

#[cfg(test)]
mod tests {
    // Each time we are using `separated_list`, we need to add a trailing
    // character otherwise the parser will return `IResult::Incomplete`.
    // Relevant nom issue: https://github.com/Geal/nom/issues/505

    use super::*;

    #[test]
    fn test_entry() {
        assert_eq!(
            entry(CompleteByteSlice(b" comment")),
            Ok((CompleteByteSlice(b""), Entry::Comment("comment")))
        );

        let kv = KeyValue::new("key", vec![StringValueType::Str("value")]);
        assert_eq!(
            entry(CompleteByteSlice(b" @ StrIng { key = \"value\" }")),
            Ok((CompleteByteSlice(b""), Entry::Variable(kv)))
        );

        let bib_str = b"@misc{ patashnik-bibtexing,
           author = \"Oren Patashnik\",
           title = \"BIBTEXing\",
           year = \"1988\" }";

        let tags = vec![
            KeyValue::new("author", vec![StringValueType::Str("Oren Patashnik")]),
            KeyValue::new("title", vec![StringValueType::Str("BIBTEXing")]),
            KeyValue::new("year", vec![StringValueType::Str("1988")]),
        ];
        assert_eq!(
            entry_with_type(CompleteByteSlice(bib_str)),
            Ok((
                CompleteByteSlice(b""),
                Entry::Bibliography("misc", "patashnik-bibtexing", tags)
            ))
        );
    }

    #[test]
    fn test_no_type_comment() {
        assert_eq!(
            no_type_comment(CompleteByteSlice(b"test@")),
            Ok((CompleteByteSlice(b"@"), "test"))
        );
        assert_eq!(
            no_type_comment(CompleteByteSlice(b"test")),
            Ok((CompleteByteSlice(b""), "test"))
        );
    }

    #[test]
    fn test_entry_with_type() {
        assert_eq!(
            entry_with_type(CompleteByteSlice(b"@Comment{test}")),
            Ok((CompleteByteSlice(b""), Entry::Comment("test")))
        );

        let kv = KeyValue::new("key", vec![StringValueType::Str("value")]);
        assert_eq!(
            entry_with_type(CompleteByteSlice(b"@String{key=\"value\"}")),
            Ok((CompleteByteSlice(b""), Entry::Variable(kv)))
        );

        assert_eq!(
            entry_with_type(CompleteByteSlice(b"@preamble{name # \"'s preamble\"}")),
            Ok((
                CompleteByteSlice(b""),
                Entry::Preamble(vec![
                    StringValueType::Abbreviation("name"),
                    StringValueType::Str("'s preamble")
                ])
            ))
        );

        let bib_str = b"@misc{ patashnik-bibtexing,
           author = \"Oren Patashnik\",
           title = \"BIBTEXing\",
           year = \"1988\" }";

        let tags = vec![
            KeyValue::new("author", vec![StringValueType::Str("Oren Patashnik")]),
            KeyValue::new("title", vec![StringValueType::Str("BIBTEXing")]),
            KeyValue::new("year", vec![StringValueType::Str("1988")]),
        ];
        assert_eq!(
            entry_with_type(CompleteByteSlice(bib_str)),
            Ok((
                CompleteByteSlice(b""),
                Entry::Bibliography("misc", "patashnik-bibtexing", tags)
            ))
        );
    }

    #[test]
    fn test_type_comment() {
        assert_eq!(
            type_comment(CompleteByteSlice(b"@Comment{test}")),
            Ok((CompleteByteSlice(b""), Entry::Comment("test")))
        );
    }

    #[test]
    fn test_preamble() {
        assert_eq!(
            preamble(CompleteByteSlice(b"@preamble{my preamble}")),
            Ok((
                CompleteByteSlice(b""),
                Entry::Preamble(vec![StringValueType::Str("my preamble")])
            ))
        );
    }

    #[test]
    fn test_variable() {
        let kv1 = KeyValue::new("key", vec![StringValueType::Str("value")]);
        let kv2 = KeyValue::new("key", vec![StringValueType::Str("value")]);
        let kv3 = KeyValue::new(
            "key",
            vec![
                StringValueType::Abbreviation("varone"),
                StringValueType::Abbreviation("vartwo"),
            ],
        );

        assert_eq!(
            variable(CompleteByteSlice(b"@string{key=\"value\"}")),
            Ok((CompleteByteSlice(b""), Entry::Variable(kv1)))
        );

        assert_eq!(
            variable(CompleteByteSlice(b"@string( key=\"value\" )")),
            Ok((CompleteByteSlice(b""), Entry::Variable(kv2)))
        );

        assert_eq!(
            variable(CompleteByteSlice(b"@string( key=varone # vartwo)")),
            Ok((CompleteByteSlice(b""), Entry::Variable(kv3)))
        );
    }

    #[test]
    fn test_variable_key_value_pair() {
        let kv = KeyValue::new(
            "key",
            vec![
                StringValueType::Abbreviation("varone"),
                StringValueType::Abbreviation("vartwo"),
            ],
        );

        assert_eq!(
            variable_key_value_pair(CompleteByteSlice(b"key = varone # vartwo,")),
            Ok((CompleteByteSlice(b","), kv))
        );
    }

    #[test]
    fn test_bibliography_entry() {
        let bib_str = b"@misc{ patashnik-bibtexing,
           author = \"Oren Patashnik\",
           title = \"BIBTEXing\",
           year = \"1988\", }";

        let tags = vec![
            KeyValue::new("author", vec![StringValueType::Str("Oren Patashnik")]),
            KeyValue::new("title", vec![StringValueType::Str("BIBTEXing")]),
            KeyValue::new("year", vec![StringValueType::Str("1988")]),
        ];
        assert_eq!(
            bibliography_entry(CompleteByteSlice(bib_str)),
            Ok((
                CompleteByteSlice(b""),
                Entry::Bibliography("misc", "patashnik-bibtexing", tags)
            ))
        );
    }

    #[test]
    fn test_bib_tags() {
        let tags_str = b"author= \"Oren Patashnik\",
            year=1988,
            note= var # \"str\",
            title= { My new book }}";

        let result = vec![
            KeyValue::new("author", vec![StringValueType::Str("Oren Patashnik")]),
            KeyValue::new("year", vec![StringValueType::Str("1988")]),
            KeyValue::new(
                "note",
                vec![
                    StringValueType::Abbreviation("var"),
                    StringValueType::Str("str"),
                ],
            ),
            KeyValue::new("title", vec![StringValueType::Str("My new book")]),
        ];
        assert_eq!(
            bib_tags(CompleteByteSlice(tags_str)),
            Ok((CompleteByteSlice(b"}"), result))
        );
    }

    #[test]
    fn test_entry_type() {
        assert_eq!(
            entry_type(CompleteByteSlice(b"@misc{")),
            Ok((CompleteByteSlice(b"{"), "misc"))
        );

        assert_eq!(
            entry_type(CompleteByteSlice(b"@ misc {")),
            Ok((CompleteByteSlice(b"{"), "misc"))
        );

        assert_eq!(
            entry_type(CompleteByteSlice(b"@string(")),
            Ok((CompleteByteSlice(b"("), "string"))
        );
    }

    #[test]
    fn test_abbreviation_string() {
        assert_eq!(
            abbreviation_string(CompleteByteSlice(b"var # \"string\",")),
            Ok((
                CompleteByteSlice(b","),
                vec![
                    StringValueType::Abbreviation("var"),
                    StringValueType::Str("string"),
                ]
            ))
        );
        assert_eq!(
            abbreviation_string(CompleteByteSlice(b"\"string\" # var,")),
            Ok((
                CompleteByteSlice(b","),
                vec![
                    StringValueType::Str("string"),
                    StringValueType::Abbreviation("var"),
                ]
            ))
        );
        assert_eq!(
            abbreviation_string(CompleteByteSlice(b"string # var,")),
            Ok((
                CompleteByteSlice(b","),
                vec![
                    StringValueType::Abbreviation("string"),
                    StringValueType::Abbreviation("var"),
                ]
            ))
        );
    }

    #[test]
    fn test_abbreviation_only() {
        assert_eq!(
            abbreviation_only(CompleteByteSlice(b" var ")),
            Ok((
                CompleteByteSlice(b""),
                vec![StringValueType::Abbreviation("var")]
            ))
        );
    }

    #[test]
    fn test_bracketed_string() {
        assert_eq!(
            bracketed_string(CompleteByteSlice(b"{ test }")),
            Ok((CompleteByteSlice(b""), "test"))
        );
        assert_eq!(
            bracketed_string(CompleteByteSlice(b"{ {test} }")),
            Ok((CompleteByteSlice(b""), "{test}"))
        );
        assert!(bracketed_string(CompleteByteSlice(b"{ @{test} }")).is_err());
    }

    #[test]
    fn test_quoted_string() {
        assert_eq!(
            quoted_string(CompleteByteSlice(b"\"test\"")),
            Ok((CompleteByteSlice(b""), "test"))
        );
        assert_eq!(
            quoted_string(CompleteByteSlice(b"\"test \"")),
            Ok((CompleteByteSlice(b""), "test "))
        );
        assert_eq!(
            quoted_string(CompleteByteSlice(b"\"{\"test\"}\"")),
            Ok((CompleteByteSlice(b""), "{\"test\"}"))
        );
        assert_eq!(
            quoted_string(CompleteByteSlice(b"\"A {bunch {of} braces {in}} title\"")),
            Ok((CompleteByteSlice(b""), "A {bunch {of} braces {in}} title"))
        );
        assert_eq!(
            quoted_string(CompleteByteSlice(b"\"Simon {\"}the {saint\"} Templar\"")),
            Ok((CompleteByteSlice(b""), "Simon {\"}the {saint\"} Templar"))
        );
    }
}
