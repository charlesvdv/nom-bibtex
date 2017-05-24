// //! In this module reside all the parsers need for the bibtex format.
// //!
// //! All the parsers are using the *nom* crates.
//
// // Required because the compiler don't seems do recognize
// // that macros are use inside of each others..
// #![allow(dead_code)]
//
use std::str;
use nom::{alpha, is_digit, IResult, ErrorKind};
use model::{StringValueType, KeyValue};

#[derive(Debug, PartialEq, Eq)]
pub enum Entry<'a> {
    Preamble(Vec<StringValueType<'a>>),
    Comment(&'a str),
    Variable(KeyValue<'a>),
    Bibliography(&'a str, &'a str, Vec<KeyValue<'a>>),
}

named!(pub entries<Vec<Entry>>,
    many1!(entry)
);

/// Parse any entry in a bibtex file.
/// A good entry normally starts with a @ otherwise, it's
/// considered as a comment.
named!(pub entry<Entry>,
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

/// Handle data beginning without an @ which are considered comments.
named!(no_type_comment<&str>,
    map!(
        map_res!(alt!(
                take_until!("@") |
                call!(take_until_end)),
            str::from_utf8),
        str::trim
    )
);

/// Parse any entry which starts with a @.
fn entry_with_type<'a>(input: &'a [u8]) -> IResult<&'a [u8], Entry> {
    let entry_type = peeked_entry_type(input).to_full_result().unwrap();

    match entry_type.to_lowercase().as_ref() {
        "comment" => type_comment(input),
        "string" => variable(input),
        "preamble" => preamble(input),
        _ => bibliography_entry(input),
    }
}

/// Handle a comment of the format:
/// @Comment { my comment }
named!(type_comment<Entry>, do_parse!(
    entry_type >>
    comment: call!(bracketed_string) >>
    (Entry::Comment(comment))
));

/// Handle a preamble of the format:
/// @Preamble { my preamble }
named!(preamble<Entry>, do_parse!(
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
            map!(map_res!(take_until!("}"), str::from_utf8), str::trim),
            |v| vec![StringValueType::Str(v)]
        )
    ) >>
    ws!(char!('}')) >>
    (Entry::Preamble(preamble))
));

/// Handle a string variable from the bibtex format:
/// @String (key = "value") or @String {key = "value"}
named!(variable<Entry>, do_parse!(
    entry_type >>
    key_val: call!(handle_variable) >>
    alt!(char!('}') | char!(')')) >>
    (Entry::Variable(key_val))
));

/// String variable can be delimited by brackets or parenthesis.
named!(handle_variable<KeyValue>,
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

/// Parse key value pair which has the form:
/// key="value"
named!(variable_key_value_pair<KeyValue>,
    map!(
        separated_pair!(
            map_res!(call!(alpha), str::from_utf8),
            ws!(char!('=')),
            alt_complete!(
                map!(call!(quoted_string), |v| vec![StringValueType::Str(v)]) |
                call!(abbreviation_string) |
                call!(abbreviation_only)
            )
        ),
        |v: (&'a str, Vec<StringValueType<'a>>)| KeyValue::new(v.0, v.1)
    )
);

/// Handle a bibliography entry of the format:
/// @entry_type { citation_key,
///     tag1,
///     tag2
/// }
named!(pub bibliography_entry<Entry>, do_parse!(
    entry_t: entry_type >>
    ws!(char!('{')) >>
    citation_key: ws!(map_res!(take_until_and_consume!(","), str::from_utf8)) >>
    tags: bib_tags >>
    opt!(ws!(tag!(","))) >>
    ws!(char!('}')) >>
    (Entry::Bibliography(entry_t, citation_key, tags))
));

/// Parse all the tags used by one bibliography entry separated by a comma.
named!(bib_tags<Vec<KeyValue<'a>>>,
    separated_list!(
        ws!(char!(',')),
        map!(
            separated_pair!(
                // The key.
                map_res!(call!(alpha), str::from_utf8),
                ws!(char!('=')),
                alt_complete!(
                    call!(abbreviation_string) |
                    map!(call!(quoted_string), |v| vec![StringValueType::Str(v)]) |
                    map!(call!(bracketed_string), |v| vec![StringValueType::Str(v)]) |
                    map!(
                        map_res!(take_while1!(is_digit), str::from_utf8),
                        |v| vec![StringValueType::Str(v)]
                    ) |
                    call!(abbreviation_only)
                )
            ),
            |v: (&'a str, Vec<StringValueType<'a>>)| KeyValue::new(v.0, v.1)
        )
    )
);

/// Parse a bibtex entry type which looks like:
/// @type{ ...
///
/// But don't consume the last bracket.
named!(entry_type<&str>,
    delimited!(
        char!('@'),
        map_res!(ws!(alpha), str::from_utf8),
        peek!(
            alt!(
                char!('{') |
                // Handling for variable string.
                char!('(')
            )
        )

    )
);

/// Same as entry_type but with peek so it doesn't consume the
/// entry type.
named!(peeked_entry_type<&str>,
    peek!(
        entry_type
    )
);

named!(abbreviation_string<Vec<StringValueType>>,
    complete!(separated_nonempty_list!(
        ws!(char!('#')),
        alt!(
            map!(map_res!(call!(alpha), str::from_utf8), |v| StringValueType::Abbreviation(v)) |
            map!(call!(quoted_string), |v| StringValueType::Str(v))
        )
    ))
);

named!(abbreviation_only<Vec<StringValueType>>,
    ws!(map!(map_res!(call!(alpha), str::from_utf8), |v| vec![StringValueType::Abbreviation(v)]))
);

/// Only used for bibliography tags.
fn bracketed_string<'a>(input: &'a [u8]) -> IResult<&'a [u8], &str> {
    // We are not in a bracketed_string.
    if input[0] as char != '{' {
        return IResult::Error(ErrorKind::Custom(0));
    }
    let mut brackets_queue = 0;

    let mut i = 0;
    loop {
        i += 1;
        match input[i] as char {
            '{' => brackets_queue += 1,
            '}' => {
                if brackets_queue == 0 {
                    break;
                } else {
                    brackets_queue -= 1;
                }
            }
            '"' => {
                if brackets_queue == 0 {
                    return IResult::Error(ErrorKind::Custom(0));
                }
            }
            '@' => return IResult::Error(ErrorKind::Custom(0)),
            _ => continue,
        }
    }
    let value = str::from_utf8(&input[1..i]).expect("Unable to parse char sequence");
    IResult::Done(&input[i + 1..], str::trim(value))
}

fn quoted_string<'a>(input: &'a [u8]) -> IResult<&'a [u8], &str> {
    if input[0] as char != '"' {
        return IResult::Error(ErrorKind::Custom(0));
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
                    return IResult::Error(ErrorKind::Custom(0));
                }
            }
            '"' => {
                if brackets_queue == 0 {
                    break;
                }
            }
            _ => continue,
        }
    }
    let value = str::from_utf8(&input[1..i]).expect("Unable to parse char sequence");
    IResult::Done(&input[i + 1..], value)
}

named!(take_until_end,
    take_while!(call!(|c| c != '\0' as u8))
);

#[cfg(test)]
mod tests {
    // Each time we are using `separated_list`, we need to add a trailing
    // character otherwise the parser will return `IResult::Incomplete`.
    // Relevant nom issue: https://github.com/Geal/nom/issues/505

    use super::*;
    use nom::IResult;

    #[test]
    fn test_entry() {
        assert_eq!(
            entry(b" comment"),
            IResult::Done(&b""[..], Entry::Comment("comment"))
        );

        let kv = KeyValue::new("key", vec![StringValueType::Str("value")]);
        assert_eq!(
            entry(b" @ StrIng { key = \"value\" }"),
            IResult::Done(&b""[..], Entry::Variable(kv))
        );

        let bib_str = b"@misc{ patashnik-bibtexing,
           author = \"Oren Patashnik\",
           title = \"BIBTEXing\",
           year = \"1988\" }";

        let tags = vec![
            KeyValue::new("author", vec![StringValueType::Str("Oren Patashnik")]),
            KeyValue::new("title", vec![StringValueType::Str("BIBTEXing")]),
            KeyValue::new("year", vec![StringValueType::Str("1988")])
        ];
        assert_eq!(
            entry_with_type(bib_str),
            IResult::Done(&b""[..], Entry::Bibliography("misc", "patashnik-bibtexing", tags))
        );
    }

    #[test]
    fn test_no_type_comment() {
        assert_eq!(no_type_comment(b"test@"),
                   IResult::Done(&b"@"[..], "test"));
        assert_eq!(no_type_comment(b"test"),
                   IResult::Done(&b""[..], "test"));
    }

    #[test]
    fn test_entry_with_type() {
        assert_eq!(
            entry_with_type(b"@Comment{test}"),
            IResult::Done(&b""[..], Entry::Comment("test"))
        );

        let kv = KeyValue::new("key", vec![StringValueType::Str("value")]);
        assert_eq!(
            entry_with_type(b"@String{key=\"value\"}"),
            IResult::Done(&b""[..], Entry::Variable(kv))
        );

        assert_eq!(
            entry_with_type(b"@preamble{name # \"'s preamble\"}"),
            IResult::Done(&b""[..], Entry::Preamble(vec![
                StringValueType::Abbreviation("name"),
                StringValueType::Str("'s preamble")
            ]))
        );

        let bib_str = b"@misc{ patashnik-bibtexing,
           author = \"Oren Patashnik\",
           title = \"BIBTEXing\",
           year = \"1988\" }";

        let tags = vec![
            KeyValue::new("author", vec![StringValueType::Str("Oren Patashnik")]),
            KeyValue::new("title", vec![StringValueType::Str("BIBTEXing")]),
            KeyValue::new("year", vec![StringValueType::Str("1988")])
        ];
        assert_eq!(
            entry_with_type(bib_str),
            IResult::Done(&b""[..], Entry::Bibliography("misc", "patashnik-bibtexing", tags))
        );
    }

    #[test]
    fn test_type_comment() {
        assert_eq!(type_comment(b"@Comment{test}"),
                   IResult::Done(&b""[..], Entry::Comment("test")));
    }

    #[test]
    fn test_preamble() {
        assert_eq!(preamble(b"@preamble{my preamble}"),
                   IResult::Done(&b""[..],
                                 Entry::Preamble(
                                     vec![StringValueType::Str("my preamble")]
                                 ))
        );
    }

    #[test]
    fn test_variable() {
        let kv1 = KeyValue::new("key", vec![StringValueType::Str("value")]);
        let kv2 = KeyValue::new("key", vec![StringValueType::Str("value")]);
        let kv3 = KeyValue::new("key",
                                vec![
            StringValueType::Abbreviation("varone"),
            StringValueType::Abbreviation("vartwo")
        ]);

        assert_eq!(variable(b"@string{key=\"value\"}"),
                   IResult::Done(&b""[..], Entry::Variable(kv1)));

        assert_eq!(variable(b"@string( key=\"value\" )"),
                   IResult::Done(&b""[..], Entry::Variable(kv2)));

        assert_eq!(variable(b"@string( key=varone # vartwo)"),
                   IResult::Done(&b""[..], Entry::Variable(kv3)));
    }

    #[test]
    fn test_variable_key_value_pair() {
        let kv = KeyValue::new("key",
                               vec![
                StringValueType::Abbreviation("varone"),
                StringValueType::Abbreviation("vartwo")
            ]);

        assert_eq!(
            variable_key_value_pair(b"key = varone # vartwo,"),
            IResult::Done(&b","[..], kv)
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
                        KeyValue::new("year", vec![StringValueType::Str("1988")])
                   ];
        assert_eq!(
            bibliography_entry(bib_str),
            IResult::Done(
                &b""[..],
                Entry::Bibliography("misc", "patashnik-bibtexing", tags)
            )
        );
    }

    #[test]
    fn test_bib_tags() {
        let tags_str = b"author= \"Oren Patashnik\",
            year=1988,
            note= var # \"str\",
            title= { My new book }}";

        let result = vec![
            KeyValue::new("author",
                          vec![StringValueType::Str("Oren Patashnik")]),
            KeyValue::new("year",
                          vec![StringValueType::Str("1988")]),
            KeyValue::new("note",
                          vec![
                              StringValueType::Abbreviation("var"),
                              StringValueType::Str("str"),
                          ]),
            KeyValue::new("title",
                          vec![
                              StringValueType::Str("My new book")
                          ]),
        ];
        assert_eq!(bib_tags(tags_str), IResult::Done(&b"}"[..], result));
    }

    #[test]
    fn test_entry_type() {
        assert_eq!(entry_type(b"@misc{"),
                   IResult::Done(&b"{"[..], "misc"));

        assert_eq!(entry_type(b"@ misc {"),
                   IResult::Done(&b"{"[..], "misc"));

        assert_eq!(entry_type(b"@string("),
                   IResult::Done(&b"("[..], "string"));
    }

    #[test]
    fn test_abbreviation_string() {
        assert_eq!(abbreviation_string(b"var # \"string\","),
                   IResult::Done(&b","[..], vec![
                       StringValueType::Abbreviation("var"),
                       StringValueType::Str("string"),
                   ])
        );
        assert_eq!(abbreviation_string(b"\"string\" # var,"),
                   IResult::Done(&b","[..], vec![
                       StringValueType::Str("string"),
                       StringValueType::Abbreviation("var"),
                   ])
        );
        assert_eq!(abbreviation_string(b"string # var,"),
                   IResult::Done(&b","[..], vec![
                       StringValueType::Abbreviation("string"),
                       StringValueType::Abbreviation("var"),
                   ])
        );
    }

    #[test]
    fn test_abbreviation_only() {
        assert_eq!(
            abbreviation_only(b" var "),
            IResult::Done(&b""[..], vec![StringValueType::Abbreviation("var")])
        );
    }

    #[test]
    fn test_bracketed_string() {
        assert_eq!(bracketed_string(b"{ test }"), IResult::Done(&b""[..], "test"));
        assert_eq!(bracketed_string(b"{ {test} }"), IResult::Done(&b""[..], "{test}"));
        assert!(bracketed_string(b"{ @{test} }").to_full_result().is_err());
    }

    #[test]
    fn test_quoted_string() {
        assert_eq!(quoted_string(b"\"test\""), IResult::Done(&b""[..], "test"));
        assert_eq!(quoted_string(b"\"test \""), IResult::Done(&b""[..], "test "));
        assert_eq!(quoted_string(b"\"{\"test\"}\""), IResult::Done(&b""[..], "{\"test\"}"));
        assert_eq!(quoted_string(b"\"A {bunch {of} braces {in}} title\""),
                   IResult::Done(&b""[..], "A {bunch {of} braces {in}} title"));
        assert_eq!(quoted_string(b"\"Simon {\"}the {saint\"} Templar\""),
                   IResult::Done(&b""[..], "Simon {\"}the {saint\"} Templar"));
    }
}
