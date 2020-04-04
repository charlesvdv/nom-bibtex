// //! In this module reside all the parsers need for the bibtex format.
// //!
// //! All the parsers are using the *nom* crates.
//
// // Required because the compiler don't seems do recognize
// // that macros are use inside of each others..
// #![allow(dead_code)]
//
use model::{KeyValue, StringValueType};
use nom::{Err, IResult};
use nom::error::ErrorKind;
use nom::character::{
    is_digit,
    is_alphabetic,
    complete::{alpha0, multispace0},
};
use nom::bytes::complete::is_not;
use std::str;

#[derive(Debug, PartialEq, Eq)]
pub enum Entry<'a> {
    Preamble(Vec<StringValueType<'a>>),
    Comment(&'a str),
    Variable(KeyValue<'a>),
    Bibliography(&'a str, &'a str, Vec<KeyValue<'a>>),
}



pub fn entries<'a>(input: &[u8]) -> IResult<&[u8], Vec<Entry>> {
    if input.is_empty() {
        Ok((input, vec!()))
    }
    else {
        let (rest_slice, new_entry) = entry(input)?;
        let (remaining_slice, mut rest_entries) = entries(rest_slice)?;
        // NOTE: O(n) insertions, could cause issues in the future
        rest_entries.insert(0, new_entry);
        Ok((remaining_slice, rest_entries))
    }
}

// Parse any entry in a bibtex file.
// A good entry normally starts with a @ otherwise, it's
// considered as a comment.
named!(pub entry<&[u8], Entry>,
    preceded!(
        multispace0,
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
named!(no_type_comment<&[u8], &str>,
    map!(
        map_res!(
            is_not("@"),
            complete_byte_slice_to_str
        ),
        str::trim
    )
);

fn complete_byte_slice_to_str<'a>(s: &'a [u8]) -> Result<&'a str, str::Utf8Error> {
    str::from_utf8(s)
}

// Parse any entry which starts with a @.
fn entry_with_type<'a>(input: &'a [u8]) -> IResult<&'a [u8], Entry> {
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
named!(type_comment<&[u8], Entry>, do_parse!(
    entry_type >>
    comment: call!(bracketed_string) >>
    (Entry::Comment(comment))
));

// Handle a preamble of the format:
// @Preamble { my preamble }
named!(preamble<&[u8], Entry>, do_parse!(
    entry_type >>
    preceded!(multispace0, char!('{')) >>
    preamble: alt!(
        // Required because otherwise the `mixed_abbreviation_string` will match for
        // a single value like there were only one variable.
        do_parse!(
            val: call!(abbreviation_string) >>
            peek!(preceded!(multispace0, char!('}'))) >>
            (val)
        ) |
        map!(
            map!(map_res!(take_until!("}"), complete_byte_slice_to_str), str::trim),
            |v| vec![StringValueType::Str(v)]
        )
    ) >>
    preceded!(multispace0, char!('}')) >>
    (Entry::Preamble(preamble))
));

// Handle a string variable from the bibtex format:
// @String (key = "value") or @String {key = "value"}
named!(variable<&[u8], Entry>, do_parse!(
    entry_type >>
    key_val: call!(handle_variable) >>
    alt!(char!('}') | char!(')')) >>
    (Entry::Variable(key_val))
));

// String variable can be delimited by brackets or parenthesis.
named!(handle_variable<&[u8], KeyValue>,
        alt!(
           delimited!(
               preceded!(multispace0, char!('{')),
               delimited!(multispace0, call!(variable_key_value_pair), multispace0),
               peek!(char!('}'))
           ) | delimited!(
               preceded!(multispace0, char!('(')),
               delimited!(multispace0, call!(variable_key_value_pair), multispace0),
               peek!(char!(')'))
           )
        )
);

// Parse key value pair which has the form:
// key="value"
named!(variable_key_value_pair<&[u8], KeyValue>,
    map!(
        separated_pair!(
            preceded!(
                multispace0,
                map_res!(
                    take_while1!(|c: u8| is_alphabetic(c) || c == b'_' || c == b'-'),
                    complete_byte_slice_to_str
                )
            ),
            preceded!(multispace0, char!('=')),
            preceded!(
                multispace0,
                alt!(
                    map!(preceded!(multispace0, call!(quoted_string)), |v| vec![StringValueType::Str(v)]) |
                    call!(abbreviation_string) |
                    call!(abbreviation_only)
                )
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
named!(pub bibliography_entry<&[u8], Entry>, do_parse!(
    entry_t: entry_type >>
    preceded!(multispace0, char!('{')) >>
    citation_key: preceded!(multispace0, map_res!(take_until!(","), complete_byte_slice_to_str)) >>
    delimited!(multispace0, char!(','), multispace0) >>
    tags: bib_tags >>
    opt!(preceded!(multispace0, tag!(","))) >>
    delimited!(multispace0, char!('}'), multispace0) >>
    (Entry::Bibliography(entry_t, citation_key, tags))
));

// Parse all the tags used by one bibliography entry separated by a comma.
named!(bib_tags<&[u8], Vec<KeyValue<'_>>>,
    separated_list!(
        delimited!(multispace0, char!(','), multispace0),
        map!(
            separated_pair!(
                // The key.
                map_res!(call!(alpha0), complete_byte_slice_to_str),
                delimited!(multispace0, char!('='), multispace0),
                alt!(
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
named!(entry_type<&[u8], &str>,
    delimited!(
        char!('@'),
        map_res!(
            delimited!(multispace0, alpha0, multispace0),
            complete_byte_slice_to_str
        ),
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
named!(peeked_entry_type<&[u8], &str>,
    peek!(
        entry_type
    )
);

named!(abbreviation_string<&[u8], Vec<StringValueType>>,
    separated_nonempty_list!(
        preceded!(multispace0, char!('#')),
        preceded!(
            multispace0,
            alt!(
                map!(map_res!(
                    take_while1!(|c: u8| is_alphabetic(c) || c == b'_' || c == b'-'),
                    complete_byte_slice_to_str
                ), |v| StringValueType::Abbreviation(v)) |
                map!(call!(quoted_string), |v| StringValueType::Str(v))
            )
        )
    )
);

named!(abbreviation_only<&[u8], Vec<StringValueType>>,
    delimited!(
        multispace0,
        map!(
            map_res!(
                take_while1!(|c: u8| is_alphabetic(c) || c == b'_' || c == b'-'),
                complete_byte_slice_to_str
            ),
            |v| vec![StringValueType::Abbreviation(v)]
        ),
        multispace0
    )
);

// Only used for bibliography tags.
fn bracketed_string<'a>(input: &'a [u8]) -> IResult<&'a [u8], &str> {
    let input = &input;
    // We are not in a bracketed_string.
    if input[0] as char != '{' {
        return Err(nom::Err::Error((input, ErrorKind::Tag)));
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
                return Err(nom::Err::Error((input, ErrorKind::Tag)));
            },
            '@' => {
                return Err(nom::Err::Error((input, ErrorKind::Tag)));
            }
            _ => continue,
        }
    }
    let value = str::from_utf8(&input[1..i]).expect("Unable to parse char sequence");
    Ok((&input[i + 1..], str::trim(value)))
}

fn quoted_string<'a>(input: &'a [u8]) -> IResult<&'a [u8], &str> {
    let input = input.as_ref();
    if input[0] as char != '"' {
        return Err(nom::Err::Error((input, ErrorKind::Tag)));
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
                    return Err(nom::Err::Error((input, ErrorKind::Tag)));
                }
            }
            '"' => if brackets_queue == 0 {
                break;
            },
            _ => continue,
        }
    }
    let value = str::from_utf8(&input[1..i]).expect("Unable to parse char sequence");
    Ok((&input[i + 1..], value))
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
            entry(b" comment"),
            Ok((&b""[..], Entry::Comment("comment")))
        );

        let kv = KeyValue::new("key", vec![StringValueType::Str("value")]);
        assert_eq!(
            entry(b" @ StrIng { key = \"value\" }"),
            Ok((&b""[..], Entry::Variable(kv)))
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
            entry_with_type(bib_str),
            Ok((
                &b""[..],
                Entry::Bibliography("misc", "patashnik-bibtexing", tags)
            ))
        );
    }

    #[test]
    fn test_entry_with_journal() {
        assert_eq!(
            entry(b" comment"),
            Ok((&b""[..], Entry::Comment("comment")))
        );

        let kv = KeyValue::new("key", vec![StringValueType::Str("value")]);
        assert_eq!(
            entry(b" @ StrIng { key = \"value\" }"),
            Ok((&b""[..], Entry::Variable(kv)))
        );

        let bib_str = b"@misc{ patashnik-bibtexing,
           author = \"Oren Patashnik\",
           title = \"BIBTEXing\",
           journal = SOME_ABBREV,
           year = \"1988\" }";

        let tags = vec![
            KeyValue::new("author", vec![StringValueType::Str("Oren Patashnik")]),
            KeyValue::new("title", vec![StringValueType::Str("BIBTEXing")]),
            KeyValue::new("journal", vec![StringValueType::Abbreviation("SOME_ABBREV")]),
            KeyValue::new("year", vec![StringValueType::Str("1988")]),
        ];
        assert_eq!(
            entry_with_type(bib_str),
            Ok((
                &b""[..],
                Entry::Bibliography("misc", "patashnik-bibtexing", tags)
            ))
        );
    }

    #[test]
    fn test_no_type_comment() {
        assert_eq!(
            no_type_comment(b"test@"),
            Ok((&b"@"[..], "test"))
        );
        assert_eq!(
            no_type_comment(b"test"),
            Ok((&b""[..], "test"))
        );
    }

    #[test]
    fn test_entry_with_type() {
        assert_eq!(
            entry_with_type(b"@Comment{test}"),
            Ok((&b""[..], Entry::Comment("test")))
        );

        let kv = KeyValue::new("key", vec![StringValueType::Str("value")]);
        assert_eq!(
            entry_with_type(b"@String{key=\"value\"}"),
            Ok((&b""[..], Entry::Variable(kv)))
        );

        assert_eq!(
            entry_with_type(b"@preamble{name # \"'s preamble\"}"),
            Ok((
                &b""[..],
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
            entry_with_type(bib_str),
            Ok((
                &b""[..],
                Entry::Bibliography("misc", "patashnik-bibtexing", tags)
            ))
        );
    }

    #[test]
    fn test_type_comment() {
        assert_eq!(
            type_comment(b"@Comment{test}"),
            Ok((&b""[..], Entry::Comment("test")))
        );
    }

    #[test]
    fn test_preamble() {
        assert_eq!(
            preamble(b"@preamble{my preamble}"),
            Ok((
                &b""[..],
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
            variable(b"@string{key=\"value\"}"),
            Ok((&b""[..], Entry::Variable(kv1)))
        );

        assert_eq!(
            variable(b"@string( key=\"value\" )"),
            Ok((&b""[..], Entry::Variable(kv2)))
        );

        assert_eq!(
            variable(b"@string( key=varone # vartwo)"),
            Ok((&b""[..], Entry::Variable(kv3)))
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
            variable_key_value_pair(b"key = varone # vartwo,"),
            Ok((&b","[..], kv))
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
            bibliography_entry(bib_str),
            Ok((
                &b""[..],
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
            bib_tags(tags_str),
            Ok((&b"}"[..], result))
        );
    }

    #[test]
    fn test_abbreviation_string() {
        assert_eq!(
            abbreviation_string(b"var # \"string\","),
            Ok((
                &b","[..],
                vec![
                    StringValueType::Abbreviation("var"),
                    StringValueType::Str("string"),
                ]
            ))
        );
        assert_eq!(
            abbreviation_string(b"\"string\" # var,"),
            Ok((
                &b","[..],
                vec![
                    StringValueType::Str("string"),
                    StringValueType::Abbreviation("var"),
                ]
            ))
        );
        assert_eq!(
            abbreviation_string(b"string # var,"),
            Ok((
                &b","[..],
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
            abbreviation_only(b" var "),
            Ok((
                &b""[..],
                vec![StringValueType::Abbreviation("var")]
            ))
        );
    }

    #[test]
    fn test_abbreviation_with_underscore() {
        assert_eq!(
            abbreviation_only(b" IEEE_J_CAD "),
            Ok((
                &b""[..],
                vec![StringValueType::Abbreviation("IEEE_J_CAD")]
            ))
        );
    }

    #[test]
    fn test_bracketed_string() {
        assert_eq!(
            bracketed_string(b"{ test }"),
            Ok((&b""[..], "test"))
        );
        assert_eq!(
            bracketed_string(b"{ {test} }"),
            Ok((&b""[..], "{test}"))
        );
        assert!(bracketed_string(b"{ @{test} }").is_err());
    }

    #[test]
    fn test_quoted_string() {
        assert_eq!(
            quoted_string(b"\"test\""),
            Ok((&b""[..], "test"))
        );
        assert_eq!(
            quoted_string(b"\"test \""),
            Ok((&b""[..], "test "))
        );
        assert_eq!(
            quoted_string(b"\"{\"test\"}\""),
            Ok((&b""[..], "{\"test\"}"))
        );
        assert_eq!(
            quoted_string(b"\"A {bunch {of} braces {in}} title\""),
            Ok((&b""[..], "A {bunch {of} braces {in}} title"))
        );
        assert_eq!(
            quoted_string(b"\"Simon {\"}the {saint\"} Templar\""),
            Ok((&b""[..], "Simon {\"}the {saint\"} Templar"))
        );
    }

    #[test]
    fn test_variable_with_underscore() {
        let kv1 = KeyValue::new("IEEE_J_ANNE", vec![StringValueType::Str("{IEEE} Trans. Aeronaut. Navig. Electron.")]);

        assert_eq!(
            variable(
                b"@string{IEEE_J_ANNE       = \"{IEEE} Trans. Aeronaut. Navig. Electron.\"}"
            ),
            Ok((&b""[..], Entry::Variable(kv1)))
        );
    }

    #[test]
    fn test_dashes_in_variables_are_supported() {
        let kv1 = KeyValue::new(
            "IEEE_J_B-ME",
            vec![StringValueType::Str("{IEEE} Trans. Bio-Med. Eng.")]
        );

        assert_eq!(
            variable(
                b"@STRING{IEEE_J_B-ME       = \"{IEEE} Trans. Bio-Med. Eng.\"}"
            ),
            Ok((&b""[..], Entry::Variable(kv1)))
        );

        assert_eq!(
            abbreviation_only(b" IEE_j_B-ME "),
            Ok((
                &b""[..],
                vec![StringValueType::Abbreviation("IEE_j_B-ME")]
            ))
        );
    }

    #[test]
    fn malformed_entries_produce_errors() {
        let bib_str = b"
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
            !entries(bib_str).is_ok(),
            "Malformed entries list parsed correctly"
        );
    }
}
