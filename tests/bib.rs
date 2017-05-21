extern crate nom_bibtex;

use nom_bibtex::{Bibtex, Entry, BibliographyEntry};

const BIBDATA: &str = "
@misc{knuthwebsite,
    author    = \"Donald Knuth\",
    title     = \"Knuth: Computers and Typesetting\",
    url       = \"http://www-cs-faculty.stanford.edu/\\~{}uno/abcde.html\"
}

@string {
    key = \"value\"
}

some comments
";

#[test]
fn test_bibtex() {
    let biblio = BibliographyEntry::new("misc",
                                        "knuthwebsite",
                                        vec![
        ("author".into(), "Donald Knuth".into()),
        ("title".into(), "Knuth: Computers and Typesetting".into()),
        ("url".into(), "http://www-cs-faculty.stanford.edu/\\~{}uno/abcde.html".into())
    ]);
    assert_eq!(Bibtex::parse(BIBDATA).unwrap(),
               Bibtex::new(vec![Entry::Bibliography(biblio),
                                Entry::Variable("key".into(), "value".into()),
                                Entry::Comment("some comments".into())]));
}
