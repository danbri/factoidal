//! W3C RDF 1.1 N-Triples Test Suite
//!
//! Runs the official W3C test cases from tests/w3c/rdf/rdf11/rdf-n-triples/
//! against our N-Triples parser.

use rdf_wasm::ntriples;

const TEST_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/w3c/rdf/rdf11/rdf-n-triples");

// =========================================================================
//  Helper: load a test file
// =========================================================================

fn load_test(name: &str) -> String {
    let path = format!("{TEST_DIR}/{name}");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("Failed to read {path}: {e}"))
}

// =========================================================================
//  Positive syntax tests — must parse without error
// =========================================================================

macro_rules! positive_test {
    ($name:ident, $file:expr) => {
        #[test]
        fn $name() {
            let input = load_test($file);
            match ntriples::parse(&input) {
                Ok(g) => {
                    // Verify roundtrip: serialize and re-parse
                    let nt = g.to_ntriples();
                    if !nt.is_empty() {
                        match ntriples::parse(&nt) {
                            Ok(g2) => assert_eq!(
                                g.len(),
                                g2.len(),
                                "Roundtrip changed triple count for {}: {} → {}",
                                $file,
                                g.len(),
                                g2.len()
                            ),
                            Err(e) => panic!("Roundtrip parse failed for {}: {e}", $file),
                        }
                    }
                }
                Err(e) => panic!("Should parse {}: {e}", $file),
            }
        }
    };
}

// -- File structure tests --
positive_test!(nt_syntax_file_01, "nt-syntax-file-01.nt");
positive_test!(nt_syntax_file_02, "nt-syntax-file-02.nt");
positive_test!(nt_syntax_file_03, "nt-syntax-file-03.nt");

// -- URI tests --
positive_test!(nt_syntax_uri_01, "nt-syntax-uri-01.nt");
positive_test!(nt_syntax_uri_02, "nt-syntax-uri-02.nt");
positive_test!(nt_syntax_uri_03, "nt-syntax-uri-03.nt");
positive_test!(nt_syntax_uri_04, "nt-syntax-uri-04.nt");

// -- String literal tests --
positive_test!(nt_syntax_string_01, "nt-syntax-string-01.nt");
positive_test!(nt_syntax_string_02, "nt-syntax-string-02.nt");
positive_test!(nt_syntax_string_03, "nt-syntax-string-03.nt");

// -- String escape tests --
positive_test!(nt_syntax_str_esc_01, "nt-syntax-str-esc-01.nt");
positive_test!(nt_syntax_str_esc_02, "nt-syntax-str-esc-02.nt");
positive_test!(nt_syntax_str_esc_03, "nt-syntax-str-esc-03.nt");

// -- Blank node tests --
positive_test!(nt_syntax_bnode_01, "nt-syntax-bnode-01.nt");
positive_test!(nt_syntax_bnode_02, "nt-syntax-bnode-02.nt");
positive_test!(nt_syntax_bnode_03, "nt-syntax-bnode-03.nt");

// -- Datatype tests --
positive_test!(nt_syntax_datatypes_01, "nt-syntax-datatypes-01.nt");
positive_test!(nt_syntax_datatypes_02, "nt-syntax-datatypes-02.nt");

// -- Submission tests --
positive_test!(nt_syntax_subm_01, "nt-syntax-subm-01.nt");

// -- Literal content tests --
positive_test!(literal, "literal.nt");
positive_test!(langtagged_string, "langtagged_string.nt");
positive_test!(lantag_with_subtag, "lantag_with_subtag.nt");
positive_test!(literal_with_squote, "literal_with_squote.nt");
positive_test!(literal_with_2_squotes, "literal_with_2_squotes.nt");
positive_test!(literal_with_2_dquotes, "literal_with_2_dquotes.nt");
positive_test!(literal_with_dquote, "literal_with_dquote.nt");
positive_test!(literal_with_numeric_escape4, "literal_with_numeric_escape4.nt");
positive_test!(literal_with_numeric_escape8, "literal_with_numeric_escape8.nt");
positive_test!(literal_with_character_tabulation, "literal_with_CHARACTER_TABULATION.nt");
positive_test!(literal_with_backspace, "literal_with_BACKSPACE.nt");
positive_test!(literal_with_line_feed, "literal_with_LINE_FEED.nt");
positive_test!(literal_with_carriage_return, "literal_with_CARRIAGE_RETURN.nt");
positive_test!(literal_with_form_feed, "literal_with_FORM_FEED.nt");
positive_test!(literal_with_reverse_solidus, "literal_with_REVERSE_SOLIDUS.nt");
positive_test!(literal_with_reverse_solidus2, "literal_with_REVERSE_SOLIDUS2.nt");
positive_test!(literal_true, "literal_true.nt");
positive_test!(literal_false, "literal_false.nt");
positive_test!(literal_all_punctuation, "literal_all_punctuation.nt");
positive_test!(literal_with_utf8_boundaries, "literal_with_UTF8_boundaries.nt");
positive_test!(literal_ascii_boundaries, "literal_ascii_boundaries.nt");
positive_test!(literal_all_controls, "literal_all_controls.nt");
positive_test!(minimal_whitespace, "minimal_whitespace.nt");
positive_test!(comment_following_triple, "comment_following_triple.nt");

// =========================================================================
//  Negative syntax tests — must reject with error
// =========================================================================

macro_rules! negative_test {
    ($name:ident, $file:expr) => {
        #[test]
        fn $name() {
            let input = load_test($file);
            assert!(
                ntriples::parse(&input).is_err(),
                "Should reject {}: parsed successfully but shouldn't have",
                $file
            );
        }
    };
}

// -- Bad URI tests --
negative_test!(nt_syntax_bad_uri_01, "nt-syntax-bad-uri-01.nt");
negative_test!(nt_syntax_bad_uri_02, "nt-syntax-bad-uri-02.nt");
negative_test!(nt_syntax_bad_uri_03, "nt-syntax-bad-uri-03.nt");
negative_test!(nt_syntax_bad_uri_04, "nt-syntax-bad-uri-04.nt");
negative_test!(nt_syntax_bad_uri_05, "nt-syntax-bad-uri-05.nt");
negative_test!(nt_syntax_bad_uri_06, "nt-syntax-bad-uri-06.nt");
negative_test!(nt_syntax_bad_uri_07, "nt-syntax-bad-uri-07.nt");
negative_test!(nt_syntax_bad_uri_08, "nt-syntax-bad-uri-08.nt");
negative_test!(nt_syntax_bad_uri_09, "nt-syntax-bad-uri-09.nt");

// -- Bad prefix/base (N-Triples doesn't support @prefix/@base) --
negative_test!(nt_syntax_bad_prefix_01, "nt-syntax-bad-prefix-01.nt");
negative_test!(nt_syntax_bad_base_01, "nt-syntax-bad-base-01.nt");

// -- Bad blank node tests --
negative_test!(nt_syntax_bad_bnode_01, "nt-syntax-bad-bnode-01.nt");
negative_test!(nt_syntax_bad_bnode_02, "nt-syntax-bad-bnode-02.nt");

// -- Bad structure tests --
negative_test!(nt_syntax_bad_struct_01, "nt-syntax-bad-struct-01.nt");
negative_test!(nt_syntax_bad_struct_02, "nt-syntax-bad-struct-02.nt");

// -- Bad language tag --
negative_test!(nt_syntax_bad_lang_01, "nt-syntax-bad-lang-01.nt");

// -- Bad escape sequences --
negative_test!(nt_syntax_bad_esc_01, "nt-syntax-bad-esc-01.nt");
negative_test!(nt_syntax_bad_esc_02, "nt-syntax-bad-esc-02.nt");
negative_test!(nt_syntax_bad_esc_03, "nt-syntax-bad-esc-03.nt");

// -- Bad string syntax --
negative_test!(nt_syntax_bad_string_01, "nt-syntax-bad-string-01.nt");
negative_test!(nt_syntax_bad_string_02, "nt-syntax-bad-string-02.nt");
negative_test!(nt_syntax_bad_string_03, "nt-syntax-bad-string-03.nt");
negative_test!(nt_syntax_bad_string_04, "nt-syntax-bad-string-04.nt");
negative_test!(nt_syntax_bad_string_05, "nt-syntax-bad-string-05.nt");
negative_test!(nt_syntax_bad_string_06, "nt-syntax-bad-string-06.nt");
negative_test!(nt_syntax_bad_string_07, "nt-syntax-bad-string-07.nt");

// -- Bad numeric syntax --
negative_test!(nt_syntax_bad_num_01, "nt-syntax-bad-num-01.nt");
negative_test!(nt_syntax_bad_num_02, "nt-syntax-bad-num-02.nt");
negative_test!(nt_syntax_bad_num_03, "nt-syntax-bad-num-03.nt");
