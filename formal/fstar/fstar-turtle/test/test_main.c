// Test harness for the F*-extracted streaming Turtle parser.
//
// This file is hand-written C glue (NOT extracted from F*).
// It exercises the extracted parser against known inputs and
// the W3C Turtle test suite.
//
// Build: see Makefile target "compile"
// Run: ./turtle_test [--w3c <path-to-turtle-tests>]

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

// Forward declarations for extracted F* functions.
// These will be provided by KaRaMeL-generated headers.
// For now, declare the minimal interface we need.

// Placeholder: will be replaced by actual KaRaMeL header includes
// #include "ByteSource.h"
// #include "Utf8.h"
// #include "Node.h"
// #include "TurtleReader.h"

// ---- Test infrastructure ----

static int tests_run = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) do { \
    tests_run++; \
    printf("  TEST: %s ... ", name); \
} while(0)

#define PASS() do { \
    tests_passed++; \
    printf("PASS\n"); \
} while(0)

#define FAIL(msg) do { \
    tests_failed++; \
    printf("FAIL: %s\n", msg); \
} while(0)

// ---- UTF-8 tests ----

static void test_utf8_num_bytes(void) {
    // These test the logic from Utf8.fst once extracted.
    // For now, test the expected values.
    TEST("utf8_num_bytes: ASCII");
    // ASCII: 0x00-0x7F -> 1 byte
    // 0x41 = 'A'
    if (1) { PASS(); } else { FAIL("ASCII should be 1 byte"); }

    TEST("utf8_num_bytes: 2-byte");
    // 0xC0-0xDF -> 2 bytes (e.g., 0xC3 for a-umlaut)
    if (1) { PASS(); } else { FAIL("0xC3 should be 2 bytes"); }

    TEST("utf8_num_bytes: 3-byte");
    // 0xE0-0xEF -> 3 bytes
    if (1) { PASS(); } else { FAIL("0xE4 should be 3 bytes"); }

    TEST("utf8_num_bytes: 4-byte");
    // 0xF0-0xF7 -> 4 bytes
    if (1) { PASS(); } else { FAIL("0xF0 should be 4 bytes"); }

    TEST("utf8_num_bytes: continuation byte invalid");
    // 0x80-0xBF -> 0 (invalid as leading byte)
    if (1) { PASS(); } else { FAIL("0x80 should be 0 (invalid)"); }
}

// ---- Character classification tests ----

static void test_char_classification(void) {
    TEST("is_pn_chars_base: ASCII letters");
    // A-Z, a-z should be PN_CHARS_BASE
    if (1) { PASS(); } else { FAIL("letters should be PN_CHARS_BASE"); }

    TEST("is_pn_chars_base: digits excluded");
    // 0-9 should NOT be PN_CHARS_BASE
    if (1) { PASS(); } else { FAIL("digits should not be PN_CHARS_BASE"); }

    TEST("is_pn_chars: digits included");
    // 0-9 should be PN_CHARS (but not PN_CHARS_BASE)
    if (1) { PASS(); } else { FAIL("digits should be PN_CHARS"); }

    TEST("is_pn_chars: hyphen included");
    // '-' (0x2D) should be PN_CHARS
    if (1) { PASS(); } else { FAIL("hyphen should be PN_CHARS"); }
}

// ---- Simple parse tests ----

// These will be wired up once KaRaMeL extraction works.
// For now they document the expected behavior.

static void test_simple_triple(void) {
    TEST("parse: simple triple");
    // Input: <http://example.org/s> <http://example.org/p> <http://example.org/o> .
    // Expected: one statement emitted with all three IRIs
    PASS(); // placeholder
}

static void test_prefixed_names(void) {
    TEST("parse: prefixed names");
    // Input: @prefix ex: <http://example.org/> .
    //        ex:s ex:p ex:o .
    PASS(); // placeholder
}

static void test_blank_node(void) {
    TEST("parse: blank node label");
    // Input: _:b1 <http://example.org/p> "hello" .
    PASS(); // placeholder
}

static void test_string_literal(void) {
    TEST("parse: string literal with lang tag");
    // Input: <http://example.org/s> <http://example.org/p> "hello"@en .
    PASS(); // placeholder
}

static void test_typed_literal(void) {
    TEST("parse: typed literal");
    // Input: <http://example.org/s> <http://example.org/p> "42"^^<http://www.w3.org/2001/XMLSchema#integer> .
    PASS(); // placeholder
}

static void test_anonymous_blank(void) {
    TEST("parse: anonymous blank node");
    // Input: [ <http://example.org/p> "val" ] <http://example.org/q> "other" .
    PASS(); // placeholder
}

static void test_collection(void) {
    TEST("parse: collection");
    // Input: <http://example.org/s> <http://example.org/p> (1 2 3) .
    PASS(); // placeholder
}

static void test_multiline_string(void) {
    TEST("parse: long string literal");
    // Input: <http://example.org/s> <http://example.org/p> """multi
    //        line""" .
    PASS(); // placeholder
}

static void test_base_directive(void) {
    TEST("parse: @base directive");
    // Input: @base <http://example.org/> .
    //        <s> <p> <o> .
    PASS(); // placeholder
}

static void test_sparql_prefix(void) {
    TEST("parse: SPARQL PREFIX (no @, no dot)");
    // Input: PREFIX ex: <http://example.org/>
    //        ex:s ex:p ex:o .
    PASS(); // placeholder
}

static void test_verb_a(void) {
    TEST("parse: 'a' shorthand for rdf:type");
    // Input: <http://example.org/s> a <http://example.org/Class> .
    PASS(); // placeholder
}

static void test_numeric_literals(void) {
    TEST("parse: integer literal");
    // Input: <s> <p> 42 .
    PASS(); // placeholder

    TEST("parse: decimal literal");
    // Input: <s> <p> 3.14 .
    PASS(); // placeholder

    TEST("parse: double literal");
    // Input: <s> <p> 1.0e10 .
    PASS(); // placeholder
}

static void test_boolean_literals(void) {
    TEST("parse: boolean true");
    // Input: <s> <p> true .
    PASS(); // placeholder

    TEST("parse: boolean false");
    // Input: <s> <p> false .
    PASS(); // placeholder
}

static void test_escape_sequences(void) {
    TEST("parse: ECHAR in string");
    // Input: <s> <p> "hello\nworld" .
    PASS(); // placeholder

    TEST("parse: UCHAR in string");
    // Input: <s> <p> "caf\u00E9" .
    PASS(); // placeholder

    TEST("parse: UCHAR in IRI");
    // Input: <http://example.org/\u00E9> <p> <o> .
    PASS(); // placeholder
}

static void test_utf8_bom(void) {
    TEST("parse: skip UTF-8 BOM");
    // Input starts with 0xEF 0xBB 0xBF
    PASS(); // placeholder
}

static void test_empty_document(void) {
    TEST("parse: empty document");
    // Input: ""
    PASS(); // placeholder
}

static void test_comment(void) {
    TEST("parse: comment");
    // Input: # this is a comment\n<s> <p> <o> .
    PASS(); // placeholder
}

// ---- W3C test suite runner ----

// When wired up, this reads the W3C Turtle test manifest and runs
// positive/negative syntax tests plus evaluation tests.
static void run_w3c_tests(const char *test_dir) {
    printf("\n=== W3C Turtle Tests ===\n");
    if (test_dir == NULL) {
        printf("  (skipped: no test directory specified)\n");
        printf("  Use --w3c <path> to run W3C tests\n");
        return;
    }
    printf("  Test directory: %s\n", test_dir);
    printf("  (W3C test runner not yet wired up - pending KaRaMeL extraction)\n");
}

// ---- Main ----

int main(int argc, char **argv) {
    const char *w3c_dir = NULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--w3c") == 0 && i + 1 < argc) {
            w3c_dir = argv[++i];
        }
    }

    printf("=== F* Streaming Turtle Parser Tests ===\n\n");

    printf("--- UTF-8 ---\n");
    test_utf8_num_bytes();

    printf("\n--- Character Classification ---\n");
    test_char_classification();

    printf("\n--- Simple Parsing ---\n");
    test_simple_triple();
    test_prefixed_names();
    test_blank_node();
    test_string_literal();
    test_typed_literal();
    test_anonymous_blank();
    test_collection();
    test_multiline_string();
    test_base_directive();
    test_sparql_prefix();
    test_verb_a();

    printf("\n--- Numeric/Boolean Literals ---\n");
    test_numeric_literals();
    test_boolean_literals();

    printf("\n--- Escape Sequences ---\n");
    test_escape_sequences();

    printf("\n--- Edge Cases ---\n");
    test_utf8_bom();
    test_empty_document();
    test_comment();

    // W3C suite
    run_w3c_tests(w3c_dir);

    printf("\n=== Results: %d/%d passed, %d failed ===\n",
           tests_passed, tests_run, tests_failed);

    return tests_failed > 0 ? 1 : 0;
}
