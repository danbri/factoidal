//! W3C SPARQL test suite runner.
//!
//! Runs SPARQL 1.0 test suites from tests/w3c/sparql/sparql10/.
//! Tests load Turtle data, execute SPARQL queries, and compare results
//! against expected SRX (SPARQL XML Results) output.

use std::collections::HashMap;

const SPARQL10_DIR: &str = "../tests/w3c/sparql/sparql10";

// ---------------------------------------------------------------------------
// Simple SRX (SPARQL XML Results) parser
// ---------------------------------------------------------------------------

/// A single result row: variable name -> SrxValue
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SrxValue {
    Uri(String),
    Literal { value: String, lang: Option<String>, datatype: Option<String> },
    BNode(String),
    Unbound,
}

#[derive(Debug)]
struct SrxResults {
    variables: Vec<String>,
    rows: Vec<HashMap<String, SrxValue>>,
}

fn parse_srx(xml: &str) -> Result<SrxResults, String> {
    let mut variables = Vec::new();
    let mut rows = Vec::new();
    let mut current_row: Option<HashMap<String, SrxValue>> = None;
    let mut current_var: Option<String> = None;
    let mut current_value: Option<SrxValue> = None;
    let mut in_uri = false;
    let mut in_literal = false;
    let mut in_bnode = false;
    let mut literal_lang: Option<String> = None;
    let mut literal_datatype: Option<String> = None;
    let mut text_buf = String::new();

    // Very simple XML-like parser (not a full XML parser)
    let mut pos = 0;
    let bytes = xml.as_bytes();

    while pos < bytes.len() {
        if bytes[pos] == b'<' {
            // Found a tag
            let tag_start = pos;
            pos += 1;
            let is_closing = pos < bytes.len() && bytes[pos] == b'/';
            if is_closing {
                pos += 1;
            }
            let name_start = pos;
            while pos < bytes.len() && bytes[pos] != b'>' && bytes[pos] != b' ' && bytes[pos] != b'/' {
                pos += 1;
            }
            let tag_name = std::str::from_utf8(&bytes[name_start..pos]).unwrap_or("");

            // Collect attributes
            let mut attrs = HashMap::new();
            while pos < bytes.len() && bytes[pos] != b'>' && bytes[pos] != b'/' {
                // Skip whitespace
                while pos < bytes.len() && bytes[pos] == b' ' {
                    pos += 1;
                }
                if pos >= bytes.len() || bytes[pos] == b'>' || bytes[pos] == b'/' {
                    break;
                }
                // Read attr name
                let attr_start = pos;
                while pos < bytes.len() && bytes[pos] != b'=' && bytes[pos] != b'>' && bytes[pos] != b' ' {
                    pos += 1;
                }
                let attr_name = std::str::from_utf8(&bytes[attr_start..pos]).unwrap_or("").to_string();
                if pos < bytes.len() && bytes[pos] == b'=' {
                    pos += 1;
                    if pos < bytes.len() && bytes[pos] == b'"' {
                        pos += 1;
                        let val_start = pos;
                        while pos < bytes.len() && bytes[pos] != b'"' {
                            pos += 1;
                        }
                        let val = std::str::from_utf8(&bytes[val_start..pos]).unwrap_or("").to_string();
                        attrs.insert(attr_name, val);
                        if pos < bytes.len() {
                            pos += 1; // skip closing quote
                        }
                    }
                }
            }

            let is_self_closing = pos < bytes.len() && bytes[pos] == b'/';
            // Skip to end of tag
            while pos < bytes.len() && bytes[pos] != b'>' {
                pos += 1;
            }
            if pos < bytes.len() {
                pos += 1; // skip '>'
            }

            match tag_name {
                "variable" if !is_closing => {
                    if let Some(name) = attrs.get("name") {
                        variables.push(name.clone());
                    }
                }
                "result" if !is_closing => {
                    current_row = Some(HashMap::new());
                }
                "result" if is_closing => {
                    if let Some(row) = current_row.take() {
                        rows.push(row);
                    }
                }
                "binding" if !is_closing => {
                    current_var = attrs.get("name").cloned();
                    text_buf.clear();
                }
                "binding" if is_closing => {
                    if let (Some(ref mut row), Some(ref var)) = (&mut current_row, &current_var) {
                        if let Some(val) = current_value.take() {
                            row.insert(var.clone(), val);
                        }
                    }
                    current_var = None;
                }
                "uri" if !is_closing => {
                    in_uri = true;
                    text_buf.clear();
                }
                "uri" if is_closing => {
                    in_uri = false;
                    current_value = Some(SrxValue::Uri(text_buf.clone()));
                    text_buf.clear();
                }
                "literal" if !is_closing => {
                    in_literal = true;
                    literal_lang = attrs.get("xml:lang").cloned();
                    literal_datatype = attrs.get("datatype").cloned();
                    text_buf.clear();
                }
                "literal" if is_closing => {
                    in_literal = false;
                    current_value = Some(SrxValue::Literal {
                        value: text_buf.clone(),
                        lang: literal_lang.take(),
                        datatype: literal_datatype.take(),
                    });
                    text_buf.clear();
                }
                "bnode" if !is_closing => {
                    in_bnode = true;
                    text_buf.clear();
                }
                "bnode" if is_closing => {
                    in_bnode = false;
                    current_value = Some(SrxValue::BNode(text_buf.clone()));
                    text_buf.clear();
                }
                _ => {}
            }
        } else {
            // Text content
            if in_uri || in_literal || in_bnode {
                // Handle XML entities
                if bytes[pos] == b'&' {
                    let entity_start = pos;
                    while pos < bytes.len() && bytes[pos] != b';' {
                        pos += 1;
                    }
                    if pos < bytes.len() {
                        pos += 1;
                    }
                    let entity = std::str::from_utf8(&bytes[entity_start..pos]).unwrap_or("");
                    match entity {
                        "&amp;" => text_buf.push('&'),
                        "&lt;" => text_buf.push('<'),
                        "&gt;" => text_buf.push('>'),
                        "&quot;" => text_buf.push('"'),
                        "&apos;" => text_buf.push('\''),
                        _ => text_buf.push_str(entity),
                    }
                } else {
                    text_buf.push(bytes[pos] as char);
                    pos += 1;
                }
            } else {
                pos += 1;
            }
        }
    }

    Ok(SrxResults { variables, rows })
}

// ---------------------------------------------------------------------------
// SPARQL query result comparison
// ---------------------------------------------------------------------------

/// Convert an engine display string to an SrxValue for comparison.
/// Display format: `<iri>`, `_:bN`, `"lex"`, `"lex"@lang`, `"lex"^^<dt>`
fn display_to_srx(s: &str) -> SrxValue {
    if s.starts_with('<') && s.ends_with('>') {
        SrxValue::Uri(s[1..s.len() - 1].to_string())
    } else if s.starts_with("_:") {
        SrxValue::BNode(s[2..].to_string())
    } else if s.starts_with('"') {
        // Parse literal
        // Find the closing quote (handling escaped quotes)
        let bytes = s.as_bytes();
        let mut i = 1;
        while i < bytes.len() {
            if bytes[i] == b'\\' {
                i += 2;
            } else if bytes[i] == b'"' {
                break;
            } else {
                i += 1;
            }
        }
        let lexical = unescape_ntriples(&s[1..i]);
        let after = &s[i + 1..];
        if after.starts_with("@") {
            SrxValue::Literal {
                value: lexical,
                lang: Some(after[1..].to_string()),
                datatype: None,
            }
        } else if after.starts_with("^^<") && after.ends_with('>') {
            let dt = &after[3..after.len() - 1];
            SrxValue::Literal {
                value: lexical,
                lang: None,
                datatype: if dt == "http://www.w3.org/2001/XMLSchema#string" {
                    None
                } else {
                    Some(dt.to_string())
                },
            }
        } else {
            SrxValue::Literal {
                value: lexical,
                lang: None,
                datatype: None,
            }
        }
    } else {
        // Fallback: treat as literal value
        SrxValue::Literal {
            value: s.to_string(),
            lang: None,
            datatype: None,
        }
    }
}

fn unescape_ntriples(s: &str) -> String {
    let mut result = String::new();
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => result.push('\n'),
                Some('r') => result.push('\r'),
                Some('t') => result.push('\t'),
                Some('"') => result.push('"'),
                Some('\\') => result.push('\\'),
                Some(other) => {
                    result.push('\\');
                    result.push(other);
                }
                None => result.push('\\'),
            }
        } else {
            result.push(c);
        }
    }
    result
}

/// Compare result sets, ignoring order and bnode labels.
fn results_match(
    actual: &rdf_wasm::sparql::QueryResult,
    expected: &SrxResults,
) -> bool {
    if actual.rows.len() != expected.rows.len() {
        return false;
    }

    // Convert actual results to SrxValue maps
    let actual_rows: Vec<HashMap<String, SrxValue>> = actual.rows.iter().map(|row| {
        let mut map = HashMap::new();
        for (i, var) in actual.variables.iter().enumerate() {
            if let Some(Some(val)) = row.get(i) {
                map.insert(var.clone(), display_to_srx(val));
            }
        }
        map
    }).collect();

    let mut expected_matched = vec![false; expected.rows.len()];
    for actual_row in &actual_rows {
        let mut found = false;
        for (i, expected_row) in expected.rows.iter().enumerate() {
            if expected_matched[i] {
                continue;
            }
            if row_matches(actual_row, expected_row, &expected.variables) {
                expected_matched[i] = true;
                found = true;
                break;
            }
        }
        if !found {
            return false;
        }
    }
    true
}

fn row_matches(
    actual: &HashMap<String, SrxValue>,
    expected: &HashMap<String, SrxValue>,
    variables: &[String],
) -> bool {
    for var in variables {
        let a = actual.get(var);
        let e = expected.get(var);
        match (a, e) {
            (None, None) => continue,
            (None, Some(SrxValue::Unbound)) => continue,
            (Some(SrxValue::Unbound), None) => continue,
            (Some(a_val), Some(e_val)) => {
                match (a_val, e_val) {
                    (SrxValue::BNode(_), SrxValue::BNode(_)) => continue,
                    _ if a_val == e_val => continue,
                    (
                        SrxValue::Literal { value: av, lang: al, datatype: ad },
                        SrxValue::Literal { value: ev, lang: el, datatype: ed },
                    ) => {
                        if av != ev || al != el {
                            return false;
                        }
                        let a_dt = ad.as_deref().unwrap_or("http://www.w3.org/2001/XMLSchema#string");
                        let e_dt = ed.as_deref().unwrap_or("http://www.w3.org/2001/XMLSchema#string");
                        if a_dt != e_dt {
                            return false;
                        }
                    }
                    _ => return false,
                }
            }
            _ => return false,
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Test runner
// ---------------------------------------------------------------------------

struct TestCase {
    name: String,
    data_file: String,
    query_file: String,
    result_file: String,
}

/// Parse a manifest.ttl to extract test cases (simplified).
fn extract_test_cases(suite_dir: &str) -> Vec<TestCase> {
    let manifest_path = format!("{}/{}/manifest.ttl", SPARQL10_DIR, suite_dir);
    let manifest = match std::fs::read_to_string(&manifest_path) {
        Ok(s) => s,
        Err(_) => return Vec::new(),
    };

    let mut tests = Vec::new();

    // Simple regex-style extraction of test entries
    // Looking for patterns like:
    //   mf:action [ qt:query <file.rq> ; qt:data <file.ttl> ] ;
    //   mf:result <file.srx> ;
    let lines: Vec<&str> = manifest.lines().collect();
    let mut i = 0;
    let mut current_name = String::new();
    let mut current_query = String::new();
    let mut current_data = String::new();
    let mut current_result = String::new();

    while i < lines.len() {
        let line = lines[i].trim();

        // Test name: :name rdf:type mf:QueryEvaluationTest
        if line.contains("rdf:type") && line.contains("QueryEvaluationTest") {
            // Extract name
            if let Some(name) = line.split_whitespace().next() {
                current_name = name.trim_start_matches(':').trim_start_matches('<').trim_end_matches('>').to_string();
                if current_name.starts_with('#') {
                    current_name = current_name[1..].to_string();
                }
            }
        }

        // Query file
        if line.contains("qt:query") {
            if let Some(s) = extract_angle_bracket(line, "qt:query") {
                current_query = s;
            }
        }

        // Data file
        if line.contains("qt:data") {
            if let Some(s) = extract_angle_bracket(line, "qt:data") {
                current_data = s;
            }
        }

        // Result file
        if line.contains("mf:result") {
            if let Some(s) = extract_angle_bracket(line, "mf:result") {
                current_result = s.clone();
                // Only include tests with .srx results for now
                if current_result.ends_with(".srx") && !current_query.is_empty() && !current_data.is_empty() {
                    tests.push(TestCase {
                        name: current_name.clone(),
                        data_file: current_data.clone(),
                        query_file: current_query.clone(),
                        result_file: current_result.clone(),
                    });
                }
                current_name.clear();
                current_query.clear();
                current_data.clear();
                current_result.clear();
            }
        }

        i += 1;
    }

    tests
}

fn extract_angle_bracket(line: &str, after: &str) -> Option<String> {
    if let Some(idx) = line.find(after) {
        let rest = &line[idx + after.len()..];
        if let Some(start) = rest.find('<') {
            if let Some(end) = rest[start + 1..].find('>') {
                return Some(rest[start + 1..start + 1 + end].to_string());
            }
        }
    }
    None
}

fn run_sparql_suite(suite_dir: &str) -> (usize, usize, usize, Vec<String>) {
    let tests = extract_test_cases(suite_dir);
    let mut passed = 0;
    let mut failed = 0;
    let mut skipped = 0;
    let mut failures = Vec::new();

    for test in &tests {
        let data_path = format!("{}/{}/{}", SPARQL10_DIR, suite_dir, test.data_file);
        let query_path = format!("{}/{}/{}", SPARQL10_DIR, suite_dir, test.query_file);
        let result_path = format!("{}/{}/{}", SPARQL10_DIR, suite_dir, test.result_file);

        // Load data
        let data_content = match std::fs::read_to_string(&data_path) {
            Ok(s) => s,
            Err(_) => {
                skipped += 1;
                continue;
            }
        };

        // Parse Turtle data
        let graph = match rdf_wasm::turtle::parse(&data_content) {
            Ok(g) => g,
            Err(e) => {
                failures.push(format!("{}: Turtle parse error: {e}", test.name));
                failed += 1;
                continue;
            }
        };

        // Load query
        let query = match std::fs::read_to_string(&query_path) {
            Ok(s) => s,
            Err(_) => {
                skipped += 1;
                continue;
            }
        };

        // Load expected results
        let result_xml = match std::fs::read_to_string(&result_path) {
            Ok(s) => s,
            Err(_) => {
                skipped += 1;
                continue;
            }
        };

        let expected = match parse_srx(&result_xml) {
            Ok(r) => r,
            Err(e) => {
                failures.push(format!("{}: SRX parse error: {e}", test.name));
                failed += 1;
                continue;
            }
        };

        // Execute query
        let actual = match rdf_wasm::sparql::execute(&graph, &query) {
            Ok(r) => r,
            Err(e) => {
                failures.push(format!("{}: SPARQL error: {e}", test.name));
                failed += 1;
                continue;
            }
        };

        // Compare
        if results_match(&actual, &expected) {
            passed += 1;
        } else {
            failures.push(format!(
                "{}: result mismatch (actual={} rows, expected={} rows)",
                test.name,
                actual.rows.len(),
                expected.rows.len(),
            ));
            failed += 1;
        }
    }

    (passed, failed, skipped, failures)
}

// ---------------------------------------------------------------------------
// Test functions
// ---------------------------------------------------------------------------

#[test]
fn w3c_sparql10_basic() {
    let (passed, failed, skipped, failures) = run_sparql_suite("basic");
    eprintln!("\n=== W3C SPARQL 1.0: basic ===");
    eprintln!("Passed: {passed}, Failed: {failed}, Skipped: {skipped}");
    for f in &failures {
        eprintln!("  FAIL: {f}");
    }
    // Report but don't fail — we're measuring coverage
}

#[test]
fn w3c_sparql10_distinct() {
    let (passed, failed, skipped, failures) = run_sparql_suite("distinct");
    eprintln!("\n=== W3C SPARQL 1.0: distinct ===");
    eprintln!("Passed: {passed}, Failed: {failed}, Skipped: {skipped}");
    for f in &failures {
        eprintln!("  FAIL: {f}");
    }
}

#[test]
fn w3c_sparql10_regex() {
    let (passed, failed, skipped, failures) = run_sparql_suite("regex");
    eprintln!("\n=== W3C SPARQL 1.0: regex ===");
    eprintln!("Passed: {passed}, Failed: {failed}, Skipped: {skipped}");
    for f in &failures {
        eprintln!("  FAIL: {f}");
    }
}

#[test]
fn w3c_sparql10_expr_ops() {
    let (passed, failed, skipped, failures) = run_sparql_suite("expr-ops");
    eprintln!("\n=== W3C SPARQL 1.0: expr-ops ===");
    eprintln!("Passed: {passed}, Failed: {failed}, Skipped: {skipped}");
    for f in &failures {
        eprintln!("  FAIL: {f}");
    }
}

#[test]
fn w3c_sparql10_expr_builtin() {
    let (passed, failed, skipped, failures) = run_sparql_suite("expr-builtin");
    eprintln!("\n=== W3C SPARQL 1.0: expr-builtin ===");
    eprintln!("Passed: {passed}, Failed: {failed}, Skipped: {skipped}");
    for f in &failures {
        eprintln!("  FAIL: {f}");
    }
}

/// Summary test that runs all suites with SRX results and reports a scorecard.
#[test]
fn w3c_sparql10_scorecard() {
    let suites = ["basic", "distinct", "regex", "expr-ops", "expr-builtin"];
    let mut total_passed = 0;
    let mut total_failed = 0;
    let mut total_skipped = 0;
    let mut all_failures = Vec::new();

    eprintln!("\n╔══════════════════════════════════════════════╗");
    eprintln!("║      W3C SPARQL 1.0 Test Scorecard          ║");
    eprintln!("╠══════════════════════════════════════════════╣");

    for suite in &suites {
        let (p, f, s, failures) = run_sparql_suite(suite);
        let total = p + f;
        let pct = if total > 0 { (p as f64 / total as f64) * 100.0 } else { 0.0 };
        eprintln!("║ {suite:<15} {p:>3}/{total:<3} ({pct:>5.1}%)  skip={s:<3} ║");
        total_passed += p;
        total_failed += f;
        total_skipped += s;
        for fail in failures {
            all_failures.push(format!("[{suite}] {fail}"));
        }
    }

    let total = total_passed + total_failed;
    let pct = if total > 0 { (total_passed as f64 / total as f64) * 100.0 } else { 0.0 };
    eprintln!("╠══════════════════════════════════════════════╣");
    eprintln!("║ TOTAL:          {total_passed:>3}/{total:<3} ({pct:>5.1}%)  skip={total_skipped:<3} ║");
    eprintln!("╚══════════════════════════════════════════════╝");

    if !all_failures.is_empty() {
        eprintln!("\nFailures:");
        for f in &all_failures {
            eprintln!("  {f}");
        }
    }
}
