//! W3C SPARQL 1.0 + 1.1 test suite runner.
//!
//! Runs all SPARQL evaluation test suites from tests/w3c/sparql/sparql10/
//! and tests/w3c/sparql/sparql11/ that have SRX (SPARQL XML Results) outputs.
//! Tests load Turtle data, execute SPARQL queries, and compare results
//! against expected SRX output.

use std::collections::HashMap;
use std::time::Instant;

const SPARQL10_DIR: &str = "../tests/w3c/sparql/sparql10";
const SPARQL11_DIR: &str = "../tests/w3c/sparql/sparql11";

// ---------------------------------------------------------------------------
// Simple SRX (SPARQL XML Results) parser
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SrxValue {
    Uri(String),
    Literal {
        value: String,
        lang: Option<String>,
        datatype: Option<String>,
    },
    BNode(String),
    #[allow(dead_code)]
    Unbound,
}

#[derive(Debug)]
struct SrxResults {
    variables: Vec<String>,
    rows: Vec<HashMap<String, SrxValue>>,
    /// For ASK results: Some(true/false). For SELECT results: None.
    boolean: Option<bool>,
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
    let mut in_boolean = false;
    let mut boolean_result: Option<bool> = None;
    let mut literal_lang: Option<String> = None;
    let mut literal_datatype: Option<String> = None;
    let mut text_buf = String::new();

    let mut pos = 0;
    let bytes = xml.as_bytes();

    while pos < bytes.len() {
        if bytes[pos] == b'<' {
            let _tag_start = pos;
            pos += 1;
            let is_closing = pos < bytes.len() && bytes[pos] == b'/';
            if is_closing {
                pos += 1;
            }
            let name_start = pos;
            while pos < bytes.len()
                && bytes[pos] != b'>'
                && bytes[pos] != b' '
                && bytes[pos] != b'/'
            {
                pos += 1;
            }
            let tag_name = std::str::from_utf8(&bytes[name_start..pos]).unwrap_or("");

            let mut attrs = HashMap::new();
            while pos < bytes.len() && bytes[pos] != b'>' && bytes[pos] != b'/' {
                while pos < bytes.len() && bytes[pos] == b' ' {
                    pos += 1;
                }
                if pos >= bytes.len() || bytes[pos] == b'>' || bytes[pos] == b'/' {
                    break;
                }
                let attr_start = pos;
                while pos < bytes.len()
                    && bytes[pos] != b'='
                    && bytes[pos] != b'>'
                    && bytes[pos] != b' '
                {
                    pos += 1;
                }
                let attr_name =
                    std::str::from_utf8(&bytes[attr_start..pos]).unwrap_or("").to_string();
                if pos < bytes.len() && bytes[pos] == b'=' {
                    pos += 1;
                    if pos < bytes.len() && bytes[pos] == b'"' {
                        pos += 1;
                        let val_start = pos;
                        while pos < bytes.len() && bytes[pos] != b'"' {
                            pos += 1;
                        }
                        let val = std::str::from_utf8(&bytes[val_start..pos])
                            .unwrap_or("")
                            .to_string();
                        attrs.insert(attr_name, val);
                        if pos < bytes.len() {
                            pos += 1;
                        }
                    }
                }
            }

            let _is_self_closing = pos < bytes.len() && bytes[pos] == b'/';
            while pos < bytes.len() && bytes[pos] != b'>' {
                pos += 1;
            }
            if pos < bytes.len() {
                pos += 1;
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
                "boolean" if !is_closing => {
                    in_boolean = true;
                    text_buf.clear();
                }
                "boolean" if is_closing => {
                    in_boolean = false;
                    boolean_result = Some(text_buf.trim() == "true");
                    text_buf.clear();
                }
                _ => {}
            }
        } else {
            if in_uri || in_literal || in_bnode || in_boolean {
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

    Ok(SrxResults { variables, rows, boolean: boolean_result })
}

// ---------------------------------------------------------------------------
// SPARQL query result comparison
// ---------------------------------------------------------------------------

fn display_to_srx(s: &str) -> SrxValue {
    if s.starts_with('<') && s.ends_with('>') {
        SrxValue::Uri(s[1..s.len() - 1].to_string())
    } else if s.starts_with("_:") {
        SrxValue::BNode(s[2..].to_string())
    } else if s.starts_with('"') {
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
        if after.starts_with('@') {
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

fn results_match(actual: &rdf_wasm::sparql::QueryResult, expected: &SrxResults) -> bool {
    // ASK query: compare boolean results
    if let Some(expected_bool) = expected.boolean {
        return actual.boolean == Some(expected_bool);
    }

    if actual.rows.len() != expected.rows.len() {
        return false;
    }

    let actual_rows: Vec<HashMap<String, SrxValue>> = actual
        .rows
        .iter()
        .map(|row| {
            let mut map = HashMap::new();
            for (i, var) in actual.variables.iter().enumerate() {
                if let Some(Some(val)) = row.get(i) {
                    map.insert(var.clone(), display_to_srx(val));
                }
            }
            map
        })
        .collect();

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
            (Some(a_val), Some(e_val)) => match (a_val, e_val) {
                (SrxValue::BNode(_), SrxValue::BNode(_)) => continue,
                _ if a_val == e_val => continue,
                (
                    SrxValue::Literal {
                        value: av,
                        lang: al,
                        datatype: ad,
                    },
                    SrxValue::Literal {
                        value: ev,
                        lang: el,
                        datatype: ed,
                    },
                ) => {
                    if av != ev || al != el {
                        return false;
                    }
                    let a_dt = ad
                        .as_deref()
                        .unwrap_or("http://www.w3.org/2001/XMLSchema#string");
                    let e_dt = ed
                        .as_deref()
                        .unwrap_or("http://www.w3.org/2001/XMLSchema#string");
                    if a_dt != e_dt {
                        return false;
                    }
                }
                _ => return false,
            },
            _ => return false,
        }
    }
    true
}

// ---------------------------------------------------------------------------
// TTL Result Set parser (rs:ResultSet format)
// ---------------------------------------------------------------------------

/// Parse a W3C SPARQL result set in Turtle format (rs:ResultSet vocabulary).
/// Uses our own Turtle parser to parse the result file.
fn parse_ttl_results(ttl: &str) -> Result<SrxResults, String> {
    let graph = rdf_wasm::turtle::parse(ttl).map_err(|e| format!("TTL result parse: {e}"))?;
    let triples = graph.triples();

    let rs_var = "http://www.w3.org/2001/sw/DataAccess/tests/result-set#resultVariable";
    let rs_solution = "http://www.w3.org/2001/sw/DataAccess/tests/result-set#solution";
    let rs_binding = "http://www.w3.org/2001/sw/DataAccess/tests/result-set#binding";
    let rs_variable = "http://www.w3.org/2001/sw/DataAccess/tests/result-set#variable";
    let rs_value = "http://www.w3.org/2001/sw/DataAccess/tests/result-set#value";

    // Extract variables
    let variables: Vec<String> = triples
        .iter()
        .filter(|t| t.p.as_str() == rs_var)
        .filter_map(|t| match &t.o {
            rdf_wasm::RdfTerm::Literal(l) => Some(l.lexical_form.clone()),
            _ => None,
        })
        .collect();

    // Extract solutions: each rs:solution points to a bnode that has rs:binding entries
    let solution_bnodes: Vec<u64> = triples
        .iter()
        .filter(|t| t.p.as_str() == rs_solution)
        .filter_map(|t| match &t.o {
            rdf_wasm::RdfTerm::BNode(b) => Some(b.id()),
            _ => None,
        })
        .collect();

    let mut rows = Vec::new();
    for sol_id in &solution_bnodes {
        let mut row = HashMap::new();

        // Find binding bnodes for this solution
        let binding_ids: Vec<u64> = triples
            .iter()
            .filter(|t| {
                t.p.as_str() == rs_binding
                    && matches!(&t.s, rdf_wasm::Subject::BNode(b) if b.id() == *sol_id)
            })
            .filter_map(|t| match &t.o {
                rdf_wasm::RdfTerm::BNode(b) => Some(b.id()),
                _ => None,
            })
            .collect();

        for bind_id in &binding_ids {
            // Find variable name and value for this binding bnode
            let var_name: Option<String> = triples
                .iter()
                .find(|t| {
                    t.p.as_str() == rs_variable
                        && matches!(&t.s, rdf_wasm::Subject::BNode(b) if b.id() == *bind_id)
                })
                .and_then(|t| match &t.o {
                    rdf_wasm::RdfTerm::Literal(l) => Some(l.lexical_form.clone()),
                    _ => None,
                });

            let value: Option<SrxValue> = triples
                .iter()
                .find(|t| {
                    t.p.as_str() == rs_value
                        && matches!(&t.s, rdf_wasm::Subject::BNode(b) if b.id() == *bind_id)
                })
                .map(|t| match &t.o {
                    rdf_wasm::RdfTerm::Iri(i) => SrxValue::Uri(i.as_str().to_string()),
                    rdf_wasm::RdfTerm::BNode(_) => SrxValue::BNode("ttl_bnode".to_string()),
                    rdf_wasm::RdfTerm::Literal(l) => {
                        let dt = l.datatype.as_str();
                        SrxValue::Literal {
                            value: l.lexical_form.clone(),
                            lang: l.lang_tag.clone(),
                            datatype: if dt == "http://www.w3.org/2001/XMLSchema#string" {
                                None
                            } else if l.lang_tag.is_some() {
                                None
                            } else {
                                Some(dt.to_string())
                            },
                        }
                    }
                });

            if let (Some(var), Some(val)) = (var_name, value) {
                row.insert(var, val);
            }
        }

        rows.push(row);
    }

    Ok(SrxResults { variables, rows, boolean: None })
}

// ---------------------------------------------------------------------------
// Generic test runner (works for both 1.0 and 1.1)
// ---------------------------------------------------------------------------

struct TestCase {
    name: String,
    data_file: String,
    query_file: String,
    result_file: String,
}

/// Parse a manifest.ttl to extract QueryEvaluationTest cases.
/// Accepts .srx and .ttl result files.
fn extract_test_cases_from(manifest_path: &str) -> Vec<TestCase> {
    let manifest = match std::fs::read_to_string(manifest_path) {
        Ok(s) => s,
        Err(_) => return Vec::new(),
    };

    let mut tests = Vec::new();
    let lines: Vec<&str> = manifest.lines().collect();
    let mut i = 0;
    let mut current_name = String::new();
    let mut current_query = String::new();
    let mut current_data = String::new();

    while i < lines.len() {
        let line = lines[i].trim();

        // Test entry: :name rdf:type mf:QueryEvaluationTest
        // Also handle "a mf:QueryEvaluationTest"
        if (line.contains("rdf:type") || line.contains(" a "))
            && line.contains("QueryEvaluationTest")
        {
            if let Some(name) = line.split_whitespace().next() {
                current_name = name
                    .trim_start_matches(':')
                    .trim_start_matches('<')
                    .trim_end_matches('>')
                    .to_string();
                if current_name.starts_with('#') {
                    current_name = current_name[1..].to_string();
                }
            }
        }

        if line.contains("qt:query") {
            if let Some(s) = extract_angle_bracket(line, "qt:query") {
                current_query = s;
            }
        }

        if line.contains("qt:data") {
            if let Some(s) = extract_angle_bracket(line, "qt:data") {
                current_data = s;
            }
        }

        if line.contains("mf:result") {
            if let Some(s) = extract_angle_bracket(line, "mf:result") {
                // Accept both .srx and .ttl result files
                if (s.ends_with(".srx") || s.ends_with(".ttl"))
                    && !current_query.is_empty()
                    && !current_data.is_empty()
                {
                    tests.push(TestCase {
                        name: current_name.clone(),
                        data_file: current_data.clone(),
                        query_file: current_query.clone(),
                        result_file: s,
                    });
                }
                current_name.clear();
                current_query.clear();
                current_data.clear();
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

struct SuiteResult {
    name: String,
    passed: usize,
    failed: usize,
    skipped: usize,
    failures: Vec<String>,
    duration_ms: u128,
}

fn run_suite(base_dir: &str, suite_name: &str) -> SuiteResult {
    let manifest_path = format!("{}/{}/manifest.ttl", base_dir, suite_name);
    let tests = extract_test_cases_from(&manifest_path);
    let start = Instant::now();
    let mut passed = 0;
    let mut failed = 0;
    let mut skipped = 0;
    let mut failures = Vec::new();

    for test in &tests {
        let data_path = format!("{}/{}/{}", base_dir, suite_name, test.data_file);
        let query_path = format!("{}/{}/{}", base_dir, suite_name, test.query_file);
        let result_path = format!("{}/{}/{}", base_dir, suite_name, test.result_file);

        let data_content = match std::fs::read_to_string(&data_path) {
            Ok(s) => s,
            Err(_) => {
                skipped += 1;
                continue;
            }
        };

        let graph = match rdf_wasm::turtle::parse(&data_content) {
            Ok(g) => g,
            Err(e) => {
                failures.push(format!("{}: Turtle parse error: {e}", test.name));
                failed += 1;
                continue;
            }
        };

        let query = match std::fs::read_to_string(&query_path) {
            Ok(s) => s,
            Err(_) => {
                skipped += 1;
                continue;
            }
        };

        let result_content = match std::fs::read_to_string(&result_path) {
            Ok(s) => s,
            Err(_) => {
                skipped += 1;
                continue;
            }
        };

        let expected = if test.result_file.ends_with(".srx") {
            match parse_srx(&result_content) {
                Ok(r) => r,
                Err(e) => {
                    failures.push(format!("{}: SRX parse error: {e}", test.name));
                    failed += 1;
                    continue;
                }
            }
        } else {
            match parse_ttl_results(&result_content) {
                Ok(r) => r,
                Err(e) => {
                    failures.push(format!("{}: TTL result parse error: {e}", test.name));
                    failed += 1;
                    continue;
                }
            }
        };

        let actual = match rdf_wasm::sparql::execute(&graph, &query) {
            Ok(r) => r,
            Err(e) => {
                failures.push(format!("{}: SPARQL error: {e}", test.name));
                failed += 1;
                continue;
            }
        };

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

    SuiteResult {
        name: suite_name.to_string(),
        passed,
        failed,
        skipped,
        failures,
        duration_ms: start.elapsed().as_millis(),
    }
}

fn print_scorecard(title: &str, results: &[SuiteResult]) {
    let mut total_passed = 0;
    let mut total_failed = 0;
    let mut total_skipped = 0;
    let mut total_ms: u128 = 0;

    eprintln!("\n╔═══════════════════════════════════════════════════════════╗");
    eprintln!("║  {title:<55} ║");
    eprintln!("╠═══════════════════════════════════════════════════════════╣");

    for r in results {
        let total = r.passed + r.failed;
        let pct = if total > 0 {
            (r.passed as f64 / total as f64) * 100.0
        } else {
            0.0
        };
        eprintln!(
            "║ {:<20} {:>3}/{:<3} ({:>5.1}%) skip={:<3} {:>4}ms ║",
            r.name, r.passed, total, pct, r.skipped, r.duration_ms
        );
        total_passed += r.passed;
        total_failed += r.failed;
        total_skipped += r.skipped;
        total_ms += r.duration_ms;
    }

    let total = total_passed + total_failed;
    let pct = if total > 0 {
        (total_passed as f64 / total as f64) * 100.0
    } else {
        0.0
    };
    eprintln!("╠═══════════════════════════════════════════════════════════╣");
    eprintln!(
        "║ {:<20} {:>3}/{:<3} ({:>5.1}%) skip={:<3} {:>4}ms ║",
        "TOTAL", total_passed, total, pct, total_skipped, total_ms
    );
    eprintln!("╚═══════════════════════════════════════════════════════════╝");

    // Print failures grouped by suite
    let all_failures: Vec<_> = results
        .iter()
        .filter(|r| !r.failures.is_empty())
        .flat_map(|r| r.failures.iter().map(move |f| format!("[{}] {f}", r.name)))
        .collect();
    if !all_failures.is_empty() {
        eprintln!("\nFailures ({}):", all_failures.len());
        for f in all_failures.iter().take(300) {
            eprintln!("  {f}");
        }
        if all_failures.len() > 30 {
            eprintln!("  ... and {} more", all_failures.len() - 30);
        }
    }
}

// ===========================================================================
// SPARQL 1.0 — all suites with SRX results
// ===========================================================================

const SPARQL10_SUITES: &[&str] = &[
    "algebra",
    "basic",
    "bnode-coreference",
    "boolean-effective-value",
    "bound",
    "cast",
    "dataset",
    "distinct",
    "expr-builtin",
    "expr-equals",
    "expr-ops",
    "i18n",
    "open-world",
    "optional",
    "optional-filter",
    "reduced",
    "regex",
    "solution-seq",
    "sort",
    "triple-match",
    "type-promotion",
];

#[test]
fn w3c_sparql10_full_scorecard() {
    let results: Vec<SuiteResult> = SPARQL10_SUITES
        .iter()
        .map(|s| run_suite(SPARQL10_DIR, s))
        .collect();
    print_scorecard("W3C SPARQL 1.0 Full Scorecard", &results);
}

// Individual suite tests for CI granularity
#[test]
fn w3c_sparql10_basic() {
    let r = run_suite(SPARQL10_DIR, "basic");
    eprintln!("basic: {}/{} passed", r.passed, r.passed + r.failed);
}

#[test]
fn w3c_sparql10_algebra() {
    let r = run_suite(SPARQL10_DIR, "algebra");
    eprintln!("algebra: {}/{} passed", r.passed, r.passed + r.failed);
}

#[test]
fn w3c_sparql10_triple_match() {
    let r = run_suite(SPARQL10_DIR, "triple-match");
    eprintln!("triple-match: {}/{} passed", r.passed, r.passed + r.failed);
}

#[test]
fn w3c_sparql10_optional() {
    let r = run_suite(SPARQL10_DIR, "optional");
    eprintln!("optional: {}/{} passed", r.passed, r.passed + r.failed);
}

#[test]
fn w3c_sparql10_sort() {
    let r = run_suite(SPARQL10_DIR, "sort");
    eprintln!("sort: {}/{} passed", r.passed, r.passed + r.failed);
}

// ===========================================================================
// SPARQL 1.1 — all query evaluation suites with SRX results
// ===========================================================================

const SPARQL11_SUITES: &[&str] = &[
    "aggregates",
    "bind",
    "bindings",
    "cast",
    "exists",
    "functions",
    "grouping",
    "negation",
    "project-expression",
    "property-path",
    "subquery",
];

#[test]
fn w3c_sparql11_full_scorecard() {
    let results: Vec<SuiteResult> = SPARQL11_SUITES
        .iter()
        .map(|s| run_suite(SPARQL11_DIR, s))
        .collect();
    print_scorecard("W3C SPARQL 1.1 Query Scorecard", &results);
}

// Individual 1.1 suite tests
#[test]
fn w3c_sparql11_bind() {
    let r = run_suite(SPARQL11_DIR, "bind");
    eprintln!("bind: {}/{} passed", r.passed, r.passed + r.failed);
}

#[test]
fn w3c_sparql11_functions() {
    let r = run_suite(SPARQL11_DIR, "functions");
    eprintln!("functions: {}/{} passed", r.passed, r.passed + r.failed);
}

#[test]
fn w3c_sparql11_aggregates() {
    let r = run_suite(SPARQL11_DIR, "aggregates");
    eprintln!("aggregates: {}/{} passed", r.passed, r.passed + r.failed);
}

#[test]
fn w3c_sparql11_negation() {
    let r = run_suite(SPARQL11_DIR, "negation");
    eprintln!("negation: {}/{} passed", r.passed, r.passed + r.failed);
}

#[test]
fn w3c_sparql11_property_path() {
    let r = run_suite(SPARQL11_DIR, "property-path");
    eprintln!(
        "property-path: {}/{} passed",
        r.passed,
        r.passed + r.failed
    );
}

// ===========================================================================
// Combined scorecard (1.0 + 1.1)
// ===========================================================================

#[test]
fn w3c_sparql_combined_scorecard() {
    let start = Instant::now();

    let mut all_results = Vec::new();

    eprintln!("\n--- SPARQL 1.0 suites ---");
    for s in SPARQL10_SUITES {
        all_results.push(run_suite(SPARQL10_DIR, s));
    }
    eprintln!("--- SPARQL 1.1 suites ---");
    for s in SPARQL11_SUITES {
        let mut r = run_suite(SPARQL11_DIR, s);
        r.name = format!("1.1/{}", r.name);
        all_results.push(r);
    }

    let total_time = start.elapsed().as_millis();
    print_scorecard("W3C SPARQL Combined Scorecard (1.0 + 1.1)", &all_results);
    eprintln!("Total wall time: {}ms", total_time);
}
