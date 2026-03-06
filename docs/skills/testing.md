# Testing the Factoidal Engine

## Test Infrastructure

### Running Tests

```bash
# Full suite (172 Rust tests, ~0.5s)
cd rdf-wasm && cargo test

# SPARQL scorecard only (32 suites, 436 individual tests)
cargo test w3c_sparql_combined_scorecard -- --nocapture

# Specific suite
cargo test w3c_sparql10_regex -- --nocapture
cargo test w3c_sparql11_full_scorecard -- --nocapture

# Large graph integration tests
cargo test sparql_large_graph -- --nocapture

# Individual module tests
cargo test rdf_tests -- --nocapture
cargo test w3c_ntriples -- --nocapture
cargo test w3c_turtle -- --nocapture
```

### Test File Locations

| Test File | What it tests | Count |
|-----------|--------------|-------|
| `rdf-wasm/tests/rdf_tests.rs` | Core types: Iri, Literal, Triple, Graph | 25 |
| `rdf-wasm/tests/w3c_ntriples.rs` | W3C N-Triples 1.1 compliance | 72 |
| `rdf-wasm/tests/w3c_turtle.rs` | W3C Turtle 1.1 compliance (pos+neg+eval) | 3 (223 individual) |
| `rdf-wasm/tests/w3c_sparql.rs` | W3C SPARQL 1.0+1.1 test harness | 13 (436 individual) |
| `rdf-wasm/tests/sparql_large_graph.rs` | Multi-hop joins, 117-triple graph | 17 |
| `rdf-wasm/src/lib.rs` (unit tests) | Parser and engine unit tests | 42 |

### W3C Test Data Sources

```
tests/w3c/rdf/rdf11/rdf-n-triples/    # N-Triples positive/negative tests
tests/w3c/rdf/rdf11/rdf-turtle/        # Turtle positive/negative/eval tests
tests/w3c/sparql/sparql10/             # SPARQL 1.0 suites (21 directories)
tests/w3c/sparql/sparql11/             # SPARQL 1.1 suites (11 directories)
```

The `tests/w3c/` directory is a git submodule pointing to `github.com/w3c/rdf-tests`.

## W3C SPARQL Test Harness Architecture

The test harness in `w3c_sparql.rs` works as follows:

1. For each suite directory, scan for `.rq` query files
2. Load the corresponding data file (`.ttl` or `.nt`)
3. Load the expected result (`.srx` XML or `.ttl` result set)
4. Parse data with our Turtle/N-Triples parser
5. Execute query with our SPARQL engine
6. Compare results (order-insensitive for non-ORDER-BY queries)

### Result Format Support

- **SRX** (SPARQL Results XML): Parsed with a custom XML reader
- **TTL** (rs:ResultSet vocabulary): Parsed using our own Turtle parser, extracting `rs:solution`, `rs:binding`, `rs:variable`, `rs:value` triples

### Adding New Tests

To add a new test:
1. Place `.rq`, `.ttl`, and `.srx`/`.ttl` files in the appropriate suite directory
2. The harness auto-discovers all `.rq` files in the suite directory
3. File naming convention: `{test-name}.rq`, `{test-name}.srx`, `{data-name}.ttl`

## Test Quality Checklist

When making SPARQL engine changes:

- [ ] All 172 Rust tests pass (`cargo test`)
- [ ] No regressions in W3C SPARQL scorecard (check combined total)
- [ ] Large graph integration tests pass (17 multi-hop queries)
- [ ] N-Triples roundtrip still works (72/72)
- [ ] Turtle compliance unchanged (223/223)
- [ ] Check for new warnings (`cargo test 2>&1 | grep warning`)

## Known Test Gaps

- No WASM-specific tests (browser integration via `docs/tests.html` only)
- No fuzz testing yet (Turtle parser is a prime candidate)
- No benchmark suite (only wall-clock timing in scorecard)
- No property-based testing (QuickCheck/proptest for roundtrip properties)
- No concurrency tests (single-threaded only currently)
