# Measuring Performance & Coverage

## SPARQL Coverage Metrics

### Running the Scorecard

```bash
cargo test w3c_sparql_combined_scorecard -- --nocapture 2>&1 | grep "║"
```

This prints a formatted table with pass/total/rate per suite plus timing.

### Tracking Progress Over Time

Record scorecard snapshots after each improvement round:

| Date | Total | Rate | Key Changes |
|------|-------|------|-------------|
| 2026-03-05 | 32/436 | 7.3% | Initial baseline |
| 2026-03-06 | 93/436 | 21.3% | Literals, UNION, BEV, regex, arithmetic |

### Per-Suite Breakdown Script

```bash
# Extract just pass counts per suite
cargo test w3c_sparql_combined_scorecard -- --nocapture 2>&1 \
  | grep "║" | grep -v "═" | grep "/" \
  | awk -F'║' '{print $2}' | sed 's/^  *//'
```

## Execution Time Measurement

### Debug Build Timing

```bash
# Full test suite timing
time cargo test 2>&1 | tail -1

# SPARQL-specific timing
cargo test w3c_sparql_combined_scorecard -- --nocapture 2>&1 | grep "TOTAL"
```

### Release Build Comparison

```bash
cargo test --release w3c_sparql_combined_scorecard -- --nocapture 2>&1 | grep "TOTAL"
```

Expected: 2-5x faster than debug build.

### Per-Suite Timing

The scorecard output includes per-suite timing in milliseconds. Watch for:
- regex suite: can be slow due to regex compilation (currently ~80ms)
- functions suite: many tests, ~50ms
- Most suites: <20ms each

## Code Size Metrics

```bash
# Lines of code per module
wc -l rdf-wasm/src/*.rs

# Current counts:
# rdf.rs:       345  (core types)
# ntriples.rs:  365  (N-Triples parser)
# turtle.rs:   1198  (Turtle parser)
# sparql.rs:   1438+ (SPARQL engine, growing)
# wasm_api.rs:  194  (WASM bindings)
# lib.rs:        ~50 (module declarations)
```

### F* Specification Size

```bash
wc -l formal/fstar/rdfcore11.fstar.txt
# Current: 241 lines
```

Ratio: ~241 lines F* spec for ~3540 lines Rust = 6.8% formal coverage by LOC. Target: increase F* coverage as Rust stabilizes.

## W3C Compliance Tracking

| Spec | Current | Target | Notes |
|------|---------|--------|-------|
| N-Triples 1.1 | 72/72 (100%) | Maintain | Complete |
| Turtle 1.1 | 223/223 (100%) | Maintain | Complete |
| SPARQL 1.0 | ~80/234 | 150/234 | Focus on parser fixes |
| SPARQL 1.1 | ~13/202 | 50/202 | Need new features |

## Regression Detection

After any change:
1. Run `cargo test` — all 172 must pass
2. Run scorecard — total must not decrease
3. If a previously passing test now fails, investigate before committing

### Automated Regression Check

```bash
# Save baseline
cargo test w3c_sparql_combined_scorecard -- --nocapture 2>&1 | grep "TOTAL" > /tmp/baseline.txt

# After changes
cargo test w3c_sparql_combined_scorecard -- --nocapture 2>&1 | grep "TOTAL" > /tmp/current.txt

# Compare
diff /tmp/baseline.txt /tmp/current.txt
```

## Memory and Binary Size

```bash
# WASM binary size
ls -lh docs/pkg/rdf_wasm_bg.wasm

# Debug binary size
ls -lh target/debug/deps/rdf_wasm-*

# Check for bloat
cargo bloat --release --crates 2>/dev/null || echo "Install: cargo install cargo-bloat"
```
