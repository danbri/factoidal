# Improving the SPARQL Engine

## Current Architecture

The SPARQL engine (`rdf-wasm/src/sparql.rs`) is a hand-written recursive descent parser + evaluator. No parser generator. This keeps dependencies minimal but means every grammar production must be coded by hand.

### Components

1. **Tokenizer** (`tokenize()`): Splits query string into tokens, handling strings, IRIs, operators
2. **Parser** (`Parser::parse_query()`): Builds `ParsedQuery` from tokens
3. **Evaluator** (`evaluate_clauses()`): Executes query against `RdfGraph`
4. **Filter evaluator** (`eval_filter()`): Evaluates FILTER expressions

## Improvement Strategy: Highest Impact First

### Tier 1: Parser Fixes (unlock many tests with small code changes)

| Fix | Tests Unlockable | Effort | Status |
|-----|-----------------|--------|--------|
| Literal values in patterns | ~40 | Medium | Done |
| FILTER without parens | ~25 | Low | Done |
| Boolean effective value | ~7 | Low | Done |
| Numeric literals | ~14 | Low | Done |
| Semicolons in patterns | ~5 | Low | Done |
| UNION support | ~10 | Medium | Done |
| `a` keyword (rdf:type) | ~5 | Low | Done |
| Arithmetic in FILTER | ~6 | Low | Done |
| BASE IRI resolution | ~5 | Low | Pending |
| List patterns `( )` | ~4 | Medium | Pending |
| REDUCED modifier | ~2 | Low | Pending |
| Comma in object lists | ~2 | Low | Pending |

### Tier 2: New Features (require new evaluator logic)

| Feature | Tests Unlockable | Effort | Status |
|---------|-----------------|--------|--------|
| BIND clause | 10 | Medium | Pending |
| VALUES clause | 11 | Medium | Pending |
| Sub-SELECT | 9 | High | Pending |
| SELECT expressions | 7 | Medium | Pending |
| SPARQL 1.1 functions (STRLEN, SUBSTR, etc.) | 74 | Medium | Pending |
| Aggregates (COUNT, SUM, GROUP BY) | 35 | High | Pending |
| Property paths | 29 | High | Pending |
| NOT EXISTS / EXISTS | 6 | Medium | Partially done |
| MINUS | 11 | Medium | Pending |
| Casting functions | 13 | Medium | Pending |

### Tier 3: Advanced (require architectural changes)

| Feature | Tests | Effort |
|---------|-------|--------|
| Named graphs (GRAPH keyword) | ~10 | High |
| CONSTRUCT queries | N/A | Medium |
| ASK / DESCRIBE | N/A | Low |
| Federated queries (SERVICE) | N/A | High |

## Debugging Failed Tests

### Find why a specific test fails

```bash
# Run scorecard with full failure details
cargo test w3c_sparql_combined_scorecard -- --nocapture 2>&1 | grep "\[suite-name\]"

# Common failure patterns:
# "SPARQL error: Unexpected token in pattern: 'X'" → Parser doesn't handle token X
# "result mismatch (actual=N rows, expected=M rows)" → Evaluator bug
# "SPARQL error: Unknown comparison operator: 'X'" → FILTER parsing issue
# "SPARQL error: Expected 'X', got 'Y'" → Parser structural issue
```

### Examine the actual test query

```bash
cat tests/w3c/sparql/sparql10/{suite}/{test-name}.rq
cat tests/w3c/sparql/sparql10/{suite}/{test-name}.srx  # expected results
```

### Test a fix quickly

```bash
# Run just the suite you're working on
cargo test w3c_sparql10_{suite} -- --nocapture
```

## Common Parser Patterns to Handle

### Property lists (semicolons)
```sparql
?s foaf:name ?name ; foaf:age ?age .
# Expands to: ?s foaf:name ?name . ?s foaf:age ?age .
```

### Object lists (commas)
```sparql
?s foaf:knows ?a , ?b , ?c .
# Expands to: ?s foaf:knows ?a . ?s foaf:knows ?b . ?s foaf:knows ?c .
```

### Boolean effective value
```sparql
FILTER(?x)           # true if ?x is bound and non-empty/non-zero
FILTER(bound(?x))    # true if ?x is bound
FILTER(str(?x))      # true if STR(?x) is non-empty
```

### UNION
```sparql
{ ?x foaf:name ?n } UNION { ?x rdfs:label ?n }
```

### Nested OPTIONAL
```sparql
{ ?x foaf:name ?n }
OPTIONAL { ?x foaf:age ?a }
OPTIONAL { ?x foaf:email ?e }
```

## Testing Workflow for Engine Changes

1. **Read the failing test** query and expected results
2. **Identify the parser/evaluator gap**
3. **Make the minimal fix** in `sparql.rs`
4. **Run `cargo test`** — all 172 must pass
5. **Run scorecard** — total must increase (or at least not decrease)
6. **Commit with scorecard delta** in commit message
7. **Push to branch**

## Performance Considerations

- The evaluator uses nested loops (O(n*m) for each pattern against graph)
- For large graphs (>1000 triples), this becomes noticeable
- Index structures (subject index, predicate index) would help
- Current 117-triple test graph runs 17 queries in ~30ms — acceptable
- Regex compilation is cached per FILTER evaluation — could cache across queries
