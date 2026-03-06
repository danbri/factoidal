# Validating Correctness

## Validation Layers

### Layer 1: F* Formal Specification

The F* spec in `formal/fstar/rdfcore11.fstar.txt` defines the authoritative semantics for:
- Well-formed IRIs (`wf_iri`: non-empty, contains `:`)
- Well-formed literals (`wf_literal`: lang tag ↔ rdf:langString)
- Graph operations (add, remove, union with set semantics)
- Triple pattern matching (SPARQL BGP semantics)

**Proofs completed:**
- `lemma_add_no_dup`: Adding a triple guarantees membership
- `lemma_remove_absent`: Removing a triple guarantees absence
- `lemma_empty_no_bnodes`: Empty graph has no blank nodes

**Validation approach:** The Rust code in `rdf.rs` must produce identical behavior to the F* spec for all specified operations. This is currently validated by shared test cases, not by automated extraction.

### Layer 2: W3C Test Suites

The gold standard for correctness. Our compliance:

| Spec | Coverage | Status |
|------|----------|--------|
| N-Triples 1.1 | 72/72 (100%) | Complete |
| Turtle 1.1 | 223/223 (100%) | Complete |
| SPARQL 1.0+1.1 | 93/436 (21.3%) | In progress |

### Layer 3: Integration Tests

The large graph test (`sparql_large_graph.rs`) validates real-world query patterns:
- Multi-hop joins across 117 triples
- OPTIONAL with missing data
- DISTINCT deduplication
- ORDER BY + LIMIT/OFFSET
- FILTER with various expressions

### Layer 4: Roundtrip Verification

N-Triples roundtrip: parse → serialize → parse → compare. Verified in unit tests.
Turtle: parse → N-Triples serialize → parse → compare. Used in W3C eval tests.

## F* ↔ Rust Alignment Checks

### Current Alignment Status

| F* Construct | Rust Implementation | Verified By |
|-------------|--------------------|-----------|
| `wf_iri` | `Iri::new()` | Unit tests (reject empty, require `:`) |
| `wf_literal` | `Literal::new()` | Unit tests (lang↔langString) |
| `graph_add` (set dedup) | `RdfGraph::add()` | Unit tests + W3C tests |
| `graph_remove` | `RdfGraph::remove()` | Unit tests |
| `mem_triple` | `RdfGraph::contains()` | Unit tests |
| `find_by_subject` | `RdfGraph::find_by_subject()` | Unit tests |
| `find_by_predicate` | `RdfGraph::find_by_predicate()` | Unit tests |
| `graph_union` | Not in Rust yet | Pending |

### Checking Alignment

When modifying `rdf.rs`:
1. Read corresponding F* spec section
2. Verify Rust behavior matches F* postconditions
3. Add test cases that exercise the F* lemma's scenario
4. Example: F* says `mem_triple t (graph_add t g)` = true → Rust test adds triple then checks contains

### Future: Automated Alignment via Hax

[Hax](https://github.com/hacspec/hax) can translate Rust → F* for verification. When ready:
1. Annotate Rust code with `#[hax::ensures(...)]` attributes
2. Extract F* from annotated Rust
3. Verify extracted F* against our hand-written spec
4. Any divergence = bug in Rust or spec

## Invariants to Monitor

### Graph Invariants
- No duplicate triples (set semantics) — `graph_add` deduplicates
- All IRIs well-formed (non-empty, contain `:`) — enforced by `Iri::new()`
- All literals well-formed (lang↔langString) — enforced by `Literal::new()`
- BNode IDs globally unique — atomic u64 counter

### Parser Invariants
- Every valid N-Triples document roundtrips cleanly
- Every valid Turtle document produces correct triples
- Parser never panics on malformed input (returns Result/Error)

### SPARQL Invariants
- Empty graph → empty result for any pattern query
- SELECT DISTINCT never has duplicate rows
- ORDER BY produces monotonically ordered results
- LIMIT N returns at most N rows
- OFFSET skips exactly the right number

## Validation Hooks

### Pre-commit
Before committing SPARQL changes, always run:
```bash
cargo test && echo "ALL PASS"
```

### Periodic Full Validation
```bash
# Run everything with timing
time cargo test 2>&1 | tail -5

# Check scorecard hasn't regressed
cargo test w3c_sparql_combined_scorecard -- --nocapture 2>&1 | grep "TOTAL"
```

### After Major Changes
- Re-run W3C Turtle eval tests (these parse+serialize+compare)
- Re-run N-Triples roundtrip tests
- Re-run large graph integration tests
- Check WASM build still works: `cd rdf-wasm && ./build.sh`
