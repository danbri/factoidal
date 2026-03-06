# Validating Correctness

## The Verification Pipeline

The F* specs are **not documentation** — they are the source code for the verified WASM binary. Validation exists at multiple layers, all converging toward a single goal: **KaRaMeL-extracted verified WASM**.

```
Target:  F* Low* spec → F* typechecker → KaRaMeL → verified C/WASM → wasmsign2 + SLSA
Current: F* high-level spec → manual Rust translation → wasm-bindgen → WASM (unverified)
Bridge:  Rust + Hax annotations → extracted F* → verify against hand-written spec
```

## Validation Layers

### Layer 0: F* Specifications (primary deliverable)

The F* specs define the **authoritative semantics** and are the source for eventual KaRaMeL extraction:

- `formal/fstar/RDF.Graph.Executable.fst` — Core RDF types, graph operations, N-Triples serialization
- `formal/fstar/SPARQL11.Algebra.fst` — SPARQL 1.1 algebra, evaluation semantics, 40+ built-in functions
- Original textual specs: `rdfcore11.fstar.txt`, `sparql11.fstar.txt` (kept for reference)

**F* toolchain is installed and operational:**
```bash
# Activate F* environment
eval $(opam env --switch=fstar)

# Verify all specs
cd formal/fstar && make verify

# Verify a single module
fstar.exe RDF.Graph.Executable.fst
fstar.exe SPARQL11.Algebra.fst
```

Both modules currently verify: `All verification conditions discharged successfully`.

**Tooling:**
- `fstar.exe` 2025.12.15 (via `opam install fstar` on switch `fstar`)
- `z3-4.8.5` and `z3-4.13.3` at `/usr/local/bin/`
- `opam` with OCaml 4.14.1

**Proofs completed (all verified, zero admit() in RDF.Graph.Executable.fst):**
- `lemma_add_no_dup`: Adding a triple guarantees membership — **proved** via triple_eq reflexivity
- `lemma_remove_absent`: Removing a triple guarantees absence — **proved** by induction
- `lemma_empty_no_bnodes`: Empty graph has no blank nodes
- `lemma_incompatible_types`: Numeric vs plain literal comparison returns None
- `lemma_compare_reflexive`: Value equality is reflexive — **proved** by case analysis
- `lemma_compare_symmetric`: Value equality is symmetric — **proved** by case analysis
- `lemma_bind_preserves_existing`: BIND does not overwrite existing bindings — **proved**
- Equality reflexivity lemmas for subject, literal, rdf_term, triple — all **proved**

**Concrete implementations (formerly assume val):**
- `string_contains_colon`: implemented via `list_of_string` + recursive char scan
- `subject_eq`, `literal_eq`, `rdf_term_eq`: implemented by constructor pattern matching

**KaRaMeL readiness blockers:**
- Specs use high-level F* (not Low* subset) — KaRaMeL requires Low*
- Remaining `assume val` declarations are for string library functions (string_lt, substring, etc.) and well-known IRI constants — not equality/proof blockers

**When modifying F* specs:**
1. Consider Low* compatibility — avoid features that block KaRaMeL extraction
2. Keep specs aligned with Rust implementation (divergence = bug in one or the other)
3. Update the F* ↔ Rust correspondence table in CLAUDE.md

### Layer 1: F* ↔ Rust Alignment

The Rust code must produce identical behavior to the F* spec. This is currently validated by shared test cases. The alignment will become machine-checked once Hax integration lands.

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

**When modifying `rdf.rs`:**
1. Read corresponding F* spec section first
2. Verify Rust behavior matches F* postconditions
3. Add test cases that exercise the F* lemma's scenario
4. Ask: "could this be extracted from F* via KaRaMeL instead of written manually?"

### Layer 2: W3C Test Suites

The gold standard for behavioral correctness. These validate both the current Rust implementation and (eventually) the KaRaMeL-extracted WASM.

| Spec | Coverage | Status |
|------|----------|--------|
| N-Triples 1.1 | 72/72 (100%) | Complete |
| Turtle 1.1 | 223/223 (100%) | Complete |
| SPARQL 1.0+1.1 | 159/436 (36.5%) | In progress |

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

**F* spec target:** The roundtrip property `graph_isomorphic g (parse(serialize g))` is specified in `rdfcore11.fstar.txt` — proof pending, and a priority for Low* rewrite and KaRaMeL extraction (see ARCHITECTURE.md Phase 1).

## Future: Hax Integration (Rust → F* verification)

[Hax](https://github.com/hacspec/hax) translates Rust → F* for verification. This is the bridge between the current Rust implementation and the F* specs:

1. Annotate Rust code with `#[hax::ensures(...)]` attributes
2. Extract F* from annotated Rust
3. Verify extracted F* against our hand-written spec
4. Any divergence = bug in Rust or spec

**Monthly review item:** Check Hax project status for readiness (see `docs/skills/periodic-review.md`).

## Future: KaRaMeL Extraction (F* → verified WASM)

This is the **target architecture**. When ready:

1. Rewrite core F* specs in Low* subset
2. Set up KaRaMeL in CI: verify proofs → extract to C/WASM
3. Sign extracted WASM with wasmsign2 + Sigstore/cosign
4. Publish SLSA attestation binding binary to F* proof verification

**Precedents:**
- **HACL\*** — verified crypto, KaRaMeL-extracted to C/WASM, deployed in Firefox/Linux/mbedTLS
- **EverParse** — verified parsers extracted from F* specs, deployed in Windows Hyper-V
- **Benzaken et al.** — Coq-verified SQL algebra (adaptable to SPARQL)

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
Before committing changes, always run:
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
- **Check F* spec alignment:** read corresponding spec section, verify behavior matches
