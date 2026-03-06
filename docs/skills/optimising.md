# Optimising the Engine

## Current Performance Profile

### Baseline Measurements (debug build, single-threaded)

| Test Suite | Tests | Time | Notes |
|-----------|-------|------|-------|
| Unit tests | 42 | 0.01s | Core types, parsers |
| Core RDF | 25 | 0.01s | Type validation |
| Large graph SPARQL | 17 | 0.03s | 117 triples, multi-hop |
| W3C N-Triples | 72 | 0.02s | Parse all test files |
| W3C SPARQL | 13 harness | 0.40s | 436 individual (I/O heavy) |
| W3C Turtle | 3 harness | 0.07s | 223 individual |
| **Total** | **172** | **~0.55s** | All passing |

### Where Time Goes

The SPARQL test harness spends most time on:
1. **File I/O**: Reading .rq, .ttl, .srx files from disk (~60%)
2. **Turtle parsing**: Complex test data files (~20%)
3. **Query evaluation**: Actual SPARQL execution (~15%)
4. **Result comparison**: SRX/TTL parsing and comparison (~5%)

## Query Execution Optimization

### Current Evaluator: Nested Loop Join

```
for each binding in current_results:
    for each triple in graph:
        if pattern matches:
            emit new binding
```

Time complexity: O(results × triples) per pattern.

### Optimization Opportunities

#### 1. Index Structures (Medium effort, high impact)

Add hash indexes to `RdfGraph`:
```rust
struct RdfGraph {
    triples: Vec<Triple>,
    by_subject: HashMap<Subject, Vec<usize>>,    // subject → triple indices
    by_predicate: HashMap<Iri, Vec<usize>>,       // predicate → triple indices
    by_object: HashMap<RdfTerm, Vec<usize>>,      // object → triple indices
}
```

Expected improvement: 10-100x for selective patterns (specific subject or predicate).

#### 2. Bind Join Optimization (Low effort, medium impact)

When a variable is already bound, scan only matching triples:
```rust
// Instead of scanning all triples:
if let PatternElement::Variable(name) = &pattern.s {
    if let Some(bound_value) = binding.get(name) {
        // Only check triples with this subject
        for idx in graph.by_subject.get(&bound_value) { ... }
    }
}
```

#### 3. Filter Pushdown (Medium effort, medium impact)

Evaluate filters as early as possible, not after all patterns:
```
Current:  patterns → all results → filter
Better:   pattern1 → filter → pattern2 → filter → ...
```

#### 4. Result Streaming (High effort, high impact)

Instead of materializing all intermediate results, use iterators:
```rust
// Current: Vec<Binding> at each step
// Better: Box<dyn Iterator<Item = Binding>> (lazy evaluation)
```

## Parser Optimization

### Tokenizer
- Currently creates `Vec<String>` for all tokens upfront
- Could use a streaming tokenizer that yields tokens on demand
- Estimated improvement: 2x for large queries (not a bottleneck currently)

### String Allocation
- Pattern elements clone strings frequently
- Could use string interning or `Cow<str>` to reduce allocations
- Estimated improvement: marginal for current query sizes

## WASM-Specific Optimization

### Binary Size
```bash
# Current WASM size
ls -lh docs/pkg/rdf_wasm_bg.wasm

# Optimize with wasm-opt (currently disabled due to binaryen issues)
# In Cargo.toml: wasm-opt = true

# Alternative: use wasm-opt directly
wasm-opt -Oz -o optimized.wasm docs/pkg/rdf_wasm_bg.wasm
```

### Startup Time
- WASM module compilation happens at load time
- For large modules, use streaming compilation: `WebAssembly.instantiateStreaming()`
- Our web demo already uses this pattern

## Benchmarking

### Ad-hoc Benchmarking

```bash
# Time a specific operation
cargo test test_name -- --nocapture 2>&1 | grep "finished in"

# Release build comparison
cargo test --release w3c_sparql_combined_scorecard -- --nocapture 2>&1 | grep "TOTAL"
```

### Future: Criterion Benchmarks

```toml
# Cargo.toml
[dev-dependencies]
criterion = "0.5"

[[bench]]
name = "sparql_bench"
harness = false
```

Key benchmarks to create:
- BGP evaluation on graphs of 100, 1000, 10000 triples
- Turtle parsing of progressively larger files
- N-Triples parsing throughput (triples/second)
- FILTER evaluation with various expression types

## Memory Optimization

### Current Memory Model
- Triples stored as `Vec<Triple>` with owned strings
- Each IRI is a heap-allocated `String`
- BNode IDs are `u64` (efficient)

### Potential Improvements
- **String interning**: Share common IRI prefixes (e.g., `http://www.w3.org/1999/02/22-rdf-syntax-ns#`)
- **Arena allocation**: Allocate all strings in a single arena per graph
- **Compact representation**: Encode common datatypes as enum variants instead of string IRIs

## Profiling

```bash
# CPU profiling with flamegraph
cargo install flamegraph
cargo flamegraph --test w3c_sparql -- w3c_sparql_combined_scorecard

# Heap profiling
cargo install cargo-instruments  # macOS only
# On Linux, use valgrind/massif or heaptrack
```

## Optimization Priorities

1. **Don't optimize yet** — the engine is feature-incomplete. Correctness first.
2. **Index structures** — add when targeting graphs >10K triples (kgx materialization)
3. **Filter pushdown** — add when OPTIONAL/UNION create large intermediate results
4. **WASM size** — optimize when web demo load time becomes an issue
5. **Streaming** — add when memory becomes a constraint for large graphs
