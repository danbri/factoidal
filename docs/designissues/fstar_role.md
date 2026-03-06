# F* Role in Factoidal Architecture

## The Toolchain Gap

Rust is a common route to WASM, and many tools assume the pipeline:

    spec → Rust → wasm32 target → WASM

F*'s ecosystem historically assumes a different pipeline:

    F* → Low* → KreMLin → C → native binary

or occasionally:

    F* → OCaml extraction

Direct F* → Rust → WASM is not a well-established toolchain. Therefore an automated assistant trying to satisfy "F* + SPARQL + WASM" will often default to handwritten Rust once extraction becomes awkward.

This is not irrational behavior from the tool. It is a signal that the requested architecture crosses toolchain boundaries.

A cleaner architecture for a formally grounded SPARQL system targeting WASM would separate concerns.

---

## Formal-Core SPARQL Architecture (F* + Rust + WASM)

### Layer 0 — Mathematical Semantics (F*)

Purpose: define the meaning of SPARQL.

No extraction requirement.

Define:
- RDF terms
- triples
- datasets
- solution mappings
- algebra operators

Example core definitions:

```fstar
type iri
type literal
type bnode

type term =
| IRI : iri -> term
| Literal : literal -> term
| BNode : bnode -> term

type triple = term * term * term

type dataset = set triple

type solution = map var term
```

Define algebra semantics:

```fstar
val eval_join :
  dataset -> set solution -> set solution -> set solution
```

Then define semantics for:
- BGP
- Join
- Union
- Filter
- Projection
- Optional
- Distinct

Theorems live here.

Examples:
- Join associativity
- Projection safety
- Filter commutation
- algebra rewrite correctness

This layer is the formal specification of SPARQL semantics.

No storage or indexing appears here.

---

### Layer 1 — Verified Algebra Engine (F*)

Goal: executable algebra evaluator that still lives inside F*.

Representations are simplified but executable.

```fstar
type solutions = list solution

val join_exec :
  solutions -> solutions -> Tot solutions
```

Prove:

```fstar
lemma_join_correct :
  join_exec s1 s2 == eval_join_semantics s1 s2
```

At this point you have a verified algebra kernel.

Still independent of:
- parser
- indexing
- query planner

---

### Layer 2 — Extraction Boundary

Decide what gets extracted.

Two realistic options.

**Option A (safer)**

Extract algebra kernel only.

    F* algebra → OCaml or C

Rust calls this library.

**Option B (harder)**

Translate F* data structures into Rust-compatible ones and generate C.

Rust FFI wraps the generated C.

    F* → Low* → C → Rust wrapper → WASM

This pattern already exists in verified crypto projects.

---

### Layer 3 — Rust Runtime (Engineering Layer)

Rust handles everything not suitable for F*.

Responsibilities:
- RDF parsing
- SPARQL parsing
- dataset storage
- indexing
- query planning
- streaming execution
- WASM compilation

Rust produces the SPARQL algebra tree.

Example:

```rust
enum Algebra {
    BGP(Vec<TriplePattern>),
    Join(Box<Algebra>, Box<Algebra>),
    Union(Box<Algebra>, Box<Algebra>),
    Filter(Expr, Box<Algebra>),
    Project(Vec<Var>, Box<Algebra>)
}
```

Rust then calls the verified algebra kernel.

---

### Layer 4 — WASM Target

Rust compiles to:

    wasm32-unknown-unknown

Typical deployment:
- browser SPARQL engine
- edge execution
- embedded query verification

---

## Trust Boundary

The trusted core is small.

- F* semantic definitions
- F* algebra engine
- proofs

Everything else is untrusted engineering code.

But correctness claims can be scoped:

> "The evaluation of SPARQL algebra operators inside the kernel is provably correct relative to the formal semantics."

---

## Optional Advanced Feature: Signed Query Execution

The algebra kernel can emit proof artifacts.

Example:
- query
- dataset hash
- execution trace
- result hash
- signature

This allows claims like:

> "This result set was computed by the verified algebra kernel version X on dataset hash Y."

This fits well with:
- verifiable data pipelines
- regulated data processing
- graph transformation attestations

---

## Why This Works Better

The architecture avoids three common failure modes.

### 1. Over-verification

Trying to formally verify parsing, storage engines, and indexing is extremely expensive.

### 2. Toolchain mismatch

Rust handles WASM well. F* handles formal semantics well. They are not the same tool.

### 3. Semantic drift

Formal semantics lives in one place. Rust code cannot silently change meaning.

---

## Minimal Phase-1 Scope

Only implement:
- RDF terms
- solution mappings
- BGP
- Join
- Filter
- Projection

Skip initially:
- aggregates
- property paths
- SERVICE
- entailment regimes
- update

This keeps the proof surface manageable.

---

## Reality Check

A realistic deliverable from this approach would be:
- ~1500–3000 lines F*
- ~10–20 core theorems
- small verified algebra kernel
- Rust SPARQL parser and runtime
- WASM module calling the kernel

That is ambitious but feasible.

Trying to formally derive an entire production SPARQL engine is not.
