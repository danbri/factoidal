---
name: blockengine
description: Design, implement, or review Factoidal's Lean 4 RDF block engine, physical planning, PushIR, PostgreSQL or TiKV persistence, block codecs, bitmap indexes, and refinement proofs. Use for block storage and query execution work, not ordinary RDF parser or vocabulary changes.
---

# Factoidal Lean 4 block engine

The owner direction from 2026-08-29 is to make Lean 4 the intended target for
the full Factoidal scope. The block engine uses a Lean-generated executable
core. PostgreSQL and TiKV supply persistence, transactions, snapshots, ranges,
and host integration. Do not create a second RDF or SPARQL engine in Rust, C,
SQL, or database extension code.

## Read first

1. [`docs/20260829-blockengine-baseline.md`](../../docs/20260829-blockengine-baseline.md)
2. [`docs/2026-08-blockengine.md`](../../docs/2026-08-blockengine.md)
3. [`docs/2026-08-blockengine_part2.md`](../../docs/2026-08-blockengine_part2.md)
4. [`docs/2026-08-blockengine_part3.md`](../../docs/2026-08-blockengine_part3.md)
5. [`skills/factoidal-lean-basics/SKILL.md`](../factoidal-lean-basics/SKILL.md)
6. [`skills/lean4-wasm-export/SKILL.md`](../lean4-wasm-export/SKILL.md)
7. [`skills/disk-storage-format/SKILL.md`](../disk-storage-format/SKILL.md)
8. [`skills/test-suites/SKILL.md`](../test-suites/SKILL.md)

Read [`docs/roaring_in_lean4.md`](../../docs/roaring_in_lean4.md) when work
involves candidate-row sets, postings, presence data, or bitmap compression.

Before an absence or coverage claim, verify `HEAD`, the intended upstream
reference, and the file list. A 2026-08-29 audit ran on a checkout 441 commits
behind and falsely reported landed Cottas, HDT, and SPARQL refinement modules
as absent.

## Current boundary

Re-measure when the dated baseline changes. At commit `73209342c232`:

- `SPARQL/Algebra.lean` has the simple evaluator and faster hash/indexed BGP
  paths.
- `SPARQL/IndexedEvalRefinement.lean` proves exact list equality for hash join
  and indexed BGP evaluation.
- `SPARQL/StoreBackend.lean`, `StorePlan.lean`, `StoreFastPath.lean`, and
  `StoreDataset.lean` provide backend dispatch, storage-aware planning,
  conservative fast paths, and dataset routing.
- 33 total Cottas modules provide readers, writers, dictionaries, on-disk
  search, selective decode, planning, pruning, counts, and indexes.
- Five total HDT modules provide a static container, dictionary, triples, and
  store path.
- The working tree has `Storage.BlockMvp`: an immutable in-memory block, a
  direct recursive triple-pattern scan, a candidate scan, and refinement
  theorems to `evalTP` and `tripleMatchesBound`. `Storage.BlockWireV0` frames
  its supported direct-term subset in versioned `BLK0` bytes. The native
  fixture is `l4block-mvp`, which parses SPARQL and searches decoded bytes.
  This transition MVP does not provide persistent IDs, sorting, a canonical
  codec proof, or backend I/O.
- `Storage.IndexedBlock` now supplies an executable cross-position local
  `TermId` dictionary, ID rows, predicate partitions, and backend read seam.
  `Storage.IndexedBlockWireV1` frames that shape directly for its supported
  RDF subset; its general codec theorem and canonical ordering are pending.
- There is no Physical Plan IR, PushIR, PostgreSQL adapter, or TiKV adapter
  yet.
- The current Cottas IDs are separate per subject, predicate, object, and graph
  role. Do not expose them as the common `TermId` contract.
- The native Lean toolchain has C output. The repository has a WASM route.
  LLVM is disabled in the installed toolchain.

F* is executable lineage, a source of algorithms, and a differential oracle.
Generalize the landed Lean implementation first. Port remaining behavior from
F* when the generalized Lean path needs it.

## Semantic boundaries

Keep these concepts distinct in types and proofs:

- RDF 1.1 term identity and RDF 1.2 term identity;
- SPARQL `sameTerm` and value comparison;
- operation-specific join and collation keys;
- default graph identity and named graph RDF terms;
- RDF graph set equivalence;
- SPARQL solution bag equivalence;
- ordered result sequence equivalence.

For RDF 1.2, language tags compare case-insensitively and lexical forms remain
exact. Current `Literal.eqb` also canonicalizes XMLLiteral lexical forms, while
current structural equality preserves tag case. Define and prove the intended
RDF 1.2 identity relation before allocating stable IDs.

Use one cross-position `TermId` relation and a tagged `GraphId`. Do not reserve
a normal term ID for the default graph.

## Architecture rule

Keep this dependency direction:

```text
semantic evaluator
  -> generalized physical model and plan
  -> bounded PushIR
  -> Lean-generated block core
  -> host and database adapters
```

Adapters can provide bytes and storage operations. They cannot define RDF
identity, SPARQL compatibility, filter errors, joins, multiplicity, or result
order.

Some current backend theorems are conditional on operation laws, token-table
agreement, or pruning soundness. Connect each real I/O path to those
hypotheses. Do not describe interface wiring alone as end-to-end verification.

## Symbolic plans and execution records

S-expressions are a readable serialization and diagnostic view, not the
storage format or an untyped executable language. Logical SPARQL algebra,
physical plans, dataflow DAGs, PushIR, and Common Logic/IKL objects each need
their own typed Lean AST and semantics. Make RDF terms, variables, physical
IDs, node references, and artifact hashes explicit in the syntax.

Keep object-language propositions distinct from code syntax in types. Common
Logic/IKL may make claims about plans, programs, executions, and evidence; it
does not execute the storage path.

Start physical plans as a tree whose first scan executes the proved block
scan. Add named dataflow nodes only when shared work, placement, caching, or
execution evidence requires a DAG. Nodes consume and produce immutable,
referable values. Content hashes identify artifacts and help replay,
provenance, and diagnostics.

PushIR is a typed, versioned, deterministic, bounded subset of physical plans.
Use one stable Lean-derived block kernel that executes programs and block bytes;
do not compile every query to a new WASM module. Build a narrow dependency
slice for `block-core`; keep broader parser and logic layers out unless the
deployment needs them.

For each fast path, keep a simple Lean meaning and add a refinement theorem or
recorded proof gap. Add differential and performance gates separately.

## Default implementation order

1. Settle and prove RDF 1.2 term identity.
2. Define cross-position `TermId` and tagged `GraphId` relations.
3. Generalize one landed Cottas access shape into one simple immutable block.
4. Define its logical quad denotation.
5. Implement one bounded scan and prove equality with the existing semantic
   triple-pattern result.
6. Define a canonical byte format and prove decode/encode denotation
   preservation, then prove its decoded scan against `evalTP`.
7. Compile it through the native Lean path.
8. Persist those exact bytes in PostgreSQL and add a three-path differential
   test.
9. Add a small tree Physical Plan and a closed S-expression renderer for its
   proved scan.

The direct-term MVP is a completed pre-step for items 1–5. Keep its exact
`scan_eq_evalTP` theorem as the reference when the dictionary and first sorted
permutation are introduced.

`BlockWireV0` is an executable transition boundary, not the canonical-byte
gate. It retains row order, supports only the inherited delta triple subset,
and has fixture-level round trips. Do not persist it as the common PostgreSQL
or TiKV object. Replace it with the canonical TermId block codec and its
general denotation theorem.

Use `l4block-corpus` for the real-RDF executable probe. It drives a Turtle
file through `IndexedBlock` and the parsed SPARQL backend seam; see
`docs/20260830-blockengine-corpora.md` for the corpus ladder. The checked
small fixture is `examples/wikidata/subsets/lifesci-kgx/data/active_site.ttl`.
It is an integration check only: it builds an in-memory dictionary and
predicate partitions, but is intentionally not the canonical medium-corpus
storage path. `IndexedBlock` uses `Array Term`, ID triples, and a predicate
`HashMap`; retain semantic `boundMatches` after decoding IDs.

For the current no-Turtle-reparse persistence vertical, use `l4block-pack` to
write supported Turtle as CRC-checked BLK0 and `l4block-file-query` to decode
that file, construct `IndexedBlock`, and run a parsed SELECT. This is a
transition-only file seam. See `docs/20260830-blockfile-e2e.md`; replace BLK0
with the canonical ID-row codec before PostgreSQL, TiKV, or mmap-backed storage.

The direct-ID prototype is `IndexedBlockWireV1`, with `l4block-id-pack` and
`l4block-id-file-query`. It stores dictionary terms once and fixed-width ID
triples, then opens those rows directly into `IndexedBlock`. Its active limits
are input-order dictionary IDs, one whole block, executable round-trip guards,
and the inherited restricted term codec. See
`docs/20260830-indexedblockwirev1.md` before extending it.

Use `l4block-id-diff INPUT.ttl --query 'SELECT ...'` as the integration gate
while strengthening proofs. It compares exact query results from the ordinary
list-backed dataset evaluator with the `IndexedBlock -> IBK1 -> decode ->
BackendReadOps` route. It is evidence for the executable byte/query seam, not
a replacement for the general codec theorem. See
`docs/20260830-indexedblock-differential.md`.

Do not sort V1 rows merely to obtain input-order-independent bytes. The current
block and SPARQL refinements preserve exact list order from the source graph.
Canonical encoding of an ordered physical block and content-addressed RDF graph
normalization are different contracts; decide and prove the latter separately.

The canonical-byte theorem is the persistence gate. PostgreSQL `bytea` and
TiKV may persist the same bytes only after it. A backend read must decode
those bytes before the proved scan runs. This is also why a separate Rust
kernel is out of scope: the Lean-derived kernel owns the common physical
object and execution semantics.

For local PostgreSQL smoke tests, prefer Podman over Docker. Verify that the
Podman machine remains reachable before drawing any database conclusion: the
development host has previously reported a successful VM start while its
rootless API immediately stopped/refused connections. Record host-runtime
failures in a dated worknote; they do not validate or invalidate the Lean
format.

`tools/blockengine-postgres-smoke.sh` is the landed local PostgreSQL 16 smoke.
It proves `IBK1 -> bytea -> exact retrieved bytes -> Lean decoder -> Lean
SPARQL`, preceded by `l4block-id-diff` for ordinary-graph/direct-IBK1 result
equality, currently on the active-site fixture. PostgreSQL is opaque
persistence only; production code must use a parameterized binary client rather
than the local smoke's `pg_read_binary_file` convenience. See
`docs/20260830-blockengine-postgres-smoke.md`.

Add plan DAGs and execution records after the tree plan. Add compression,
Roaring, PushIR, all permutations, and TiKV after this vertical unless a newer
dated decision changes the order.

Roaring32 is for block-local row offsets and candidate sets. It is not the
global term ID. Start with a pure Lean set meaning and portable codec. Add
native word primitives only after measurement, with a total Lean reference and
an agreement method.

New block-engine definitions must be total. Do not add `sorry`, user `axiom`,
`native_decide`, or `partial def`. An external primitive needs approval, a
stated boundary, and an agreement gate.

## Checks and records

From `formal/lean4/` run the full build, with no target:

```bash
/Users/danbri/.elan/bin/lake --version
/Users/danbri/.elan/bin/lake build
```

For the MVP native fixture:

```bash
/Users/danbri/.elan/bin/lake build l4block-mvp
./.lake/build/bin/l4block-mvp
```

For export changes, follow the `lean4-wasm-export` skill and test the native
ABI before WASM. Treat LLVM as unavailable until an LLVM-enabled toolchain and
a project gate exist.

At each substantial session, create or update
`docs/YYYYMMDD-blockengine-*.md`. Record the commit and dirty state, decisions
and their source, files changed, proof gaps, exact command results, benchmark
corpus and environment, and the next runnable unit.

Put stable routing and invariants here. Put measurements and temporary
conclusions in the dated worknote. Update both when a working-method error
could recur.
