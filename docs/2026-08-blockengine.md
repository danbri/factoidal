# Factoidal Verified RDF Block Engine

## Draft architecture and implementation plan — v0.1

**Status:** exploratory Part One; read with the current Part Two correction
**Date:** 29 August 2026

Current repository and implementation guidance is in
[`2026-08-blockengine_part2.md`](2026-08-blockengine_part2.md). It supersedes
Part One where this file assigns the block kernel to an independent Rust/C
implementation. After repository refresh, the landed Lean Cottas and SPARQL
refinement work is the primary starting point. The default is a Lean-generated
executable core with narrow PostgreSQL and TiKV adapters.

## 1. Thesis

Build a new RDF/SPARQL execution layer around three separable ideas:

1. **QLever-like sorted, compressed integer blocks** as the physical RDF representation.
2. **A small typed pushdown language** compiled from selected parts of SPARQL physical plans and executable close to those blocks.
3. **Lean 4 as the specification, refinement and compilation layer**, reusing the existing Factoidal SPARQL and Cottas formalisation.

The same RDF block/execution layer should support at least two persistence backends:

* **PostgreSQL** — initially the simplest production-quality local/single-primary backend; later potentially replicated or externally sharded.
* **TiKV** — the scale-out distributed backend, with RDF block operations pushed into storage nodes where useful.

The important abstraction is therefore not “PostgreSQL triples” versus “TiKV triples”. Both persist the **same RDF-specific block structures**.

```text
                    SPARQL
                       │
                       ▼
             semantic algebra
                 [Lean model]
                       │
                       ▼
              physical planner
                       │
             ┌─────────┴─────────┐
             │                   │
       coordinator plan      PushIR program
             │                   │
             └─────────┬─────────┘
                       ▼
               RDF block engine
                       │
              canonical blocks
                ╱             ╲
               ╱               ╲
      PostgreSQL               TiKV
```

The storage database supplies transactions, persistence and recovery. It does **not** define the RDF execution model.

---

# 2. Existing Factoidal code is a substantial starting point

The current Lean SPARQL implementation already has almost exactly the semantic layering needed for this project.

`SPARQL.Algebra` explicitly distinguishes:

* specification-level BGP evaluation and nested-loop join;
* faster hash/indexed execution;
* proofs elsewhere that the faster paths return exactly the specification result.

It also already defines `PatternBound`, specifically described as the bound positions that a physical store answers.

`IndexedEvalRefinement.lean` then proves, as list equality rather than mere set equivalence:

```text
hashJoin o1 o2 = join o1 o2

evalBgpIdx b g = evalBgp b g
```

That is precisely the methodology wanted for a new block engine: retain a deliberately simple semantic implementation and prove each physical implementation refines it.

The new development should generalise this pattern:

```text
evalTP                         -- semantic specification
      ▲
      │ proof of equivalence
      │
blockScan

join                           -- semantic specification
      ▲
      │
vectorMergeJoin

filterSeq
      ▲
      │
compiledPushFilter

evalBgp
      ▲
      │
physicalPlan.execute
```

The semantic code should not become contaminated by backend details.

---

# 3. Cottas is also directly relevant, but not necessarily as the final physical format

Cottas already formalises several decisions that become central to a block database.

`PlanPruning` defines conservative row-group pruning and makes the safety rule explicit:

> missing information means “include”; a negative answer may skip data only when it is justified.

It also combines single-column and compound `(p,o)` presence information, with a proof-oriented distinction between safe over-inclusion and unsafe false negatives.

`AccessPath` similarly turns access selection into an explicit typed decision:

```text
skip
offsetJump
fullScan
```

and proves that `skip` is sound while missing information falls back to scanning.

`OnDiskPlan` proves dictionary-based row-group pruning complete: a row group holding a matching token is never omitted. It also proves that candidate lists are sorted before using merge intersection.

`OnDiskSelective` formalises a particularly relevant optimisation: first find matching row indices using cheap columns, then decode only the unbound columns actually needed by the rest of the query. It proves that this “need” information changes what is decoded, not which rows match.

`OnDiskCountExact` already expresses another theme needed here: several progressively cheaper implementations of an aggregate, with formal eligibility guards determining when each optimisation is valid.

These should be refactored conceptually into backend-independent notions such as:

```text
BlockPruneDecision
BlockAccessPath
RequiredColumns
FastPathEligibility
CandidateBlockSet
```

Cottas can remain a portable/cold-storage format, importer/exporter and test corpus even if PostgreSQL/TiKV use a new block codec.

One thing should **not** simply carry across unchanged: Cottas currently has distinct subject, predicate, object and graph dictionaries, with IDs being positions in those separate dictionaries.

The new engine probably wants a common physical `TermId` domain so that values moving between subject and object positions can be joined directly.

---

# 4. Physical model: sorted blocks of integer IDs

The initial physical ID should be conceptually:

```text
TermId = unsigned 64-bit integer
```

For proofs it may remain useful to model IDs as `Nat` plus an encoding relation:

```text
PhysicalId(n, u) :=
    n < 2^64
    ∧ u.toNat = n
```

This avoids forcing every semantic theorem through fixed-width arithmetic.

The RDF dictionary maps exact RDF terms to `TermId`.

A quad becomes:

```text
(G,S,P,O) : TermId⁴
```

The first implementation should support the familiar six useful quad permutations:

```text
GSPO
GPOS
GOSP

SPOG
POSG
OSPG
```

The number need not be permanently fixed at six, but six makes the initial access-path semantics simple.

QLever demonstrates the importance of multiple sorted permutations at very large scale; current deployments report all six triple permutations over a roughly 20-billion-triple Wikidata index.

## 4.1 Blocks, not KV entries per quad

The backend should not normally contain:

```text
GPOS|g|p|o|s → {}
GPOS|g|p|o|s → {}
GPOS|g|p|o|s → {}
```

for every quad.

Instead:

```text
GPOS | g | p | block-start
        ↓
┌───────────────────────────────┐
│ Block header                  │
│ row count                     │
│ min/max IDs                   │
│ generation                    │
│ codec                         │
│ statistics                    │
├───────────────────────────────┤
│ O stream                      │
│ S stream                      │
│ optional G/P elision          │
├───────────────────────────────┤
│ revision information          │
│ optional auxiliary summaries  │
└───────────────────────────────┘
```

The fixed prefix need not be repeated in every row.

This follows the QLever design in which a first-order relation value is stored
once and metadata identifies the contiguous encoded second/third-order data.

Candidate codecs include:

```text
plain u64
frame-of-reference + bit packing
delta + bit packing
delta-varint
run-length encoding
```

Codec choice can be per block.

Use Roaring32 separately for block-local row offsets, postings, and candidate
sets. See [`roaring_in_lean4.md`](roaring_in_lean4.md).

## 4.2 Block metadata

Every block should expose enough information to reject irrelevant blocks without decoding their payload:

```text
rowCount
first/last key
per-column min/max
distinct count where cheap
encoded byte size
generation/revision range
optional presence summaries
optional compound summaries
```

This is the block equivalent of the existing Cottas pruning machinery.

A later implementation should support QLever-like block-overlap planning:

```text
A blocks:  [1..100] [101..300] [900..1200]
B blocks:              [250..400] [950..980]

```

Only mutually relevant blocks are decoded.

---

# 5. Immutable blocks plus mutable deltas

QLever obtains much of its performance from highly optimised static indexes. A mutable engine should preserve that property at block granularity instead of making every update destroy the physical layout.

Proposed model:

```text
immutable base blocks
        +
small mutable delta
        ↓
background compaction
        ↓
new immutable block generation
```

A manifest transaction publishes a new generation atomically.

```text
generation 71
   block A
   block B
   block C

delta
  + q1
  - q2

compaction
      ↓

generation 72
   block A'
   block B
   block C

manifest: 71 → 72
```

Both PostgreSQL and TiKV can provide the transactional publication mechanism.

Revision history can optionally be represented at RDF level, independently of the backend's own MVCC.

---

# 6. Yes: retain the “compiled mini-language” idea

The block representation and compiled mini-language solve different problems.

Blocks determine **how RDF is represented**.

The mini-language determines **how much query execution can move down beside those blocks**.

The project should have two execution IRs.

## 6.1 Physical Plan IR

This is relatively high level:

```text
IndexScan
BlockMergeJoin
HashJoin
LeapfrogJoin
Filter
Project
Distinct
Group
Aggregate
Union
Minus
LeftJoin
Limit
```

It chooses:

* permutation;
* bounds;
* join ordering;
* join algorithm;
* block ranges;
* coordinator versus backend execution.

## 6.2 PushIR

A smaller, deliberately bounded language describes operations safe and worthwhile to execute inside PostgreSQL or TiKV.

For debugging it could have an S-expression rendering:

```lisp
(program 1
  (scan GPOS
    (eq g 17)
    (eq p 42))
  (visible-at 103)
  (filter
    (eq-id o 9001))
  (project s o)
  (count))
```

The binary transport representation should be canonical and versioned.

Initial instructions should be intentionally modest:

```text
scan-range
decode-column
eq-id
neq-id
lt-id / le-id where meaningful
and / or / not
is-bound
visible-at-revision
select
project
count
min-id
max-id
emit
```

Then add block-level primitives:

```text
intersect-sorted
semi-join
merge-join
distinct-sorted
group-count
```

Eventually, co-partitioned multi-pattern fragments could execute completely inside a TiKV region.

PushIR should **not** initially be “SPARQL bytecode”. Unsupported SPARQL remains in the coordinator.

---

# 7. Compiling SPARQL expressions to PushIR

Factoidal already has a substantial concrete `Expr` AST and evaluator covering SPARQL expression semantics, numeric operations, string functions, term functions, error/EBV behaviour, etc.

Define:

```text
compilePushExpr : Expr → Option PushExpr
```

`none` means:

> this expression is not safe/useful to push; execute it using the normal evaluator.

The first supported subset might be:

```text
BOUND
sameTerm / exact ID equality
logical connectives
constant comparisons
simple datatype/type tests
revision predicates
```

Later add numeric and string comparisons once the physical dictionary exposes suitable normalized scalar representations.

The central theorem is then approximately:

```text
compilePushExpr e = some pe
    →
evalPushExpr pe physicalRow
    =
evalExpr e semanticRow
```

under the relation connecting `physicalRow` and `semanticRow`.

This is where Lean has unusually high leverage.

---

# 8. A subtle semantic issue should be resolved early: term equality

The existing Lean code already identifies an important mismatch.

`Binding.compatible` currently uses `Term.eqb`; for literals that comparison can be coarser than structural RDF term equality, for example by folding language-tag case. `AlgebraRefinement` explicitly proves one direction and provides a witness showing the converse is false without an additional exactness hypothesis.

A storage engine must not accidentally bake this ambiguity into its IDs.

Therefore distinguish:

```text
TermId
    exact RDF term identity

ComparisonKey / JoinKey
    any deliberately normalized equivalence used by
    a particular SPARQL operation
```

A simple `TermId == TermId` should mean exact RDF term identity.

Before physical-plan refinement becomes large, decide whether the production SPARQL semantics retain the current `Term.eqb` compatibility behaviour or move to the stricter specification relation.

This is probably the most important semantic issue to settle before optimisation.

---

# 9. Common storage backend interface

The semantic and physical layers should depend on capabilities, not concrete database names.

Conceptually:

```text
BlockBackend

capabilities()
openSnapshot()
scanBlockMetadata(scan)
readBlocks(scan)
estimate(scan)

executePushIR(scan, program)

writeBlock(...)
writeDelta(...)
publishManifest(...)

dictionaryLookup(term)
dictionaryResolve(id)
```

Capabilities include:

```text
distributed
atomicMultiKey
snapshotReads
orderedRangeScan
serverSidePushdown
backgroundCompaction
```

A planner can therefore make decisions such as:

```text
if backend.serverSidePushdown
   and fragment is PushIR-compilable
then remote fragment
else coordinator fragment
```

The query's semantics never depend on those capabilities.

---

# 10. PostgreSQL backend

PostgreSQL should be a first-class backend, not merely a toy implementation.

Version 1 should probably use ordinary PostgreSQL tables:

```text
rdf_blocks
----------------
repo
generation
permutation
prefix1
prefix2
first_id
last_id
row_count
payload bytea
metadata
```

with conventional B-tree indexes over the block metadata.

PostgreSQL provides:

```text
WAL
MVCC
snapshots
transactions
crash recovery
replication
catalogue
operational tooling
```

while the RDF engine owns the block payload.

## 10.1 PostgreSQL clusters

PostgreSQL should **not** be defined in the architecture as “the non-cluster backend”.

A backend instance can represent:

```text
one PostgreSQL server
HA primary + replicas
eventually, a managed set of PostgreSQL shards
```

But version 1 should not invent distributed transactions over multiple PostgreSQL primaries.

Thus:

* PostgreSQL is the first practical implementation.
* TiKV is the first backend with native distributed transactional partitioning.
* The common API leaves room for a future `PgShardSet`.

## 10.2 Native PostgreSQL execution

Do not initially embed the Lean runtime inside PostgreSQL backend processes.

First run the Lean-generated block core in an ordinary process. PostgreSQL
stores block bytes and metadata. A later narrow C ABI can call the same
Lean-generated library from an extension after the process boundary is stable.

The eventual extension call can be:

```text
rdf_exec_block(payload, push_program)
```

Later this can become a `CustomScan` provider, or even a table/index access method.

PostgreSQL 18 explicitly allows extensions to add custom scan paths, including scans used in place of joins, and separately permits entirely new table access methods.

That gives considerable room to deepen the integration without changing the RDF abstraction.

---

# 11. TiKV backend

TiKV persists the same canonical block bytes.

Keys are lexicographically arranged so the natural TiKV range layout follows RDF permutation ranges:

```text
repo | generation | GPOS | g | p | blockStart
```

Writes to blocks, delta state and manifests use TiKV transactions.

For execution, TiKV remains particularly attractive because its current source tree still contains:

```text
src/coprocessor
src/coprocessor_v2
```

with `coprocessor_v2` described as a plugin framework for raw coprocessor extensions; current configuration also exposes a directory for compiled coprocessor plugins.

The same `rdf-block-kernel` used by PostgreSQL should ideally be compiled into the TiKV-side extension.

```text
              common PushIR
                    │
           rdf-block-kernel
               ╱        ╲
              ╱          ╲
       PostgreSQL       TiKV
        extension      coprocessor
```

If TiKV's plugin ABI proves too unstable, pin/fork TiKV and make the RDF operator a maintained component of that fork rather than moving the semantics elsewhere.

---

# 12. Lean 4's role

Lean should own the things for which formalisation gives real leverage:

### Semantic authority

Existing:

```text
RDF terms
SPARQL expressions
solution mappings
BGP semantics
JOIN
OPTIONAL
MINUS
FILTER
GRAPH
property paths
etc.
```

### Physical models

New:

```text
TermId abstraction
Block
Permutation
BlockMetadata
ScanBounds
PhysicalRow
PhysicalBatch
PhysicalPlan
PushIR
```

### Compiler

```text
SPARQL algebra
      ↓
physical plan
      ↓
PushIR fragments
```

### Proofs

Examples:

```text
decode(encode(block)) = block

blockPrune=false
    → block contains no matching row

blockScan(pattern)
    = evalTP(pattern)

vectorMergeJoin
    = semantic join

compilePushExpr(e)=p
    → evalPush(p)=evalExpr(e)

fastCount(...)
    = semantic COUNT

physicalPlan.eval
    = GraphPattern.eval
```

This extends the exact methodology already used by `IndexedEvalRefinement`.

---

# 13. What should actually be extracted from Lean?

Initially:

```text
factoidal-plan
    SPARQL/algebra → physical plan

factoidal-push-compiler
    physical fragment → PushIR

factoidal-push-ref
    reference PushIR interpreter

factoidal-block-ref
    reference block codec/scan implementation
```

These can be native Lean executables/libraries.

Lean currently compiles modules to C. An LLVM-enabled Lean toolchain can add
the optional LLVM backend; the installed toolchain does not enable it.

The **reference implementation should be executable**, not proof-only.

That gives differential tests of the form:

```text
Lean semantic evaluator
          ==
Lean-generated block core
          ==
PostgreSQL result
          ==
TiKV result
```

for generated fixtures.

---

# 14. What should initially NOT be Lean-generated?

Database-host integration and measured packed-vector exceptions:

```text
bit packing
SIMD intersections
decompression kernels
CRC/checksum loops
TiKV plugin plumbing
PostgreSQL extension callbacks
zero-copy buffer manipulation
```

should start in Lean where the current representation is adequate. PostgreSQL
callbacks and TiKV plugin plumbing remain thin host code. A small native
primitive can be considered for a measured dense-word or byte operation.

The reason is not that Lean cannot calculate these things.

It is representation and integration.

Lean's generic arrays box fixed-width integers, including `UInt64`; only specialised structures such as `ByteArray` have packed storage.

Additionally, Lean's current FFI documentation explicitly calls the interface unstable, and foreign interaction with compound values is constrained.

Running a Lean runtime inside every PostgreSQL backend process or TiKV storage
node is a later integration choice. The first system uses an ordinary Lean
process and backend persistence APIs.

---

# 15. The resulting trust boundary

This should be explicit.

If Lean says:

```lean
@[extern "fast_intersection"]
def intersection := referenceIntersection
```

Lean proves properties of `referenceIntersection`.

At runtime the native symbol executes instead.

Therefore:

```text
Lean proof
   ≠
proof of arbitrary extern implementation
```

Any substituted native primitive is a trusted component until its agreement
method runs.

Mitigations:

1. Keep each primitive very small.
2. Define all its operations semantically in Lean.
3. Generate exhaustive/symbolic tests where feasible.
4. Differential-test native primitives continuously against Lean.
5. Use fuzz/property testing across codecs and plans.
6. Potentially later verify especially critical kernels in F* and extract them to C.
7. Record native-primitive version and hash in execution attestations if Factoidal's provenance work is applied.

This boundary is much cleaner than making the whole SPARQL engine native and trying to reason retrospectively about it.

---

# 16. PushIR is therefore more than a performance trick

It becomes the formal boundary between verified planning and high-performance native execution.

The program:

```text
SPARQL
  ↓
Lean semantics
  ↓ proved compilation
PushIR
  ↓
small native interpreter
  ↓
blocks
```

is much easier to validate than:

```text
SPARQL
  ↓
large opaque Rust/C++ engine
```

PushIR should consequently be:

```text
typed
bounded
versioned
canonical
deterministic
resource-limited
easy to interpret
easy to fuzz
easy to formalise
```

No arbitrary recursion or memory access.

A program should carry an explicit maximum:

```text
blocks
rows
temporary vectors
output rows
instructions
```

where appropriate.

---

# 17. Query execution strategy

Initial execution should use conventional binary joins plus sorted merge operations.

Then add:

```text
block-aware lazy merge joins
galloping intersection
SIMD intersection
semi-join reduction
late materialisation
vectorised FILTER
```

For cyclic BGPs, add a worst-case-optimal join implementation such as Leapfrog Triejoin once the sorted permutation iterators are mature.

The backend boundary should expose sorted streams strongly enough that the physical planner can reason about ordering rather than treating each scan as an unordered bag.

---

# 18. Revisions

Revision/time-travel semantics should be an RDF-layer feature rather than simply exposing PostgreSQL or TiKV MVCC timestamps.

A row/quad can have compact visibility:

```text
[insert, delete, insert, delete, ...]
```

or an equivalent compressed interval representation.

Then:

```text
visible-at revision
visible-between revisions
```

become PushIR primitives.

This recovers the particularly interesting Dydra idea while remaining storage-backend-independent.

---

# 19. Suggested source-tree evolution

The existing formalisation should remain intact where possible.

Add something approximately like:

```text
formal/lean4/L4Factoidal/

  SPARQL/
    Algebra.lean             existing
    Expr.lean                existing

    Physical/
      Model.lean
      Plan.lean
      Planner.lean
      Refinement.lean

    PushIR/
      Syntax.lean
      Eval.lean
      CompileExpr.lean
      CompilePlan.lean
      Refinement.lean

  Storage/
    TermId.lean

    Block/
      Model.lean
      Codec.lean
      Scan.lean
      Pruning.lean
      Join.lean
      Refinement.lean

    Backend/
      Model.lean
      Capabilities.lean

  Cottas/
      ... existing ...
```

Over time, generally useful Cottas proofs can migrate down into `Storage.Block`.

---

# 20. Implementation phases

## Phase 0 — semantic and benchmark baseline

Resolve:

```text
exact term identity
Term.eqb / SPARQL compatibility issue
TermId semantics
bag/order requirements of physical operators
```

Create benchmark corpus and query suite.

## Phase 1 — canonical block format

Implement:

```text
TermId
permutations
block codec
metadata
in-memory block scan
```

Lean reference implementation first.

Prove scan correctness.

Compile the same implementation through Lean's native C path.

## Phase 2 — PostgreSQL storage

Persist canonical blocks in PostgreSQL.

Implement:

```text
dictionary
block build
range lookup
snapshots
manifest publication
```

Support BGP scans and simple joins.

This gives an operational engine before distributed complexity arrives.

## Phase 3 — PushIR

Define and formalise PushIR.

Compile:

```text
bound equality
FILTER fragment
projection
revision visibility
COUNT
```

Implement both:

```text
Lean reference interpreter
Lean optimized interpreter
```

Prove or differential-test them according to the stated assurance level.

## Phase 4 — PostgreSQL native pushdown

Create a PostgreSQL extension around the Lean-generated block core.

Eventually expose custom scan paths so PostgreSQL can execute an RDF block operation without materialising ordinary tuples unnecessarily.

## Phase 5 — TiKV backend

Store identical block objects in TiKV.

Implement:

```text
range placement
snapshots
manifest transactions
dictionary
delta writes
```

Initially execution may occur in the coordinator.

Then deploy the same PushIR/block kernel through TiKV's coprocessor mechanism.

## Phase 6 — serious query engine

Implement:

```text
cost/cardinality model
lazy block joins
vectorised execution
SIMD kernels
WCOJ
block statistics
materialized graph patterns
```

QLever's current support for precomputed patterns and materialized join-chain/star views is useful inspiration here.

## Phase 7 — mutation/revision work

Implement:

```text
base + delta
background compaction
revision visibility
snapshot/time-travel querying
incremental materialized structures
```

## Phase 8 — assurance

For every physical optimisation:

```text
simple semantic definition
optimized implementation
refinement theorem where feasible
native differential gate
benchmark
```

---

# 21. First concrete prototype

The first useful implementation should deliberately be small.

Input:

```text
N-Triples / N-Quads
```

Build:

```text
global term dictionary
six permutations
canonical compressed blocks
```

Persist to:

```text
PostgreSQL
```

and optionally the same block set to:

```text
TiKV
```

Support:

```sparql
SELECT ...
WHERE {
   triple-pattern .
   triple-pattern .
   triple-pattern .
   FILTER(simple-expression)
}
LIMIT ...
```

plus:

```text
ASK
COUNT
```

Expose diagnostics:

```text
semantic algebra
physical plan
selected permutation
candidate blocks
blocks skipped
blocks decoded
PushIR program
rows before/after pushdown
join algorithm
timings
```

The important success criterion is not initially beating QLever.

It is:

> **one SPARQL semantics, one physical RDF block model, one PushIR, two radically different persistence backends, with the optimised paths continuously checked against the Lean semantics.**

Once that works, the performance architecture has enough freedom to become genuinely aggressive without losing the semantic anchor.

---

# 22. Current architectural recommendation

The strongest current design is therefore:

```text
                    EXISTING LEAN
        ┌──────────────────────────────────┐
        │ RDF/SPARQL semantics             │
        │ executable evaluator             │
        │ algebra refinement               │
        │ indexed-eval refinement          │
        │ Cottas physical/access reasoning │
        │ Cottas on-disk implementation    │
        └────────────────┬─────────────────┘
                         │
                  GENERALIZE / REUSE
                         │
                         ▼
              verified RDF Block Engine
                         │
             ┌───────────┴───────────┐
             │                       │
      PostgreSQL backend        TiKV backend
             │                       │
             └───────────┬───────────┘
                         ▼
                common semantics and
                 assurance chain
```

Lean is not being relegated to a decorative proof layer.

It defines:

```text
what SPARQL means
what a block denotes
what pruning is allowed to discard
what a physical plan means
what PushIR means
what compilation is supposed to preserve
```

The Lean-generated executable core is the default. Thin database adapters
supply persistence, transactions, snapshots, ranges, and host callbacks.
Separately implemented native primitives are allowed only for measured
operations with a stated Lean meaning and an agreement method.

The Physical Plan IR and PushIR remain useful seams between query lowering and
bounded block execution.
