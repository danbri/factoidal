# Factoidal Verified RDF Block Engine

## Part Two — Repository corrections, executable assurance architecture, and the first implementation vertical

**Status:** current companion/correction to Part One after repository refresh
**Date:** 29 August 2026
**Purpose:** reconcile the exploratory architecture with commit `73209342c232`, and clarify the intended role of Lean 4/F* in the implementation.

---

# 1. Repository status after refresh

A subsequent audit first reported that several Lean modules cited in Part One
were absent. That conclusion came from a stale local checkout and is withdrawn.
After fast-forwarding the repository to `73209342c232`, Codex confirmed that
the current Lean tree includes:

- the Cottas reader and writer;
- Cottas on-disk planning and selective-scan modules;
- `SPARQL/IndexedEvalRefinement.lean`;
- `SPARQL/AlgebraRefinement.lean`;
- the HDT container, dictionary, triples, and store modules.

These are landed implementation and proof infrastructure. They are not only
F* lineage or proposed ports.

The following vocabulary remains useful:

```text
LANDED
    present and building in the checkout being developed

LINEAGE
    existing implementation/design in F*, another branch,
    or earlier Factoidal work that may be ported/reused

PROPOSED
    new block-engine design
```

No proposed component should be presented as landed only because an analogous
component exists elsewhere. The Cottas and SPARQL modules cited above now
belong in `LANDED`.

The dated repository baseline is
[`20260829-blockengine-baseline.md`](20260829-blockengine-baseline.md).

---

# 2. More important correction: Lean is not the “proof side” of the system

The following architecture is explicitly **not** the goal:

```text
Lean
  semantics
  proofs
      │
      ▼
Rust/C database
  actual computation
```

The Factoidal approach is stronger.

Lean 4, continuing the earlier F* approach, should be an **authoritative executable implementation language for assurance-critical data processing**.

The intended architecture is closer to:

```text
                     INPUT
                       │
                       ▼
             executable Lean/F*
          parse / validate / normalize
                       │
                       ▼
             executable Lean/F*
               RDF / SPARQL
                       │
                       ▼
             executable Lean/F*
          physical planning / PushIR
                       │
                       ▼
             executable Lean/F*
             RDF block operations
                       │
              ┌────────┴────────┐
              │                 │
              ▼                 ▼
         PostgreSQL            TiKV
          adapter              adapter
              │                 │
              └────────┬────────┘
                       ▼
                     RESULT
                       │
                       ▼
             evidence / lineage /
                  attestation
```

Proofs are one consequence of choosing Lean.

Other consequences are equally important:

* the semantic implementation is executable;
* transformations can carry checked preconditions;
* optimized algorithms can refine simpler executable algorithms;
* query compilation can itself be proved correct;
* data representation changes can be proved denotation-preserving;
* processing stages can emit precise evidence about what was run;
* the same implementation can target native code and WebAssembly;
* later attestations can bind an actual executable build to the source and theorem-bearing implementation from which it arose.

This is the larger Factoidal value proposition.

---

# 3. “Implemented in Lean” is not itself an assurance level

Codex found a useful complication: the current Lean tree contains `partial def`s, including `Storage/DeltaLog.replay`, and the older repository guidance understated their number.

So we should not use:

```text
Lean = verified
```

as a category.

Instead distinguish at least:

```text
A. Total Lean definition
   executable, accepted by Lean's termination/productivity checks

B. Total Lean definition + proved contract
   e.g. scanFast x = scanSpec x

C. Lean partial def
   executable but with a weaker termination/trust story

D. Lean definition with assumptions / axioms / foreign primitives
   assurance explicitly conditional on those boundaries

E. Separately implemented optimized code
   related by proof, differential testing, or merely an interface contract
```

These distinctions should eventually be visible in Factoidal evidence records.

A physical operator might therefore report:

```text
implementation:
  language: lean4
  definition: Storage.Block.scan
  totality: total
  refinement: blockScan_eq_semanticScan
```

while another says:

```text
implementation:
  language: native
  semanticReference: Storage.Block.intersect
  evidence: differential
```

This prevents “written in Lean” from becoming a misleading green badge.

---

# 4. Current compilation paths: C and WASM are real; LLVM is currently a target

Codex verified the native C and current WebAssembly paths.

It also directly tested the installed Lean toolchain's LLVM backend and found that it was built without `-DLLVM=ON`; invoking `lean -b` hit Lean's explicit assertion requiring an LLVM-enabled build.

Therefore Part One's language should be corrected from:

```text
Lean → C / LLVM / WASM
```

to:

```text
CURRENT:
    Lean → generated/native C path
    Lean → WASM path

PLANNED/OPTIONAL:
    Lean → LLVM backend
```

LLVM should not be an initial project dependency.

It is an optimization/toolchain experiment.

A useful principle follows:

> The block-engine architecture must not depend on LLVM being available.

If LLVM later produces materially better vector code or easier SIMD integration, enable and benchmark it.

---

# 5. The native-kernel wording in Part One was too strong

Part One proposed a common Rust/C `rdf-block-kernel`.

That prematurely placed the computational center outside Lean.

The revised preference is:

```text
                Lean source
                    │
           executable algorithms
                    │
             proved contracts
                    │
                    ▼
          Lean-generated native core
                    │
             narrow stable ABI
               ╱          ╲
              ╱            ╲
      PostgreSQL shim     TiKV shim
```

The backend adapters may necessarily contain C, Rust or backend-native glue.

Their job should initially be small:

```text
receive bytes
pin/copy buffers where necessary
call Lean-generated core
translate return/error representation
interact with backend APIs
```

They should not independently reimplement:

```text
block decoding
block pruning
revision visibility
PushIR semantics
sorted intersection
SPARQL expression fragments
```

unless benchmarks force that decision.

This makes the **default executable implementation the formal implementation**.

Only measured hot spots should be candidates for separately implemented native kernels.

---

# 6. That does not forbid native optimization

There will probably be operations for which platform-specific code wins significantly:

```text
SIMD uint64 intersection
bit unpacking
Roaring primitives
CRC/hashing
memory mapping
zero-copy backend buffers
```

But the architecture should approach these incrementally.

For example:

```text
Lean:
    intersectSpec

Lean:
    intersectScalar

theorem:
    intersectScalar = intersectSpec

later:

native:
    intersectAVX2
```

The final step introduces an explicit new assurance obligation.

Possible evidence strengths include:

```text
machine-checked refinement
    strongest

compiled from the same Lean definition
    strong, subject to compiler/toolchain trust

differentially tested against Lean
    useful but weaker

reproducibly benchmarked/tested
    weaker

external implementation only
    explicit trust boundary
```

The optimized implementation should never silently inherit proofs about a different function.

---

# 7. PostgreSQL and TiKV remain complementary first-class backends

The common-framework idea still stands.

It should not be described as:

```text
PostgreSQL → small/local
TiKV       → real/clustered
```

PostgreSQL can itself be deployed in substantial HA configurations.

The important distinction is narrower.

TiKV natively supplies a distributed transactional keyspace whose ranges are automatically partitioned across a cluster.

Stock PostgreSQL does not provide that same abstraction across arbitrary PostgreSQL nodes.

So:

```text
                  BlockBackend
                      │
             ┌────────┴────────┐
             │                 │
        PostgreSQL            TiKV
             │                 │
     single / HA /          distributed
     replicated             KV cluster
```

Later we might add:

```text
PostgresShardBackend
```

but this should not be faked in version 1.

The planner should depend on capabilities such as:

```text
snapshotReads
atomicMultiKeyWrite
orderedRangeAccess
remotePushExecution
automaticPartitioning
```

rather than on assumptions encoded in backend names.

---

# 8. Both backends store the same RDF-level objects

The new system should avoid having:

```text
Postgres physical RDF model
```

and:

```text
TiKV physical RDF model
```

where possible.

Instead define a canonical RDF block model:

```text
Block
BlockMetadata
Manifest
Delta
RevisionVisibility
```

and provide two persistence realizations.

For example:

```text
                 Logical RDF dataset D
                         │
          ┌──────────────┴──────────────┐
          │                             │
      Manifest Mpg                  Manifest Mkv
          │                             │
      PostgreSQL                       TiKV
```

`Mpg` and `Mkv` might differ in block boundaries or physical placement while still satisfying:

```text
denotes(Mpg) = D

denotes(Mkv) = D
```

This is important for both portability and assurance.

The backend is not the identity of the data.

---

# 9. QLever-like blocks and the compiled mini-language remain two separate ideas

Codex should not have to choose between:

```text
QLever-like uint blocks
```

and:

```text
compiled SPARQL mini-language
```

We want both.

They operate at different levels.

## Blocks

Blocks answer:

> How do we represent and scan large RDF relations efficiently?

Characteristics:

```text
global integer term IDs
multiple sorted permutations
prefix elision
column/vector representation
compressed integer streams
min/max metadata
block statistics
selective decode
lazy block access
```

## PushIR

PushIR answers:

> Once a block is located, what bounded computation can execute beside it?

Examples:

```text
filter ID
check revision visibility
select columns
count
intersect sorted IDs
semi-join
aggregate locally
```

Conceptually:

```text
SPARQL
   │
   ▼
Physical Plan
   │
   ├──────── coordinator operators
   │
   └──────── PushIR fragment
                  │
                  ▼
              RDF blocks
```

Neither replaces the other.

---

# 10. PushIR should preferably be implemented in Lean

PushIR is especially suitable for the Factoidal methodology because it can be tiny.

Version 0 might contain only:

```text
ScanRange
LoadColumn
EqId
LtId
And
Or
Not
VisibleAt
Select
Project
Count
Min
Max
Emit
```

Its syntax, validator and evaluator can all be Lean definitions.

Then:

```text
compilePush : PhysicalFragment → Option PushProgram
```

is also executable Lean.

The key theorem family is:

```text
compilePush f = some p
       →
evalPush p data
       =
evalFragment f data
```

where equality is stated using the appropriate RDF/SPARQL bag/order semantics.

An expression or physical fragment that cannot be compiled simply remains above the pushdown boundary.

Thus:

```text
compiler returns none
```

means:

```text
execute normally
```

not:

```text
query unsupported
```

That is a useful safe-fallback rule.

---

# 11. PushIR does not need to be a generic VM

RonDB's interpreted-code machinery was the inspiration, not the required shape.

A particularly attractive alternative for Factoidal is for PushIR to be an algebra of **block primitives**.

For example:

```text
Scan GPOS g=17 p=42
VisibleAt 103
Eq O 9001
Project S
Count
```

might compile directly into calls among a small fixed family of Lean functions.

A serialized program is still useful for:

* passing computation to TiKV workers;
* passing plans into PostgreSQL extension calls;
* content-addressing the computation;
* replay;
* diagnostics;
* attestation.

But we do not need to invent registers, stacks or general-purpose bytecode unless that becomes useful.

---

# 12. The first block representation should be deliberately simple

The first vertical should not begin with clever bitpacking.

Something like:

```lean
structure Block where
  permutation : Permutation
  prefix : ...
  rows : Array PhysicalRow
```

or a simple columnar equivalent is enough to establish semantics.

Then prove things such as:

```text
blockRows (encode rows) = rows

scanBlock pattern block
    =
semanticFilter pattern (blockRows block)
```

Only after the semantic boundary works should we introduce:

```text
delta encoding
frame-of-reference
bit packing
RLE
Roaring
adaptive codecs
```

Each codec should preserve a common block denotation.

That turns compression into another data transformation with an explicit correctness contract.

---

# 13. TermId should come first

Codex suggested the first implementation unit as:

```text
TermId
tagged GraphId
one immutable block
one permutation
one scan
one refinement theorem
```

That is a good starting vertical.

I would add one requirement:

> the scan theorem should connect all the way to an existing RDF/SPARQL semantic notion, rather than merely proving two new block-engine functions agree.

So the first useful vertical is:

```text
RDF terms
   │
   ▼
TermId encoding
   │
   ▼
one sorted block
   │
   ▼
physical bounded scan
   │
   ▼
decode result
   │
   ▼
existing semantic triple-pattern result
```

with a theorem connecting the endpoints.

That gives the project its characteristic shape immediately.

---

# 14. Use one cross-position TermId domain unless evidence argues otherwise

Cottas-style separate dictionaries are useful for columnar artifacts, but a general SPARQL engine benefits from IDs that survive movement across positions.

For:

```sparql
?s :parent ?o .
?o :name ?name .
```

the first pattern's object immediately becomes the second pattern's subject join value.

So the default model should be:

```text
TermId : RDFTerm → 64-bit physical ID
```

with exact RDF-term identity represented consistently wherever the term can legally occur.

Graph scope can be separate:

```text
GraphId =
    DefaultGraph
  | NamedGraph TermId
```

or an equivalent tagged representation.

This should remain a semantic design question until proved adequate; do not prematurely burn tag bits into the public identity contract.

---

# 15. Physical TermId identity must be stricter than accidental evaluator equivalences

The existing SPARQL formalization has already exposed cases where an implementation equality relation is not literally structural RDF-term equality.

The contract must also name its RDF version. The
[RDF 1.2 Concepts definition of literal term equality](https://www.w3.org/TR/rdf12-concepts/#section-Graph-Literal)
treats language tags case-insensitively and keeps lexical forms exact. This
differs from RDF 1.1 for tag case. The current Lean relations split in a
different place:

- `Literal.eqb` folds language-tag case, as RDF 1.2 requires, and also
  canonicalizes `rdf:XMLLiteral` lexical forms, which is too coarse for RDF 1.2
  term identity;
- `Literal.termEq` compares all stored fields, which keeps XML lexical forms
  exact but treats tag case as significant.

Thus neither relation should be adopted as the public RDF 1.2 dictionary
contract without a small repair. Define and prove one version-explicit term
identity relation before allocating stable IDs.

Therefore the physical dictionary should have a simple contract:

```text
same TermId
    ⇔
same RDF term
```

for whatever precise RDF-term equality Factoidal chooses.

Other notions should be separately derived:

```text
JoinKey
ValueKey
NumericValue
CollationKey
```

if particular SPARQL operations require them.

Do not make physical identity depend on an optimization-oriented equality predicate.

---

# 16. What can be reused from the existing Lean SPARQL implementation?

Substantially more than storage code.

The existing SPARQL tree should remain the semantic root.

Useful existing categories include:

```text
RDF term model
query/pattern AST
expression AST
solution mappings
expression evaluation
BGP semantics
join/filter/union/minus/etc.
query evaluation machinery
test infrastructure
W3C conformance fixtures
```

The new project should add a physical-evaluation vertical beneath those semantics rather than create a second SPARQL implementation.

The refreshed tree gives a more specific reuse path:

```text
existing Lean SPARQL semantics
        │
        ├── AlgebraRefinement
        ├── IndexedEvalRefinement
        │
        ▼
existing Lean Cottas physical reasoning
        │
        ├── on-disk planning
        ├── selective scans
        ├── reader/writer machinery
        └── access-path and pruning logic
        │
        ▼
new generalized Block layer
        │
        ├── PostgreSQL persistence
        └── TiKV persistence
```

This makes the first work a generalization and refactoring of landed Lean
physical techniques. It is not a new port from F*.

Conceptually:

```text
SPARQL semantic evaluator
           ▲
           │ refinement
           │
physical block evaluator
```

`IndexedEvalRefinement` already proves exact list equality for the indexed BGP
evaluator and hash join. Use its proof shape as the first block-scan standard.

---

# 17. How should landed Lean Cottas and the F* lineage be used?

The Lean Cottas work is the primary physical starting point. It already
contains the reader/writer, on-disk planner, selective scans, access-path
selection, pruning, limits, counts, dictionaries, and offset-index machinery.

The older F* Cottas work remains useful as lineage, differential input, and a
source for behavior that has not yet moved. It contains physical-algorithm
reasoning such as:

```text
candidate-group pruning
dictionary-based exclusion
offset jumps
selective column decode
exact-count shortcuts
safe fallback
ordered intersection
```

The refactoring direction is now:

```text
landed Lean Cottas algorithm and theorem
       │
       ▼
general Lean Block algorithm and theorem
       │
       ├── Cottas realization
       │
       ├── PostgreSQL block realization
       │
       └── TiKV block realization
```

The current Cottas store uses separate subject, predicate, object, and graph ID
domains. It also has Cottas-specific row-group and file contracts. The common
Block layer still needs one version-explicit term identity contract, one block
denotation, and backend-neutral laws. Generalize the proved mechanisms without
making the current Cottas representation the public storage contract.

---

# 18. HDT should be treated similarly

The refreshed tree has five total Lean HDT modules: container, container
theorems, dictionary, triples, and store. The store reads a static HDT object
and performs pure searches after the I/O boundary. Use it for:

```text
binary encoding patterns
succinct representations
byte-level proof experience
test infrastructure
```

HDT remains particularly useful as prior art for:

```text
compact dictionary IDs
compressed adjacency-style relations
static RDF packaging
```

while the new engine has stronger requirements around:

```text
named graphs
transactions
updates
revisions
distributed storage
```

---

# 19. PostgreSQL integration should start thinner than a CustomScan

A reasonable progression is:

```text
Phase PG0
Lean block engine runs in ordinary process
PostgreSQL stores manifests and block bytes

Phase PG1
small PostgreSQL extension calls Lean-generated native library

Phase PG2
custom PostgreSQL scan/executor integration

Phase PG3
only if justified:
deeper access-method/planner integration
```

Do not make PostgreSQL planner integration a prerequisite for proving the RDF physical model.

Early PostgreSQL is valuable precisely because it gives us mature:

```text
transactions
WAL
snapshots
recovery
replication
operations tooling
```

without requiring us to solve distributed systems first.

---

# 20. TiKV integration can follow the same staged rule

Likewise:

```text
Phase KV0
TiKV stores canonical blocks
coordinator retrieves and executes them

Phase KV1
send bounded PushIR fragments toward data

Phase KV2
execute Lean-generated block core from a thin TiKV-side adapter

Phase KV3
specialized region-aware joins/aggregates
```

Whether the final integration is:

```text
TiKV plugin
maintained TiKV fork
sidecar colocated with TiKV
FFI into Lean-generated native library
```

is an implementation question.

The semantic contract must not depend on that choice.

---

# 21. End-to-end assurance includes data representation, not just query algorithms

For one query execution the eventual evidence chain might be:

```text
source bytes
    │
    ▼
RDF parse
    │
    ▼
canonical logical dataset D
    │
    ▼
term dictionary
    │
    ▼
block manifest M
    │
    ▼
snapshot/revision V
    │
    ▼
SPARQL query Q
    │
    ▼
logical plan L
    │
    ▼
physical plan P
    │
    ▼
PushIR fragments X1...Xn
    │
    ▼
block executions
    │
    ▼
result R
```

Possible checked statements include:

```text
parse(source) = D

manifestDenotes(M, D)

physicalPlanDenotes(P) = logicalPlanDenotes(L)

compilePush(F) = X
  → evalPush(X) = evalPhysicalFragment(F)

resultOf(P, M, V) = R
```

And the execution record can bind those semantic facts to:

```text
source hashes
Lean source/build identity
compiler/toolchain identity
backend snapshot
program hashes
block hashes
result hash
```

This is where the block engine connects to Factoidal's broader provenance/attestation work.

---

# 22. Compiler trust is part of the chain too

Even if an algorithm is written and proved in Lean, executing compiled machine code introduces a toolchain boundary.

So a mature assurance statement should distinguish:

```text
kernel-checked theorem about source definition
```

from:

```text
claim that this executable implements that source definition
```

The latter relies initially on the Lean compiler, C compiler/linker, runtime and build process.

Possible future strengthening includes:

```text
reproducible builds
signed source→binary provenance
NPM/GitHub build provenance
trusted-cloud build attestation
multiple backend compilations
cross-checking WASM/native results
```

This is not a defect in the Lean strategy.

It is precisely the kind of boundary Factoidal should make visible rather than pretending does not exist.

---

# 23. The block engine should emit its own operation DAG

Every substantial physical transformation can become a Factoidal operation:

```text
dictionary build
block build
re-encode
compact
apply delta
publish manifest
execute query
```

For example:

```text
DatasetSnapshot D17
      │
      │ build-block-index
      ▼
BlockManifest M31
      │
      │ apply Delta Δ4
      ▼
BlockManifest M32
      │
      │ compact
      ▼
BlockManifest M33
```

The same DAG has:

```text
computation view
provenance view
assurance view
```

rather than requiring a separate database audit-log ontology.

This follows the broader Factoidal direction in which operations record immutable inputs/outputs, semantics and evidence rather than merely logging that some program ran.

---

# 24. Compaction is itself an assurance-sensitive algorithm

Suppose:

```text
base B
delta Δ
```

becomes:

```text
new base B'
```

Then the relevant claim is not simply:

```text
compaction completed
```

but:

```text
denote(B, Δ, revision r)
    =
denote(B', revision r)
```

for the appropriate revision domain.

Likewise:

```text
CodecA block
   ↓ re-encode
CodecB block
```

should preserve block denotation.

This makes ordinary database maintenance part of the same formally described data-processing chain.

That is exactly where a Lean/F* approach has more to offer than “the query planner has been proved correct”.

---

# 25. Safe fallback should be a system-wide invariant

One of the strongest ideas from the existing Factoidal storage work should become a central rule:

```text
optimization cannot establish safety
        ↓
use slower path
```

not:

```text
optimization cannot establish safety
        ↓
guess
```

Examples:

```text
unknown block summary
    → read block

PushIR compilation failure
    → coordinator execution

unknown cardinality
    → conservative plan

missing native optimization
    → Lean scalar implementation

unusable offset/index metadata
    → full scan
```

This gives an attractive operational property:

> Disabling optimization should reduce performance, not correctness or semantic coverage.

---

# 26. Proposed source organization

The precise tree can evolve, but conceptually:

```text
L4Factoidal/

  RDF/
    ... existing semantic model ...

  SPARQL/
    ... existing semantics ...

    Physical/
      Model.lean
      Plan.lean
      Eval.lean
      Lower.lean
      Refinement.lean

    PushIR/
      Syntax.lean
      Validate.lean
      Eval.lean
      Compile.lean
      Refinement.lean

  Storage/

    TermId.lean

    Block/
      Model.lean
      Denotation.lean
      Scan.lean
      Prune.lean
      Join.lean
      CodecSimple.lean
      Manifest.lean
      Delta.lean
      Compact.lean

    Backend/
      Contract.lean
      Capabilities.lean
```

Backend-specific integration code should sit outside the semantic core where practical.

---

# 27. Revised first implementation vertical

The first coding milestone should be small enough to land quickly but meaningful enough to establish the architecture.

## Step 1 — RDF term identity contract

Select RDF 1.2 term identity explicitly. Repair the language-tag and
`rdf:XMLLiteral` split described in section 15. Prove the decision procedure
sound and complete for the chosen relation.

## Step 2 — TermId

Define logical/physical ID relation.

Do not optimize tagging prematurely.

## Step 3 — GraphId

Represent default versus named graph unambiguously.

## Step 4 — generalized immutable block type

Refactor one landed Cottas access shape into a backend-neutral block. Use one
simple permutation, probably one where a bound predicate produces a useful
sorted relation.

No compression required initially.

## Step 5 — block denotation

Define what logical quads the block represents.

## Step 6 — one bounded physical scan

For example:

```text
fixed predicate
optional subject/object bounds
```

## Step 7 — semantic bridge

Prove the scan returns exactly the result required by the existing RDF/SPARQL triple-pattern semantics for the supported fragment.

## Step 8 — native executable

Compile that implementation through the existing Lean native/C path.

## Step 9 — PostgreSQL persistence

Persist/read that identical block as opaque bytes plus metadata.

## Step 10 — differential end-to-end test

```text
semantic evaluator result
    =
in-memory block result
    =
PostgreSQL-persisted block result
```

This is already a small but real end-to-end assurance story.

---

# 28. Only then add compression

After the first vertical works:

```text
simple block
      ↓
compressed block
```

and prove:

```text
decode (encode b) = b
```

or an appropriately abstract equivalent.

Benchmark several codecs.

Do not assume QLever's exact choices are optimal for:

```text
mutable quads
revision metadata
PostgreSQL
TiKV
```

The transferable QLever insight is primarily:

> exploit sorted RDF integer structure aggressively.

The precise codec remains empirical.

---

# 29. Then add PushIR

Once block semantics are stable:

```text
PushIR v0:
    bound ID comparisons
    revision visibility
    projection
    COUNT
```

Compile only the corresponding SPARQL/physical fragments.

Run it first with the Lean evaluator.

Then invoke the same generated implementation through PostgreSQL.

Then through TiKV.

This gives a much cleaner progression than simultaneously designing:

```text
compression
distributed execution
complex joins
VM
optimizer
```

before anything is vertically connected.

---

# 30. Then add the genuinely SOTA work

Only after the common semantic/block/backend boundary is established should the project become aggressive:

```text
QLever-style compressed blocks
block-overlap pruning
vectorized merge joins
late materialization
SIMD intersection
galloping search
specialized RDF statistics
star-pattern indexes
materialized graph patterns
worst-case-optimal joins
region-aware distributed execution
continuous delta compaction
revision-native queries
```

At that stage PostgreSQL and TiKV can tell us different things.

PostgreSQL gives a strong single-system baseline and exceptional operational maturity.

TiKV gives the opportunity to investigate truly distributed RDF execution.

---

# 31. What constitutes “end-to-end verified” should remain precise

It would be easy to overclaim.

A result should not simply carry:

```text
verified: true
```

Instead report something like:

```text
semantic:
    Lean theorem-backed

block representation:
    Lean theorem-backed

physical planner:
    Lean executable
    selected refinements proved: [...]

PushIR:
    Lean compiler + evaluator
    refinement theorem: [...]

storage:
    PostgreSQL transactional snapshot
    external-system assumption

native executable:
    compiled from Lean source
    build provenance: ...

result:
    sha256:...
```

If later an AVX routine is substituted:

```text
SIMD intersection:
    external native optimization
    differential test suite: ...
```

The assurance frontier remains visible.

---

# 32. Immediate repository guidance

The refreshed repository is the starting point. On commit `73209342c232`,
Codex reports that the full Lean build passed all 719 jobs under Lean 4.33.1.
Native C and WASM paths exist. LLVM support is absent from the installed
toolchain.

It also created:

```text
docs/20260829-blockengine-baseline.md
skills/blockengine/SKILL.md
```

as the local durable handoff and working method.

Those should now be treated as the coding agent's repository-local source of truth about current implementation state.

The exploratory architecture documents remain design input, not a substitute for checking the tree.

---

# 33. Core principles, revised

The project should carry these rules explicitly.

### Principle 1 — executable formal core

Lean/F* is not merely where proofs live.

It is where assurance-critical algorithms should be implemented when practical.

### Principle 2 — refinement, not replacement

Optimized paths refine simpler executable paths.

### Principle 3 — conservative fallback

Failure to justify an optimization falls back to a slower semantically complete path.

### Principle 4 — physical independence

PostgreSQL and TiKV persist representations of RDF state; neither defines RDF or SPARQL semantics.

### Principle 5 — representation has semantics

Blocks, manifests, dictionaries, deltas and compaction all have explicit denotations.

### Principle 6 — pushdown is compilation

PushIR is a small, typed, bounded execution language compiled from physical SPARQL fragments.

### Principle 7 — assurance is graded

Total Lean, partial Lean, proved refinements, compiled code, external adapters and attestations are not conflated.

### Principle 8 — backend equivalence is demonstrable

The same logical dataset/query executed through PostgreSQL and TiKV should be capable of producing the same logical result identity despite different physical execution.

---

# 34. Concrete target for the next coding session

Do not begin with TiKV.

Do not begin with PostgreSQL.

Do not begin with a bytecode VM.

Begin by generalizing one landed Lean Cottas access shape:

```text
RDF 1.2 term identity contract
TermId
GraphId
Block
Block.denotes
one permutation
one scan
one theorem relating that scan to existing RDF/SPARQL semantics
```

Make it executable.

Benchmark it enough to ensure the representation is not pathological.

Then persist that exact object in PostgreSQL without changing its semantics.

That establishes the vertical seam everything else depends on:

```text
SPARQL semantics
      ↓
physical RDF representation
      ↓
executable Lean algorithm
      ↓
database persistence
      ↓
same logical result
```

Once that is real, both the QLever-inspired performance work and the TiKV distributed work have somewhere sound to attach.

---

# 35. Long-term architectural statement

The eventual system should be describable as:

```text
                    FACTOIDAL
                       │
              RDF / SPARQL semantics
                       │
                executable Lean
                       │
               physical compiler
                       │
           ┌───────────┴───────────┐
           │                       │
     coordinator plan          PushIR
           │                       │
           └───────────┬───────────┘
                       │
               Lean block engine
                       │
              compressed blocks
                 ╱           ╲
                ╱             ╲
          PostgreSQL          TiKV
              │                │
        transaction /      distributed
        durability         transaction /
                           replication
                ╲             ╱
                 ╲           ╱
                   execution
                       │
                       ▼
                     RESULT
                       │
                       ▼
            Factoidal evidence DAG
```

The distinctive proposition is not simply:

> “an RDF engine written in Lean.”

Nor is it:

> “a verified SPARQL implementation on a fast database.”

It is:

> **an RDF/SPARQL data-processing system in which logical semantics, executable algorithms, physical representation, query compilation, persistence transformations, optimized execution and provenance can be connected through an explicit chain of machine-checkable contracts and evidence.**

PostgreSQL and TiKV give us powerful storage machinery.

QLever gives us important evidence about how far specialized RDF physical structures can be pushed.

Lean/F* gives us the opportunity to make the route from source data to result unusually inspectable and unusually defensible.

That should remain the organizing principle of the project.
