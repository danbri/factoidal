# Block Engine Part Three: symbolic plans, dataflow, and portable execution

Date: 2026-08-30

Status: current design input. This document complements
[Part One](2026-08-blockengine.md),
[Part Two](2026-08-blockengine_part2.md), the
[repository baseline](20260829-blockengine-baseline.md), and the executable
[MVP](20260829-blockengine-mvp.md).

## Status boundary

The current Lean tree already supplies SPARQL algebra and evaluator code,
indexed-evaluation refinements, Cottas physical access reasoning, on-disk
read/write machinery, backend planning, and a working direct-term block scan.
The CLIF implementation also has a source-positioned S-expression reader.

The following are proposed block-engine layers, not landed implementations:

- a backend-neutral `PhysicalPlan` AST;
- a physical-plan S-expression renderer and constrained reader;
- named dataflow DAGs, execution records, and evidence links;
- `PushProgram` / PushIR and its interpreter;
- focused `block-core` and `sparql-edge` WASM artifacts;
- PostgreSQL and TiKV adapters.

Use the landed Lean Cottas and SPARQL mechanisms as the primary source for
these layers. Do not rebuild their behavior from F* or make a second query
engine in host code.

## Symbolic surface, typed core

The engine should expose a readable S-expression family in the style of Jena
SSE and Dydra algebra. It is a logical and diagnostic surface, not the wire
format or an untyped implementation language.

```text
human-readable S-expression
            <->
       typed Lean AST
            <->
canonical binary representation
            ->
      executable kernel
```

PostgreSQL, TiKV, WASM hosts, and other components may exchange protobuf,
CBOR, packed buffers, Parquet-derived structures, or another binary form.
Those forms do not replace the typed AST as the semantic API.

For logical SPARQL algebra, use familiar names where they fit:

```lisp
(project (?person ?name)
  (filter (> ?age 18)
    (join
      (bgp (triple ?person rdf:type :Person))
      (join
        (bgp (triple ?person :name ?name))
        (bgp (triple ?person :age ?age))))))
```

The physical language says how an operation is obtained, and is not
interchangeable with the logical one:

```lisp
(project (?person ?name)
  (merge-join :key ?person
    (scan :perm POSG :prefix (rdf:type :Person) :out (?person))
    (merge-join :key ?person
      (scan :perm PSOG :prefix (:name) :out (?person ?name))
      (scan :perm PSOG :prefix (:age) :out (?person ?age)
        :filter (> ?age 18)))))
```

Each language gets a separate Lean type and semantics, even where its printed
syntax is shared:

```lean
inductive LogicalPlan where
  | bgp | join | leftJoin | filter | project | union

inductive PhysicalPlan where
  | scan | mergeJoin | hashJoin | semiJoin | filter | project

inductive PushProgram where
  | scanRange | loadColumn | eqId | visibleAt | intersectSorted | count | emit
```

Each type should expose a renderer, a constrained reader, and a binary codec:

```lean
toSExpr   : T -> SExpr
fromSExpr : SExpr -> Except ParseError T
encode    : T -> ByteArray
decode    : ByteArray -> Except DecodeError T
```

Target round trips are `fromSExpr (toSExpr x) = x` and
`decode (encode x) = x`. Implement readers only for closed, versioned ASTs;
do not let an open symbol table acquire execution semantics.

## Shared substrate and language levels

A small common substrate is sufficient: symbols, strings, integers,
bytes/hashes, and lists. RDF and execution objects should have explicit forms:

```lisp
(iri "http://example.org/person")
(literal "42" xsd:integer)
(var "x")
(term-id 3819281)
(graph default)
(graph (named 99281))
(hash sha256 "...")
(ref node-17)
```

This keeps RDF terms, variables, physical IDs, plan-node references, artifact
identities, and program identities distinct. Persistent `term-id` forms wait
for the RDF 1.2 identity and cross-position `TermId` decision. Early plans
may use RDF terms and variables directly, as the MVP does.

Shared syntax does not make object language and metalanguage interchangeable.
An IKL proposition such as `(that (requiresReview invoice42))` differs in type
from `(code (scan ...))`, which denotes program syntax. IKL may refer to a
plan, program, artifact, execution, or claim about their relation; it does not
run the block-engine hot path.

```lisp
(asserts verifier-17
  (that (equivalent-results semantic-evaluation-4 execution-991)))
```

## Dataflow, artifacts, and visible lowering

Physical plans start as trees but grow into DAGs when common subplans, cache
use, placement, or execution evidence matter. Use named nodes instead of
encoding identity only through nesting:

```lisp
(flow query-17
  (node people (scan :perm POSG :prefix (rdf:type :Person) :out (?person)))
  (node names (scan :perm PSOG :prefix (:name) :out (?person ?name)))
  (node joined (merge-join :key ?person :inputs (@people @names)))
  (node result (project :vars (?person ?name) :input @joined))
  (output @result))
```

Nodes consume immutable values and produce immutable values. Content hashes
can identify blocks, snapshots, programs, and results. One node identity may
therefore connect the physical plan, runtime flow, estimates, provenance,
assurance, and diagnostic trace. Replay requires the operation, parameters,
and immutable inputs.

Keep lowering visible:

```text
SPARQL -> LogicalPlan -> PhysicalPlan -> PushProgram
```

The desired obligations are correspondingly explicit:

```text
denotePhysical(P) = denoteLogical(L)

compilePush(F) = X -> denotePush(X) = denotePhysical(F)
```

The first physical `scan` must execute the existing direct-term MVP scan and
inherit its `scan_eq_evalTP` refinement. A DAG wrapper and trace records come
after the tree-plan execution relation is established.

## PushIR and packaged execution

PushIR is a deliberately small dataflow subset of physical plans. It is typed,
versioned, deterministic, bounded, serializable, and easy to validate and
interpret. It has no unrestricted recursion, arbitrary memory access, or
general computation.

```lisp
(push
  (scan-range :perm POSG :prefix (42 918) :from 1000 :to 8000)
  (visible-at 103)
  (eq-id :column object :value 9912)
  (project subject)
  (count))
```

The primary WASM model is a stable Lean-derived kernel executing mobile
programs, rather than compiling each query into a new WASM module:

```text
factoidal-block-core.wasm + PushProgram + block bytes + snapshot -> result bytes
```

Compile only a narrow dependency closure into that kernel: IDs, layouts,
decoding, bounded scans, sorted intersection, revision filtering, PushIR, and
selected physical operators. Keep the full SPARQL parser, IKL parser, OWL,
SHACL, proof elaboration, and unrelated applications out unless a deployment
needs them.

Later packages may include `factoidal-block-core.wasm` for workers and
`factoidal-sparql-edge.wasm` for browser/mobile planning. Native and WASM
builds must use the same typed algorithms and contracts. A kernel hash,
program hash, input-block hashes, source commit, and Lean version can identify
an execution artifact across hosts.

Packed ID arrays, delta arrays, bit packing, run encoding, native SIMD, and
WASM SIMD are representation options. Choose their codecs by measurement.
They retain the public sequence-of-IDs meaning. Roaring32 remains a
block-local row/candidate representation, not a global term identifier.

## Hosting and diagnostics

PostgreSQL and TiKV integrations are thin hosts around the common kernel:

```text
block bytes + PushIR + snapshot/revision context -> kernel -> result bytes
```

Their transaction, range, placement, and byte-I/O responsibilities remain
outside Lean only where an explicit contract connects them to the pure model.
Do not move RDF identity, SPARQL compatibility, joins, filters, bag behavior,
or result ordering into host code.

Native deployments may use read-only memory mappings as a host-side byte
delivery optimization. The portable semantic boundary remains a bounded,
owned `ByteArray` consumed by the total decoder. Any later zero-copy mapped
view needs an explicit FFI, lifetime, bounds, and decoder-agreement contract;
it is not required for the first canonical codec or database byte stores.

Diagnostics should preserve each lowering stage:

```text
QUERY -> LOGICAL PLAN -> PHYSICAL FLOW -> PUSH PROGRAM -> EXECUTION RECORD
```

An execution record can include node identity, kernel and program hashes,
input/output row counts, blocks read, elapsed time, result hash, placement,
and a reference to its refinement or validation evidence.

## Immediate implementation order

1. Complete the RDF 1.2 identity and cross-position ID decisions.
2. Generalize one Cottas access shape into a local dictionary, one sorted
   permutation, and a bounded scan while preserving the MVP denotation.
3. Define a canonical block byte format. Prove either
   `decode (encode b) = some b`, or, where canonical encoding changes physical
   details, `denotes (decode (encode b)) = denotes b`. Prove the decoded-block
   scan against `SPARQL.evalTP`.
4. Persist these exact canonical bytes in PostgreSQL `bytea` and make its read
   path decode them. TiKV can then be an interchangeable realization of the
   same defined physical object, subject to its byte/range/snapshot contract.
5. Add a small tree `PhysicalPlan` whose first executable operator is that
   proved decoded scan; establish its execution/refinement relation.
6. Add a closed, versioned physical-plan S-expression renderer. Add a reader
   and binary codec only once this AST is stable enough to promise round trips.
7. Add named DAG nodes, immutable artifact references, and execution traces.
8. Define PushIR for proved physical fragments and its interpreter/refinement.
9. Extract the narrow native and WASM block-core slice. Add TiKV with its
   byte/range/snapshot agreement gates.

This sequence makes symbolic plans inspectable early without allowing syntax
work to postpone the storage identity and scan proof vertical.

The canonical byte layer also makes a separate Rust execution kernel less
justified: Lean defines, encodes, decodes, and evaluates the shared object;
database adapters persist bytes and supply host services.

## Design rule

Use a common S-expression family as the human-readable symbolic surface for
Common Logic/IKL objects, SPARQL algebra, physical query plans, dataflow
graphs, PushIR programs, executions, and evidence. Give each layer its own
typed Lean AST and semantics. Use efficient binary formats for transport and
storage without making them the conceptual API.

Compile small, explicit Lean slices into deployment artifacts. Prefer a
stable Lean-derived block kernel plus mobile PushIR/dataflow programs over
separately maintained backend engines.

```text
          Common Logic / IKL
                 ^ describes
                 |
SPARQL -> logical algebra -> physical dataflow -> PushIR
                                             |
                                      typed Lean block core
                                           /          \
                                      native          WASM
                                                      |
                                          PostgreSQL / TiKV / mobile / web
```
