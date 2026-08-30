# Block engine worknote: symbolic-plan input

Date: 2026-08-30

Commit examined: `73209342c23212dca31d7f9ef7dbc37cbbdab814`

## Decision source

Owner-supplied Block Engine Part Three: symbolic plans, dataflow, and portable
Lean execution.

## Findings

- `CL/Clif.lean` already has a source-positioned `SExpr` reader. It is CLIF
  syntax infrastructure, not a general physical-plan language.
- `SPARQL/StorePlan.lean` supplies a backend-neutral planning seam and proved
  pattern-ordering properties. It is not yet a general typed Physical Plan IR.
- `Storage/BlockMvp.lean` supplies a direct physical scan with
  `scan_eq_evalTP`. It is the execution seed for a future physical `scan`
  operator.
- The MVP now also supplies `scanBound`, proved equal to
  `tripleMatchesBound`, and `l4block-mvp` parses a SPARQL SELECT query before
  routing it through the current backend evaluator.
- The repository has a Lean-to-WASM route, but no focused block-core artifact.
- Lean Cottas reads companion files once with `IO.FS.readBinFile` and then uses
  pure `ByteArray` readers. Its F* lineage used mmap handles; the Lean port has
  no mmap-backed `ByteArray` view.

## Recorded architecture

Use separate typed Lean ASTs for logical plans, physical tree plans, dataflow
DAGs, PushIR, and IKL/Common Logic artifacts. A shared S-expression family is
the readable serialization and diagnostic surface. Binary codecs are transport
and storage forms, not semantic replacements.

Keep Common Logic/IKL outside the hot execution path. It refers to plans,
programs, artifacts, executions, and claims about their relationships.

Use a stable Lean-derived block kernel with mobile PushIR and block inputs.
Do not make one WASM module per query. Native and WASM targets must execute the
same typed definitions.

## Revised next runnable unit

Do not add a universal S-expression evaluator. First settle RDF 1.2 identity,
then implement one local dictionary plus one sorted access path that preserves
the MVP denotation and scan refinement. Before PostgreSQL persistence, define
a canonical block byte format and prove either exact decode/encode round-trip
or denotation preservation under canonicalization. Then prove the decoded
block scan against `evalTP`.

PostgreSQL `bytea` and TiKV can persist the same canonical bytes only after
this gate. The following unit is a small typed `PhysicalPlan` tree containing
only that decoded scan, its evaluator, a refinement theorem, and a closed
renderer. This leaves no role for a separate Rust kernel: the Lean-derived
kernel defines the object, bytes, and execution semantics.

## SPARQL MVP extension

`BlockMvp.scanBound` now provides the backend candidate relation and proves
`scanBound_eq_tripleMatchesBound`. The native fixture injects that function
into `BackendReadOps`, parses a supplied SELECT query, prints its SSE algebra,
and evaluates it through `runSelectQueryBackendDataset`.

The default ordered BGP query returns two bindings. A supplied FILTER query
returns Alice only. The latter uses the repository's materialise-then-semantic
algebra path for FILTER; it does not claim a block-native FILTER operator yet.

Verified on 2026-08-30 from `formal/lean4/`:

```text
lake build l4block-mvp -> Build completed successfully (104 jobs)
l4block-mvp default   -> rows=2
l4block-mvp FILTER    -> rows=1
```

## Memory-mapped bytes

Memory mapping is feasible for native PostgreSQL workers and standalone
processes, but it remains a host I/O boundary. The first portable format and
its decoder take an owned `ByteArray`; this is the object covered by the
canonical-byte and denotation theorems.

An optional native mmap adapter may own a read-only mapping, bounds-check each
range, and copy the required range into a `ByteArray` for the Lean decoder.
This permits OS page-cache behavior without giving unproved pointer access a
semantic role. A later zero-copy `MappedBytes` interface needs an explicit FFI
boundary, lifetime and bounds contract, and a decoder-agreement test. It is
not required for PostgreSQL `bytea`, TiKV, or the first codec.

## Files updated

- `docs/2026-08-blockengine_part3.md`
- `docs/20260829-blockengine-baseline.md`
- `docs/20260829-blockengine-mvp.md`
- `skills/blockengine/SKILL.md`

## Validation

The symbolic-plan update began as documentation-only work. The SPARQL MVP
extension changed Lean source and is verified above. The latest full-build
result remains recorded in `20260829-blockengine-mvp.md`.

## Lean-derived WASM physical scan (2026-08-30)

The regenerated browser artifact now exports `scanIBK2Predicate` through the
existing `l4_call_c` dispatch ABI.  It accepts canonical IBK2 bytes and a
predicate IRI, validates the complete block, and invokes the same selective
scan used by the native code.  The current JSON transport uses hexadecimal
bytes only as a portable diagnostic ABI; a worker-grade ABI must pass bounded
byte buffers directly.

The generated 4.3 MiB artifact was exercised under Node against the 4,621-byte
music IBK2 object.  Its dispatch table contained the operation and the scan of
`http://example.org/music/by` returned eight rows.  The repeatable check is:

```text
node tools/wasm-ibk2-smoke.mjs BLOCK.ibk2 PREDICATE_IRI EXPECTED_ROWS
```

This is a narrow Lean-derived physical helper, not the final `PushIR` kernel
or evidence of a PostgreSQL/TiKV embedded worker.
