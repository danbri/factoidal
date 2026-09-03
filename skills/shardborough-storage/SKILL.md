---
name: shardborough-storage
description: Operate and extend the Lean 4 persisted RDF store (Shardborough) — pack Turtle into IBK3 generations, activate through CURRENT, query the activated collection, apply SPARQL Update through the delta log, compact, and read the format registry, the corpus ladder, the executability census and the round-trip theorem status. Use for any l4block-* CLI question or on-disk Lean storage work; not for the F* COTTAS store (see disk-storage-format).
---

# Shardborough storage: the Lean persisted path

Shardborough is the Lean 4 tree's on-disk RDF store family: predicate-local
`IBK3` blocks with an embedded `PTD1` paged dictionary, `SRI2`/`OLI2`
postings sidecars, a `TLI1` term index, an `SBM6` manifest with Merkle chunk
commitments, a `DLOG` durable delta log, and a `CURRENT` pointer that
activates one immutable generation. The normative description is
[`docs/shardborough-storage-spec.md`](../../docs/shardborough-storage-spec.md);
this skill is the operating manual. Every command below was run on
2026-09-02 against `examples/wikidata/subsets/lifesci-kgx/data/sequence_variant.ttl`
(6,455 triples) and the outputs quoted are from that run.

All binaries live in `formal/lean4/.lake/build/bin/` after
`cd formal/lean4 && lake build` (run Lake only from `formal/lean4/`). Below,
`$B` is that directory.

## The lifecycle in five commands

```bash
# 1. Pack: Turtle -> one immutable generation directory
$B/l4block-shard-pack INPUT.ttl COLLECTION/gen-1 ibk3
# prints: format=predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0 triples=6455 blocks=5
#         manifest=manifest.sbm2 wire-version=6 chunk-bytes=65536

# 2. Activate: verify every artifact and cross-artifact relation, then
#    atomically write COLLECTION/CURRENT = "gen-1"
$B/l4block-shard-activate COLLECTION gen-1
# prints: verified-logical-bytes=393735 pointer=CURRENT

# 3. Query the ACTIVATED COLLECTION ROOT (not the generation directory)
$B/l4block-id-v3-query COLLECTION --query 'SELECT (COUNT(*) AS ?n) WHERE { ?v <http://www.wikidata.org/prop/direct/P1057> ?c }'
# prints the SSE plan, then: rows=1 preview=[[("n", ... "1357" ...)]]

# 4. Update: append a durable delta batch (routed through CURRENT);
#    the query path replays committed batches, so it is visible at once
$B/l4block-delta-log COLLECTION --update 'INSERT DATA { <http://example.org/a> <http://example.org/b> <http://example.org/c> }'
# prints: committed path=.../gen-1/deltas.dlog seq=1 epoch=1 ops=1 sync=file
$B/l4block-delta-log COLLECTION/gen-1 --inspect
# prints: committed-batches=1 committed-ops=1 clean-tail=true

# 5. Compact: fold the delta history into a fresh generation, then activate it
$B/l4block-shard-compact COLLECTION/gen-1 COLLECTION/gen-2
# prints: base-triples=6455 delta-batches=1 compacted-triples=6456 epoch=1
$B/l4block-shard-activate COLLECTION gen-2
```

Rules the commands enforce:

- **A failed pack or activation never becomes current.** `CURRENT` is
  replaced only after full verification; readers keep the previous
  generation until then.
- **Query the collection root.** `l4block-id-v3-query` on a generation
  directory is refused with "SBM5 and later require an activated collection
  root (CURRENT)". The older `l4block-shard-query` and
  `l4block-shard-merkle-query` read pre-SBM5 layouts (`manifest.sbm0`) and
  reject current generations; they are kept for the superseded formats.
- **An empty input packs and activates an empty generation.** Seen
  2026-09-02: a broken TriG-to-Turtle conversion produced a 0-byte file,
  `l4block-shard-pack` reported `triples=0 blocks=0` and
  `l4block-shard-activate` made it current with `verified-logical-bytes=0`.
  Read the `triples=` count in the pack output before activating; an empty
  RDF dataset is valid, so the tools do not refuse it.
- **TriG input.** The packer reads Turtle. A TriG file whose only block is
  an unlabelled `{ … }` (the default graph, as in the UK Parliament dump) is
  Turtle after dropping that line and the closing `}`:
  `awk 'NR==<line> && $0 ~ /^\{[[:space:]]*$/ {next} {print}' FILE.trig | sed '$d' > FILE.ttl`.
  A TriG file with named graphs waits on the quad-aware layout
  (`docs/designissues/2026-09-02-quad-aware-block-layout.md`).
- **Updates route through CURRENT.** `l4block-delta-log COLLECTION --update`
  appends to the active generation's `deltas.dlog`; passing the generation
  directory does the same. Replay is exactly the valid suffix after the
  compacted epoch, so a crash between compaction and activation cannot
  apply a batch twice (spec section 2.3).

## What a generation directory contains

```
manifest.sbm2            SBM manifest (wire version 6 = SBM6 content)
manifest.tsv             human-readable artifact table
predicate-N.ibk3         one predicate's rows + embedded PTD1 dictionary
predicate-N.ibk3.merkle  32-byte leaf hashes per 65,536-byte chunk
predicate-N.ibk3.sri2    subject -> row offsets (SRI2 postings codec)
predicate-N.ibk3.oli2    object  -> row offsets (same codec, object role)
predicate-N.ibk3.tli1    canonical term bytes -> local ID
*.merkle                 one per sidecar
deltas.dlog              appears after the first --update
compacted.epoch          CEP1 marker, written by compaction
compacted.source.sha256  identity of the source generation compaction read
```

Format registry with status and executable definitions: spec section 6.
Round-trip theorem status per codec: spec section 10.1 (term codec, PTD1 and
IBK3 proved 2026-09-02 with `encode? = some bytes` as the only hypothesis;
SRI2/OLI2 and TLI1 in progress the same day; SBM6 and Merkle range admission
open).

`IBK4`, the quad-aware block (a graph column in every row, a header graph-set
summary, the same PTD1 dictionary), is defined in spec section 6.1.1 and
proved in `Storage/IndexedBlockWireV4Theorems.lean` (2026-09-03). `SBM7` is
its manifest (spec section 6.3.1). `l4block-shard-pack ... ibk4` writes a
quad generation, `l4block-shard-activate` admits one, and
`l4block-quad-query` runs SPARQL over it; the graph-aware index sidecars are
not written yet.

## Other CLIs, by purpose

| Purpose | Command |
| --- | --- |
| Query a Turtle file directly (no persistence; reference path) | `l4block-corpus PATH.ttl --query SELECT...` |
| Predicate histogram of a file | `l4block-corpus PATH.ttl [PREDICATE-IRI]` |
| Verified range read of one block | `l4block-shard-merkle-pread SHARD-DIR PREDICATE-IRI [OFFSET LENGTH]` |
| Bounded Merkle scan or row range | `l4block-id-v3-merkle-scan SHARD-DIR PREDICATE-IRI LIMIT` / `--range START COUNT` |
| Convert an IBK2 block to IBK3 | `l4block-id-v3-convert INPUT.ibk2 OUTPUT-DIR PREDICATE-IRI` |
| Session of many SELECTs over one shard | `l4block-shard-merkle-session SHARD-DIR < queries.rq` |
| Pack a quad generation (IBK4, SBM7) | `l4block-shard-pack INPUT OUTPUT-DIR ibk4` (`.trig`, `.nq`, `.ttl`) |
| Query an activated quad generation | `l4block-quad-query COLLECTION-ROOT --query SELECT...` |
| Superseded formats (BLK0, IBK1, IBK2) | `l4block-pack`, `l4block-id-pack`, `l4block-id-v2-pack` and their `*-file-query` / `*-diff` partners |

`l4block-shard-merkle-query SHARD-DIR --explain|--explain-json|--explain-analyze` prints the physical plan and, with `-analyze`, the executed
read trace; it targets the Merkle session layout, not an SBM6 collection.

## IBK4 generations (quad-aware, landed 2026-09-03)

`l4block-shard-pack INPUT OUTPUT ibk4` writes a quad generation: one IBK4
block per predicate ACROSS ALL GRAPHS, with a graph column in every row and a
graph-set summary in the block header and in the SBM7 manifest entry. The
input syntax comes from the file extension — `.trig`, `.nq`/`.nquads`, and
anything else as Turtle with every triple in the default graph.

```bash
l4block-shard-pack tests/local/data/quad_sample.trig /tmp/store/gen-1 ibk4
# format=quad-ibk4-ptd1-merkle-v0 syntax=trig quads=6 blocks=2 graphs=3
# manifest=manifest.sbm2 wire-version=7 blank-node-scope=<source SHA-256 hex>
l4block-shard-activate /tmp/store gen-1
l4block-quad-query /tmp/store --query 'SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }'
```

What works:

- Pack from TriG, N-Quads and Turtle. The same quads in the same order from
  either syntax give byte-identical blocks.
- One `.merkle` leaf sidecar per block, and an SBM7 manifest committing the
  source file's SHA-256 as each entry's blank-node scope under the
  `content-digest-shared` publication profile.
- Activation: full SHA-256, rebuilt Merkle leaves and root, an
  `IndexedBlockWireV4.decode` of every artifact, and a check that the block's
  graph set equals the manifest entry's summary.
- **SPARQL through `l4block-quad-query`** (landed 2026-09-03; see the next
  subsection).
- `tools/blockengine-ibk4-quad-smoke.sh` and
  `tools/blockengine-ibk4-w3c-trig-smoke.sh` (241 pass, 0 fail out of 241
  positive W3C TriG 1.1 tests).

What does NOT work yet:

- **No index sidecars.** SRI2, OLI2 and TLI1 are keyed by a block-local ID
  with no graph dimension, so they cannot describe an IBK4 artifact, and SBM7
  admits none. Every selected block is therefore read whole; there is no
  selective row access path. The graph-aware sidecars are the next piece of
  work.
- **No streaming pack.** The IBK4 path parses the whole input file before it
  writes a block, because an IBK4 block commits its graph-set summary in the
  header and a batch boundary would split a predicate across blocks with
  partial graph sets. The IBK3 path is still the streaming one.
- **No compaction and no delta log.** There is no compacted SBM7 layout label.

### Querying an IBK4 generation

`l4block-quad-query COLLECTION-ROOT --query SELECT...` opens the activated
generation through `CURRENT`, decodes the blocks the planner selects, builds
the RDF DATASET they denote (default graph = the rows whose graph column is
`none`, one named graph per graph name), and evaluates the query with
`env.dataset` set to that dataset. `GRAPH <iri>`, `GRAPH ?g`, default-graph
patterns, `FROM`, `FROM NAMED`, SELECT, ASK and CONSTRUCT all work.

It is a SIBLING of `l4block-id-v3-query`, not an arm of it, and
`l4block-id-v3-query` still refuses SBM7 by layout. The reason is structural:
every selective access path in the IBK3 tool is driven by an SRI2, OLI2 or
TLI1 sidecar, and SBM7 admits none; and the IBK3 tool threads a `List Triple`
plus a resolved DLOG overlay, where an IBK4 generation yields a dataset and
carries no delta log. Revisit the split when the graph-aware sidecars land.

**Block selection** (`ShardManifest.quadEntriesForQuery`) is what makes this
less than a whole-store read. An entry survives unless one of two collectors
excludes it:

| Collector | Excludes an entry when | Gives up (keeps everything) when |
| --- | --- | --- |
| `queryQuadConstantPredicates?` | the entry's predicate is not one the pattern names | a triple pattern or path step has a variable predicate; a `{}` or empty BGP under a `GRAPH` clause; a non-`backendLocal` FILTER / OPTIONAL / BIND expression; a sub-SELECT, SERVICE, LATERAL or VALUES |
| `queryGraphNames?` | the entry's manifest `graphSet` meets none of the names the pattern reads | `GRAPH ?v`; the query carries `FROM` / `FROM NAMED`; the same expression and pattern forms as above |

Both are refused outright unless `Query.expressionsOutsidePatternExistsFree`
holds, because section 18.6 evaluates an `EXISTS` in the projection, a
GROUP BY key, a HAVING condition or an ORDER BY condition against the ACTIVE
GRAPH, and neither collector reads those positions (the same guard
`l4block-id-v3-query` carries,
[issue 638](https://github.com/danbri/factoidal/issues/638)).

Two rules that look small and are not:

- `GRAPH <g> { }` reads no row but still asks whether the dataset names `g`,
  so the graph collector adds `<g>` itself, and the predicate collector gives
  up on an empty group under a `GRAPH` clause. Without both, an entry that
  puts `g` into the dataset could be skipped and the query would answer zero
  rows instead of one.
- A query with `FROM` gets no graph-based selection at all. Section 13.2
  rebuilds the default graph out of the `FROM` graphs, so a default-graph
  pattern under `FROM <g>` reads `<g>` and not the default graph.

The mode line names the path:

```
l4block-quad-query shards=1 open-mode=ibk4-full-manifest(1) graphs=2 logical-read-bytes=554 fetched-bytes=554
```

`ibk4-full-manifest` is the indexed backend path
(`StoreDataset.indexedDatasetBackend`). `ibk4-full-manifest-reference` is the
same answer through the reference evaluator, taken when the generation has a
graph whose NAME is a blank node: `materialiseDatasetBackend` keeps only
graphs with a well-formed IRI name, so the delegating arms of the backend
seam would lose such a graph.

Gate: `tools/blockengine-ibk4-quad-smoke.sh`.

## Browser and WASM path

The same Lean decoder runs in the browser through the WASM dispatch
operations `scanIBK3Predicate` (one complete block, hex transport) and
`queryIBK3BlockSetPreview` (up to 8 blocks / 8 MiB / 100,000 rows, RDF kept
inside Lean). Hub posts 50 and 51 use them with an Origin Private File
System cache; the caller must check each block's byte length and SHA-256
against the manifest before decoding. This is the diagnostic worker, not the
bounded protocol worker of spec section 2.4.2.

## Corpus ladder, profiling and the census

- Corpus ladder (which files are used at which size rung, and the rules
  every rung follows): [`docs/20260901-corpus-ladder-catalogue.md`](../../docs/20260901-corpus-ladder-catalogue.md).
  Rungs 1 and 2 are in the repository (`formal/lean4/Harness/TestData/`,
  `examples/wikidata/subsets/lifesci-kgx/data/`).
- Profile one file for the ladder (bytes, SHA-256, engine-counted
  statements, predicate and object-kind histograms):
  `tools/corpus-profile.sh FILE`.
- Executability and row-agreement census of the W3C SPARQL
  QueryEvaluationTests through the persisted path (pack, activate, query,
  then compare the answer with the reference in-memory engine over the same
  file; NOT a pass/fail conformance result — that is `lake exe l4w3c`):
  `tools/w3c-persisted-census.sh`, results in
  [`docs/20260901-persisted-executability-census.md`](../../docs/20260901-persisted-executability-census.md).
  Measured 2026-09-03: default graph 535 executed, 535 matched, 0 differed
  (out of 535 eligible); named graphs 29 executed, 29 matched, 0 differed
  (out of 35 eligible `qt:graphData` entries; the 6 refusals all carry a
  relative IRI in the query text, which no query CLI resolves).
- Parser differential for the N-Quads path the browser uses:
  `tools/nquads-parser-differential.sh FILE.nq`.

## Where the code is

- Codecs and pure validators: `formal/lean4/L4Factoidal/Storage/`
  (`IndexedBlockWireV3`, `PagedTermDictionary`, `SubjectRowIndexWireV2`,
  `TermLocalIndexWire`, `ShardManifest`, `DeltaLog`; theorems in the
  `*Theorems.lean` siblings).
- Host I/O, packing, activation, compaction, query CLIs:
  `formal/lean4/Harness/` (`PredicateShardPack`, `ShardActivate`,
  `IndexedBlockV3Query`, `DeltaLogTool`, `PosixRangeIO` — the one host
  `extern_lib`, `libl4blockhost`, for `pread`, append-with-fsync and atomic
  replace).
- WASM operations: `formal/lean4/Wasm/Ops/Block.lean`, dispatch table in
  `Wasm/Dispatch.lean`, native checks in `Wasm/native-smoke.sh`.
- Design records, with status: [`docs/worknotes-index.md`](../../docs/worknotes-index.md).

## Rules when changing a format

1. The Lean definition is the format. Change `encode?`/`decode?` in the
   codec module, keep or extend the round-trip theorem in the sibling
   `*Theorems.lean`, and keep the encoder's `supported` equal to the
   decoder's admission (the 2026-09-02 rule: the encoder refuses exactly
   what the decoder would refuse, so the theorem has no side hypotheses).
2. A byte change is a new wire version. Bump the format name (IBK3 to
   IBK4, SBM6 to SBM7) rather than changing bytes under a name; the alpha
   allows repacking, it does not allow silent drift (spec section 10).
3. Rebuild the WASM mirrors after any change under `L4Factoidal/` that the
   dispatch operations can reach (`bash formal/lean4/Wasm/build-wasm.sh`,
   about ten minutes), then `node --test tests/hub/*_test.mjs`.
4. Re-run the lifecycle above on a rung-2 file and compare the packed block
   bytes with the committed hub blocks under
   `docs/web/hub/assets/blocks/lifesci-crossgraph/` (a codec change that
   keeps the format must reproduce them byte for byte).
