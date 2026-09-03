# A browser reads a Shardborough generation: the three WASM store operations

Status: record of the design as it stands on 2026-09-03. Update this file when
an operation, its envelope, its transport or a cap changes; the worknote index,
the `lean4-wasm-export` skill and the `shardborough-storage` skill link here.

## 1. The problem

The WASM module has no file system. It is built with Emscripten without libuv,
`Wasm/l4_stubs.c` stubs exactly one symbol (`initialize_libuv`), and nothing
reachable from the exported ABI touches Lean's IO, socket or task layers — that
smallness is the standing purity evidence of `skills/lean4-wasm-export`. So a
JavaScript host must do the file reads.

Iron rule 7 of `CLAUDE.md` forbids hand-written JavaScript that reimplements
what the formal source defines. A host that parsed `manifest.sbm2`, chose
blocks for a query, checked a SHA-256 or decoded an IBK3 row would be a second
implementation of the storage format in a language with no proofs. The
operations below exist so it does none of that: it reads files by name and
carries bytes.

## 2. The three operations

All three are ordinary dispatch ops (`Wasm/Dispatch.lean`), so they ride the
existing `l4_call` / `l4_call_io` exports. `storeQuery` also has a byte region,
which needs the new `l4_call_blob` export of section 4.

### `storeManifestInspect(manifestHex)`

Decodes one manifest with `ShardManifest.decode?` and reports what the host
needs in order to fetch artifacts: wire version, layout label, blank-node
publication profile, term-registry version, whether the manifest carries a
fixed-chunk Merkle commitment, byte and row totals, and one record per entry —
artifact key, byte length, SHA-256 hexadecimal, chunk bytes, chunk count,
Merkle root, predicate IRI, row count, block kind (`IBK3` or `IBK4`),
blank-node scope, the graph-name set with the default graph marked
(`{"kind":"default"}`), and the sidecar keys that are present.

Nothing here is read from a block. Every value is committed by the manifest
bytes themselves. Bytes that do not decode are refused with the shared error
envelope; `decode?` returns `none` for anything `ShardManifest.valid` refuses,
so an inadmissible manifest never reaches the host as a half-answer.

### `storeQueryPlan(manifestHex, sparql)`

Reports the artifact keys the host must fetch, in manifest order, the open mode
the native tools print for the same decision, and the byte and row totals those
artifacts declare.

The selection is the collectors the native tools already use, not a second
planner:

| Generation | Collector | Mode string |
|---|---|---|
| IBK3 layouts, constant predicates | `ShardManifest.queryNativeConstantPredicates?` then `entriesForPredicates` | `ibk3-paged-merkle(N)` |
| IBK3 layouts, no constant-predicate plan | every entry | `ibk3-paged-merkle-full-manifest(N)` |
| SBM7 / `quad-ibk4-ptd1-merkle-v0` | `ShardManifest.quadEntriesForQuery` | `ibk4-full-manifest(N)` |

`N` is the distinct predicate count for the IBK3 modes and the entry count for
the IBK4 mode, which is what `l4block-id-v3-query` and `l4block-quad-query`
print in their `open-mode=NAME(n)` headers.

The section 18.6 EXISTS guard is carried by the collectors and is not restated
here. `queryNativeConstantPredicates?` and `queryQuadConstantPredicates?` both
answer `none` unless `Query.expressionsOutsidePatternExistsFree`, and a `none`
selects every entry — an EXISTS in a projection, a GROUP BY key, a HAVING
condition or an ORDER BY condition is evaluated against the active graph, so
the query must see the whole generation.

The plan applies no cap. A host uses it to decide what to fetch, and the caps
belong to the operation that reads bytes.

### `storeQuery(manifestHex, sparql, artifactsJson)` plus one blob region

Evaluates the query and answers the ordinary `queryDataset` envelope with
`"shards"` and `"mode"` placed before `"kind"`, so a host handles the result
exactly as it handles `queryDataset`.

What it checks before it answers:

1. The manifest decodes and is admitted.
2. The manifest carries a fixed-chunk Merkle commitment (`rangeCommitted`) —
   every layout the packer writes does.
3. Each supplied artifact's byte length and SHA-256 match its manifest entry.
   A mismatch names the key and refuses the whole query; no partially trusted
   generation is answered from. The digest is the pure Lean `Crypto.sha256`,
   the specification hash of section 6.3 of `docs/shardborough-storage-spec.md`.
4. Each block decodes under the codec its manifest layout names, and its
   decoded row count equals the entry's declared `rows` — the same admission
   `Harness/QuadQuery.lean` and `Harness/IndexedBlockV3Materialize.lean` apply
   natively.

The chunk Merkle ROOT is deliberately not recomputed. This operation reads
whole artifacts, so the full-artifact digest already covers every byte, and a
second pass would double the hashing cost. A host that fetches RANGES needs the
Merkle path and is a different operation.

An IBK3 generation gives a graph (the default graph); an IBK4 generation gives
a dataset through `Storage/QuadDataset.datasetOfQuads`, graph column `none`
being the default graph. An IBK4 dataset carrying a blank-node graph name takes
the reference evaluator, because `SPARQL/StoreDataset.materialiseDatasetBackend`
keeps only IRI-named graphs — the same rule the native quad tool applies.

## 3. Caps

A cap trip is an explicit error naming the cap and the value that exceeded it.
Nothing is truncated (anti-pattern 25).

| Cap | Value | Checked against |
|---|---|---|
| selected artifacts | 64 | the plan's entry count |
| total artifact bytes | 8388608 (8 MiB) | the manifest's declared extents, then again the supplied window lengths |
| total rows | 100000 | the manifest's declared row counts |

All three are checked from the manifest before a single byte is hashed. 8 MiB
is the byte budget `queryIBK3BlockSetPreview` already carries, and it is set by
the cost of the pure Lean SHA-256 rather than by memory: the hash is the
dominant term in a whole-artifact admission.

## 4. How artifact bytes cross the boundary

The dispatch ABI carries strings. Hexadecimal doubles every byte across the
boundary and then costs a character walk on the way in — the class of cost the
decoder work of 2026-09-03 was removing, and base64 only reduces the first term
to 1.33x while keeping the second. So `storeQuery` does not use either.

The host allocates ONE buffer inside the wasm heap (`_malloc`, already
exported), writes every artifact into it back to back with no encoding at all,
and calls the new `l4_call_blob_c`:

```c
char *l4_call_blob_c(const char *op, const char *args_json,
                     const uint8_t *blob, size_t blob_len);
```

The shim builds a Lean `ByteArray` from that region with one
`lean_alloc_sarray` plus one `memcpy` and calls the Lean export
`l4_call_blob : String -> String -> ByteArray -> String`. It moves bytes and
never interprets them: it holds no knowledge of any block, manifest or digest
format, and a change that gives it any belongs in Lean instead.

Which bytes belong to which artifact is said in `artifactsJson`:

```json
[{"key": "predicate-0.ibk3", "offset": 0, "len": 118769}]
```

Two properties follow, and they are why this shape was chosen over a
pointer/length pair per artifact or a blob-handle table:

* Lean never receives a host pointer. Every window is bounds-checked against
  the `ByteArray` Lean owns, so an offset past the end is an ordinary refusal
  (`storeQuery: artifact 'k' names blob bytes [a, b) but the call carried n
  blob bytes`), never a memory fault, and a stale pointer cannot be expressed.
* Nothing has a lifetime the host must track. The region is copied on entry, so
  the host frees its buffer as soon as the call returns. A handle table would
  add mutable state in the shim and a second free the host could forget.

`storeQuery` also accepts `{"key": …, "bytes": "<hex>"}`. That form exists so
the operation still answers through the plain `l4_call` entry, which carries no
region — diagnostics and small fixtures. A host must not use it. Exactly one of
the two forms may appear per artifact.

`storeManifestInspect` and `storeQueryPlan` take the manifest as hexadecimal.
A manifest is a few kilobytes, and one encoding for the small argument keeps
the three signatures uniform.

### Measured

Largest `sequence_variant` IBK3 block, 118,769 bytes; native `l4wasm-cli`,
whole operation including process start and Lean initialisation; mean of 10
runs, repeated twice:

| Path | Time | Args document |
|---|---|---|
| hexadecimal `"bytes"` | 96 ms, 97 ms | 242,416 bytes |
| blob region + windows | 71 ms, 70 ms | 4,893 bytes |

So the hexadecimal transport costs about a quarter of the whole operation for
one 116 KiB block, and its argument document is 49.5 times larger. The gap
widens on wasm32, where the character walk is slower than it is natively.

## 5. What these operations are NOT

* They read the manifest's committed artifacts only. A generation carrying a
  non-empty DLOG delta overlay is not served: the operations cannot see one,
  and answering the base generation as though it were current would be wrong.
  A host with a delta log uses the native tools.
* They are the full-artifact path. Every selected block is read whole; block
  SELECTION is what makes the read less than the whole generation. The
  selective SRI2 / OLI2 / TLI1 paths of `Harness/IndexedBlockV3Query.lean` need
  range reads and are not offered here.
* They are not an authenticated remote-worker API. Merkle range admission,
  sidecar selection and transport remain host responsibilities that this
  boundary does not claim.

## 6. Where the code is

| Path | Role |
|---|---|
| `formal/lean4/Wasm/Ops/Store.lean` | the three operations |
| `formal/lean4/L4Factoidal/Storage/ShardManifest.lean` | `isIbk3Layout`, `isIbk4Layout`, `predicateOrder`, the collectors |
| `formal/lean4/L4Factoidal/Storage/QuadDataset.lean` | the dataset an IBK4 quad sequence denotes, shared with `Harness/QuadQuery.lean` |
| `formal/lean4/Wasm/Dispatch.lean` | `blobOpNames`, `callBlob` |
| `formal/lean4/Wasm/Exports.lean` | `@[export l4_call_blob]` |
| `formal/lean4/Wasm/l4_shim.c` | `l4_call_blob_c` |
| `docs/web/hub/assets/l4/l4factoidal.js` | `l4.callBlob(op, args, bytes)` |
| `formal/lean4/Wasm/Main.lean` | `l4wasm-cli callblob <op> <argsJsonFile> <blobFile>` |

## 7. Gates

| Gate | What it covers |
|---|---|
| `bash formal/lean4/Wasm/native-smoke.sh` | every operation, both transports, the digest refusal, the window-overrun refusal, the artifact-cap refusal, and the `blobOps` reflection — through the native CLI, so an ABI fault and a wasm-toolchain fault stay distinguishable |
| `bash tools/wasm-store-query-smoke.sh` | the committed wasm module against generations the Lean packer just wrote, comparing rows with `l4block-id-v3-query` and `l4block-quad-query` |
| `bash tools/blockengine-ibk4-quad-smoke.sh` | the native IBK4 path the wasm operations are compared against |
