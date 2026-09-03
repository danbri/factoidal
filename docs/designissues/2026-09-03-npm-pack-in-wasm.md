# Packing a store inside WebAssembly: what it needs

Owner instruction, 2026-09-03, verbatim:

> "Also please get the packing etc thing implemented and into WASM,
> Github and NPM so that the NPM module on its own can create and query
> a substantive RDF/SPARQL database. Don't worry about SPARQL protocol
> for now."

The npm package 0.3.0 can `inspect` and `query` a Shardborough store.
It cannot make one. This document states what is missing, why, and the
order of the work.

## What is NOT missing

Every format decision is already Lean and already compiles into the
shipped wasm module: IBK3 and IBK4 block encoding, the embedded PTD1
paged dictionary, SRI2/OLI2 postings, the TLI1 term index, the SBM6 and
SBM7 manifests, fixed-chunk Merkle commitments, SHA-256. The npm
package ships that module today (5,061,586 bytes, sha256
`9084903e6877151a357ade6122ece8c9be0f03be666318b558b5dedd2f48f732`).

## What IS missing

1. **No pack operation on the wasm surface.** `Wasm/Ops/Store.lean`
   exposes three operations, all read-only: `storeManifestInspect`,
   `storeQueryPlan`, `storeQuery`.

2. **Pack is a stateful two-pass fold and the wire entry is stateless.**
   `Harness/PredicateShardPack.lean` runs `prepassHandle` (line 88:
   SHA-256 of the input plus the term and predicate census) and then
   `ingestHandle` (line 213: block assembly) over a `Utf8Stream` fed by
   `TurtleChunkFold`. That state lives in the native IO loop.
   `l4_call_c` is one call in, one JSON string out.

3. **The harness writes the files itself.** Lines 129, 145, 160, 179,
   267 and 348 call `IO.FS.writeBinFile`. There is no file I/O inside
   the wasm module, by design: libuv is omitted from the Emscripten
   build and one stub `initialize_libuv` stands in for it. This is a
   build decision, not a WASI limitation. The engine must therefore
   RETURN each artifact and let the JavaScript host write it.

4. **No byte path out of the module.** `l4_call_blob_c` carries bytes
   IN; every result comes back as a NUL-terminated JSON string. An
   artifact returned as hex or base64 was rejected by the owner on
   2026-09-03 ("base64 sounds inefficient"); the measured cost of the
   hex transport on the read path was 242,416 bytes and 96 ms against
   4,893 bytes and 70 ms for the raw region.

5. **Address space and peak memory.** wasm32 addresses 4 GiB. Packing
   the skosdex corpus (2,771,180 quads, 410,280,495 bytes of N-Quads)
   natively peaked at 15,984,296,064 bytes of memory footprint with a
   4,721,262,592-byte resident set. A whole-file parse will not fit,
   and neither will the current fold. The streaming shape is forced,
   and the fold itself must emit each block as it completes instead of
   holding all 182.

## The work, in order

### Stage A — lift the pack out of IO

New `L4Factoidal/Storage/PackStream.lean`, pure and IO-free:

    structure Artifact where name : String; bytes : ByteArray
    structure PackState                 -- census, fold, emitted queue
    def packBegin  : PackFormat -> PackState
    def packFeed   : PackState -> ByteArray -> PackState
    def packFinish : PackState -> PackState × List Artifact

`Harness/PredicateShardPack.lean` is then rewritten to call it and to
do nothing but read the handle and `writeBinFile` what it is given.
The native gate is byte identity: the same input must produce the same
generation directory as today, artifact for artifact.

### Stage B — a byte path out of the module

`Wasm/Exports.lean` gains `l4_call_blob_io : String -> String ->
ByteArray -> IO (String × ByteArray)`, and `Wasm/l4_shim.c` gains

    char *l4_call_blob_io_c(const char *op, const char *args_json,
                            const uint8_t *blob, size_t blob_len,
                            uint8_t **out_ptr, size_t *out_len);

The shim copies the returned ByteArray into a malloc'd buffer, writes
its address and length through the out parameters, and returns the JSON
envelope as before. JavaScript reads `HEAPU8.subarray(ptr, ptr + len)`
and releases the buffer with `l4_free_result`. The shim still only
moves bytes; it interprets none of them.

### Stage C — the pack operations

New `Wasm/Ops/Pack.lean`, following the handle pattern of
`Wasm/Ops/Handles.lean` (the one place in the entry layer that holds
mutable state).

Stage A corrected the sketch this section first carried. The packer has
TWO bounded passes over the source, not one: the first computes the
source SHA-256 and the generated-blank-node prefix, which must avoid the
longest run of underscores in the WHOLE source and so cannot be known
from a prefix of it; the second parses and publishes blocks. The
operations therefore expose the pass, and a host feeds the source twice.

    packBegin(syntaxTag, layoutTag)
      syntaxTag : turtle | trig | nquads | ntriples
      layoutTag : ibk2 | ibk3 | ibk4
      -> {"ok":true,"handle":"p1","pass":"prepass"}

    packFeed(handle)          -- the chunk is the IN region
      -> {"ok":true,"pass":"prepass"|"ingest","pending":N}

    packEndPass(handle)
      -> {"ok":true,"pass":"ingest","pending":0}   -- after the first pass
      -> {"ok":true,"pass":"done","pending":N}     -- after the second

    packNext(handle)          -- one artifact in the OUT region
      -> {"ok":true,"name":"predicate-0.ibk3","bytes":N}
      -> {"ok":true,"done":true}

    packFinish(handle)
      -> {"ok":true,"rows":N,"blocks":N,"layout":"…","wireVersion":N,
          "pending":N}

    packClose(handle) -> {"ok":true}

The host drives it as: `packBegin`, feed the whole source, `packEndPass`,
feed the whole source again, `packEndPass`, drain `packNext`,
`packFinish`, drain `packNext`, `packClose`, draining after every feed.

`activateVerify(manifestHex, windowsJson)` over one IN region answers a
verdict — `{"ok":true,"artifacts":N,"bytes":N}` — so the host does the
atomic `CURRENT` replace it already implements in `store-host/`. Its
rules are `L4Factoidal/Storage/GenerationVerify.lean`, which
`Harness/ShardActivate.lean` also runs, so the native activator and the
wasm one reach the same verdict on the same bytes. It refuses SBM4 and
earlier: their SRI1 subject index needs positioned reads, which the
module does not have.

The IBK3 path streams. The IBK4 path buffers the source, because an IBK4
block commits a graph-set summary over the whole source; the module caps
that buffer, and the caps of `Wasm/Ops/Pack.lean` name themselves in
every refusal.

The gate is `lake exe l4wasm-cli pack`, which reaches the packer only
through `L4Wasm.callIO` and `L4Wasm.callBlobIO`. Measured 2026-09-03:
`gene.ttl` (17,363,312 bytes, 888,949 triples, 13 blocks) packed through
the operations wrote 106 files whose `shasum -a 256` list is identical to
`l4block-shard-pack`'s, and the heterogeneous fixture is identical under
both `ibk3` and `ibk4`.

### Stage D — the host

`npm/factoidal/bin/store.mjs` and `bin/factoidal.mjs`: `pack` streams
the input file in chunks through `packFeed`, drains `packNext` after
each feed and writes each artifact, then calls `packFinish`. `activate`
calls `activateVerify` and then `atomicReplace`. Neither parses a
manifest, computes a digest or decides an artifact name.

### Stage E — gates and release

`tests/store-host/` gains a pack-then-query conformance run on Node and
on Deno; the byte-identity check against the native packer is the gate
that matters. Then `skills/npm-release/SKILL.md` and a 0.4.0 release.

## The read caps, which this exposes

`Wasm/Ops/Store.lean` refuses a query plan above 64 artifacts, 8,388,608
blob bytes or 100,000 rows. On the skosdex store that refuses
`?s skos:broader ?o` (10,307,522 bytes, 138,080 rows), which the native
tool answers in 1.47 s. The caps are policy, not a wasm limit; raising
them belongs with the same streaming read path this work builds.

## The measurement this document is written against

skosdex `third_party/skos`, 2026-09-03: 726 vocabulary directories, 59
with `canonical.nq.gz` and 135 with a fetched source. Converted and
merged to 2,772,496 quads, 410,280,495 bytes of N-Quads. Packed with
`l4block-shard-pack … ibk4`: 2,771,180 quads, 182 blocks, 1 graph,
182 s. Generation size 279,789,930 bytes — 0.68 of the N-Quads text,
9.0 times the 31,003,388 bytes of `gzip -9`, which is not queryable.
The published 0.3.0 CLI answered `COUNT(*)` over `skos:notation` from
that store, reading 4,547,916 bytes of the 279 MB.
