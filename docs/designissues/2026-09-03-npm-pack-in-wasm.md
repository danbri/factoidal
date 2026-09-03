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

## The call stack the pack needs, and what a browser cannot give it

Added 2026-09-04, https://github.com/danbri/factoidal/issues/649.

The pack completed and was byte-identical at every size that finished,
but on the DEFAULT stack of Node 22.22.2 and of Deno 2.9.4 it ended with
`Maximum call stack size exceeded` above roughly 0.25 MB of Turtle. The
pack fold recurses far deeper per input chunk than a query does per row.

### What was measured

`examples/wikidata/subsets/lifesci-kgx/data/gene.ttl`, 17,363,312 bytes,
888,949 triples, packed on a Node worker thread with
`resourceLimits.stackSizeMb` set by hand (macOS 15 arm64, Node 22.22.2):

| stackSizeMb | verdict |
|---|---|
| 4 (the Node default) | Maximum call stack size exceeded |
| 6 | Maximum call stack size exceeded |
| 7 | Maximum call stack size exceeded |
| 8 | pass |
| 10 | pass |
| 64 | pass |

8 MiB is the measured minimum for the largest input in the corpus.
`npm/factoidal/bin/pack-host.mjs` asks for **64 MiB**, eight times that.
The headroom is deliberate: recursion depth grows with the input, so a
value just above the minimum moves the same defect to a larger file. It
is also cheap, because a thread stack is reserved address space and only
the pages actually touched become resident.

### Where the frames are, and what sets their number

The overflow is entirely inside the WebAssembly module, in ONE
self-recursive function at ONE call site. Captured on Node 22.22.2 with
`Error.stackTraceLimit = Infinity`, packing `biological_pathway.ttl`
(1,475,535 bytes) on the default main-thread stack:

    frames: 7890
    distinct sites: 26
    7865 at wasm://wasm/01434066:wasm-function[3201]:0x389740
    1 at wasm://wasm/01434066:wasm-function[1577]:0x1c0095
    1 at wasm://wasm/01434066:wasm-function[2336]:0x28e0dc
    ...

7,865 of 7,890 frames are the same function returning to the same
address. No JavaScript frame appears above the entry point, so nothing
on the host side recurses. Node's default main-thread budget is about
1 MiB, which puts one frame at roughly 130 bytes.

The number of frames does NOT follow the input size, the total row
count, or the number of publication batches. It follows ONE BLOCK.
Measured 2026-09-04, IBK3, `--layout ibk3`; "default stack" is
`--no-worker` on Node's main thread, and "min stack" is the smallest
`resourceLimits.stackSizeMb` that packs:

| fixture | bytes | blocks | total rows | largest block, rows | default stack | min stack |
|---|---|---|---|---|---|---|
| `chemical_compound.ttl` | 6,620 | 6 | 130 | 103 | pass | 1 MiB |
| `medication.ttl` | 176,609 | 7 | 6,780 | 3,928 | pass | 1 MiB |
| `sequence_variant.ttl` | 241,149 | 5 | 6,455 | 1,800 | pass | 1 MiB |
| `chromosome.ttl` | 316,116 | 1 | 9,227 | 9,227 | FAIL | 2 MiB |
| `protein_domain.ttl` | 664,327 | 3 | 18,865 | 11,736 | FAIL | 2 MiB |
| `disease.ttl` | 855,549 | 6 | 27,421 | 13,283 | FAIL | 2 MiB |
| `Protein__protein2.ttl` | 1,342,034 | 2 | 44,756 | 30,968 | FAIL | 3 MiB |
| `biological_pathway.ttl` | 1,475,535 | 3 | 67,219 | 60,930 | FAIL | 4 MiB |
| `protein_family.ttl` | 2,347,031 | 2 | 65,475 | 44,631 | FAIL | 6 MiB |
| `labels-en.ttl` | 2,594,952 | 1 | 31,325 | 31,325 | FAIL | 8 MiB |
| `anatomical_structure.ttl` | 3,811,378 | 3 | 112,742 | 45,782 | FAIL | 6 MiB |
| `gene.ttl` | 17,363,312 | 13 | 888,949 | 256,698 | FAIL | 8 MiB |

Three readings of that table:

1. **Not the file.** `chromosome.ttl`, `protein_domain.ttl` and
   `disease.ttl` need the same 2 MiB while their sizes differ by 2.7
   times and their total row counts by 3 times.
2. **Not the batch.** `Storage/PackStream.lean` publishes every 64
   chunks of 65,536 bytes, so everything up to 4 MiB of input publishes
   exactly once. `sequence_variant.ttl` passes and `chromosome.ttl`
   fails, and both publish once. Batch contents decide it, not batch
   count.
3. **Not the total row count, and not the largest block's row count
   either.** `gene.ttl` has a block of 256,698 rows and needs 8 MiB;
   `labels-en.ttl` has one block of 31,325 rows and needs the same
   8 MiB. Eight times the rows, the same stack.
4. **The block's DICTIONARY, which row count only sometimes tracks.**
   `labels-en.ttl` is one `rdfs:label` predicate whose object is a
   distinct literal on every row, so its 31,325 rows carry about 62,000
   distinct terms — the worst ratio in the corpus.
   `biological_pathway.ttl` repeats its objects and needs 4 MiB for
   60,930 rows; `gene.ttl`'s largest blocks repeat theirs far more. At
   about 7,800 frames per MiB, 62,000 terms is 8 MiB, and that rate
   agrees with the 7,865 frames measured directly at 1 MiB.

So the depth is one frame per TERM in one block's local term index.
That is the shape of `entriesGo` in
`formal/lean4/L4Factoidal/Storage/TermLocalIndex.lean`, which conses
after its recursive call and is therefore not tail recursive. The
native tool survives it on an 8 MiB thread stack; a browser gives about
1 MiB.

**The consequence.** The worker stack is the right immediate fix for
Node and Deno, and it is what this change lands. It is not the cure.
The cure is to make that fold tail recursive in the Lean source, which
is the same change https://github.com/danbri/factoidal/issues/647 wants
for the pack profile, and it is the only route to an in-page packer.

### The two host routes

- **Node** runs the pack on a `worker_threads` worker with
  `resourceLimits.stackSizeMb`. The engine loads inside the worker, and
  the worker writes every artifact itself through the same `store-host`
  primitives, so no artifact byte crosses the thread boundary.
- **Deno** takes neither `worker_threads` nor a stack size on its own
  `Worker`. The command re-executes itself once with
  `--v8-flags=--stack-size=…`, guarded by `FACTOIDAL_PACK_STACK_REEXEC`
  so it cannot loop, and with exactly the permissions the parent process
  was granted, queried rather than requested so no prompt appears. Deno
  2.9.4 / V8 15.0.245.2 honours the flag.

`--no-worker`, or `FACTOIDAL_NO_WORKER` in the environment, forces the
in-process path. That path still prints the frame-budget advice
(`bin/store.mjs`, `stackLimitAdvice`), which is also what a reader sees
if the raised stack is refused or is still not enough.

### What this does NOT fix: an in-page packer

A browser tab has a fixed frame budget and no host flag. Chrome gives a
main-thread JavaScript stack of about 984 KiB and a `Worker` about the
same; Firefox gives about 1 MiB. `postMessage` cannot raise it, and
`--js-flags` is a command-line switch on the browser binary, not
something a page can set. So neither route above reaches a page.

A page therefore gets what the `min stack` column above calls 1 MiB:
`sequence_variant.ttl` (241,149 bytes, largest block 1,800 rows) is the
largest fixture measured that packs there, and `chromosome.ttl`
(316,116 bytes, one block of 9,227 rows) is the smallest that does not.
Roughly, a page can pack a block holding up to about 7,800 terms and no
more, whatever the file size.

An in-page packer needs that recursion bounded, not a bigger stack:
`entriesGo` and any sibling with the same shape must become an
accumulator fold, which is what `formal/lean4` already does for its
retired `partial def`s (`skills/lean4-proof-patterns`). Until that
lands, in-page import is not promised.
