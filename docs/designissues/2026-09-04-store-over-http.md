# A Shardborough store over an HTTP object store

Owner, 2026-09-04:

> "a page ought to be able to import incrementally and write data into
> whatever cloud rest api it can?"

Yes. This document states what already supports it, what one piece does
not, and what is still in the way.

## The read path is already a range protocol

`npm/factoidal/store-host` realises four primitives from
`formal/lean4/Harness/PosixRangeIO.lean`. One of them is

    readRange(path, offset, length) -> exactly `length` bytes

which is an HTTP `Range` request written in POSIX terms. The query path
uses it because the manifest already commits, for every artifact, its
name, its byte length and its SHA-256; `storeQueryPlan` chooses which
artifacts a query needs BEFORE any of them is read.

The consequence is that a plain static object store — S3, R2, GCS, or
GitHub Pages — is a queryable RDF store with no server process. The
client:

1. GETs `CURRENT` (a few bytes) and then the manifest;
2. asks the engine which artifacts the query needs;
3. issues one ranged GET per artifact;
4. hands the bytes to the engine, which verifies each against the
   SHA-256 the manifest commits before it answers.

Step 4 is what makes an untrusted transport acceptable. A corrupted or
substituted artifact is refused by name, and that refusal already has a
test (`tests/store-host/cli.mjs`, "a damaged artifact is refused and the
key is named").

Measured on the skosdex store (2,771,180 quads, 279,574,394 bytes, 182
blocks), a bound-predicate query read 4,547,916 bytes — 1.6 percent of
the store. That ratio is what makes a ranged read over a network
worthwhile rather than merely possible.

## The write path needs one new sink, and no engine change

`packBegin` / `packFeed` / `packNext` / `packFinish` never write
anything. The engine answers `{name, bytes}` and the host puts the bytes
somewhere. The whole filesystem dependency of a pack is `writeNew` in
`store-host`. An HTTP host realises it as a `PUT`.

Two properties make this safe over a network:

- Artifacts are immutable once written and named by content. A failed
  upload is retried, not repaired.
- The manifest is published LAST, and only after the second-pass source
  digest agrees with the first pass. A generation whose upload was
  interrupted has no manifest, so no reader can activate it.

## The one piece that is not a plain object write

`CURRENT` is the single mutable byte range in the design. Activation
must be atomic, or a reader sees a generation that is half uploaded.

Locally this is `atomicReplace`: write a temporary, fsync, rename, fsync
the directory. On an S3-compatible service the counterpart is a
conditional write — `If-Match` on the current ETag, or `If-None-Match:
*` for the first write. That is a compare-and-swap, which is what the
local rename gives us, so the primitive survives the move rather than
being weakened.

A service with no conditional write cannot host an activated collection
safely. It can still host an immutable generation that readers name
directly (`--generation NAME` already exists for this), which is enough
for a published dataset that never changes.

The same reasoning applies to the delta log, whose local primitive
`appendSyncAtSize` is already a compare-and-swap on the file size. That
is the shape a conditional PUT gives, so a durable-update store over
HTTP is possible; it is not attempted here.
See https://github.com/danbri/factoidal/issues/644 for the single-writer
gap that exists even locally.

## What is still in the way for a PAGE

Incremental import does not by itself let a browser pack. The recursion
that overflows the stack happens INSIDE the wasm module during
`packFeed`, so it is unaffected by where the artifacts go afterwards.

Measured 2026-09-04 (https://github.com/danbri/factoidal/issues/649): on
the default stack of Node and of Deno, a pack fails above roughly
500,000 bytes of input with `Maximum call stack size exceeded`.
`node --stack-size=8000` packs an 888,949-triple file correctly in
51.76 s, byte-identical to the native packer.

A host flag rescues Node and Deno. A browser tab has a fixed frame
budget and no such flag, so an in-page packer needs the recursion depth
reduced in the Lean source. Do not promise in-page import before that is
measured.

The suspected cause, stated as a hypothesis and not yet confirmed:
`L4Factoidal/Storage/TermLocalIndex.lean:130`'s `entriesGo` builds a
cons after its recursive call, so its depth is one frame per dictionary
term in a publication batch. That is the same function that dominates
the pack profile in https://github.com/danbri/factoidal/issues/647. If
the hypothesis holds, the two issues are one defect and its repair helps
the browser, where no flag exists.

## Work, in order

1. Confirm or refute the `entriesGo` hypothesis
   (https://github.com/danbri/factoidal/issues/649).
2. An HTTP realisation of `store-host`: `readRange` as a ranged GET,
   `writeNew` as a PUT, `atomicReplace` as a conditional PUT. It goes
   beside `node.mjs` and `deno.mjs` and shares `index.mjs`, so nothing
   above it changes.
3. A read-only demonstration first: point the existing `query` command
   at a bucket URL and answer from it, with digest verification on. That
   needs no write path and no conditional write, and it is the half with
   the most value.
4. Only then the import path.

## What this document does NOT claim

No HTTP host exists yet. Every number above is measured on the local
filesystem host. The ranged-read ratio is a property of the planner and
the manifest, and it is the reason to expect this to work; it is not a
measurement of it working over a network.
