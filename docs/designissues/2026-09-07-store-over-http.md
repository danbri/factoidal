# Querying a Shardborough generation over HTTP, from a browser

Owner, 2026-09-07:

> "can you make some investigations of accessing the data over R2 as you
> outlined above. Can it be in a hub notebook?"

Yes to both, with one measured qualification that is the whole finding of
this note. The transport works: a public Cloudflare R2 bucket is a
queryable RDF store, a browser reaches it, and every artifact is verified
against the manifest before it is used. What does not work today is the
SIZE of the skosall generation's manifest, and the cost is in the engine,
not in the network.

Tracking:
<https://github.com/danbri/factoidal/issues/669> step 5 and
<https://github.com/danbri/factoidal/issues/670>.
This note supersedes the read half of
[the 2026-09-04 note](2026-09-04-store-over-http.md), which designed this
path before any of it existed. Its write half — `writeNew` as a PUT,
`atomicReplace` as a conditional PUT — is untouched and still not built.

## What landed

- `npm/factoidal/store-http/index.mjs` — the HTTP counterpart of
  `npm/factoidal/store-host`. `fetch` is its only I/O primitive, so one
  file serves the browser, Node and Deno.
- `tests/store-http/mock-bucket.mjs` — a read-only static server with a
  bucket's key layout, a permissive cross-origin policy and byte ranges,
  so no test depends on Cloudflare.
- `tests/store-http/over-http.mjs` — 30 pass, 0 fail (out of 30).
- `docs/web/hub/54-skosdex-over-r2.md` and `tests/hub/post54_test.mjs` —
  the notebook, and the test that pins its nine query shapes against
  measured request counts and byte counts.
- `tools/host-purity-lint.sh` grew a second group and now reads 6 pass, 0
  fail (out of 6).

## The request sequence for one query

```text
GET  <base>/CURRENT                     the activated generation's name
GET  <base>/<gen>/manifest.sbm2         every artifact, its length, its SHA-256

  storeManifestInspect(manifestHex)     the ENGINE decodes it; the host never parses it
  storeQueryPlan(manifestHex, sparql)   -> {mode, shards, keys[], sidecarKeys[],
                                            blobKeys[], bytes, rows, zoneExcluded}

GET  <base>/<gen>/<key>   per key       bounded parallel (4 in flight by default)
  SHA-256(bytes) == the manifest's digest for that key
                                        a mismatch is refused BY NAME, bytes discarded

  storeQuery(manifestHex, sparql, [{key, offset, len}, …], one byte region)
                                        -> SPARQL Results JSON
```

The host makes no format decision anywhere in that sequence. It reads
`CURRENT`, it opens whichever of two manifest names exists, and it fetches
the keys the engine named. `tools/host-purity-lint.sh`'s second group
fails the build if a store host acquires an artifact suffix, a block-kind
name, a byte offset, a magic number or a typed-array field read. The lint
was checked against a deliberate violation before it was trusted
(anti-pattern 28): a line carrying `DataView`, `getUint32`, `0x49424b35`
and `predicate-0.ibk5` was inserted into the HTTP host and the lint
reported it and exited 1.

### Whole objects, not ranges — today

`readRange` in the filesystem host is already an HTTP `Range` request
written in POSIX terms, and the HTTP host implements it. The query path
does not use it, because the plan names WHOLE artifacts: a block is
decoded as a unit. The range path is exercised by the tests (a window is
served exactly, and a server that ignores the request is reported as
`RANGE_IGNORED` rather than misread) so it is ready when the engine starts
naming byte windows. Any claim that this design "reads only the bytes it
needs" is about which OBJECTS it fetches, not which bytes within one.

## What the module holds in memory

Per open store:

- the manifest bytes, and their hexadecimal form. The ABI takes the
  manifest as a hex string, so this is 3× the manifest's size, held for
  the life of the store rather than rebuilt per query;
- the engine's decoded view of the manifest (`storeManifestInspect`'s
  envelope), from which the host reads exactly two fields per artifact:
  its key, and the digest the manifest commits for it;
- the request log.

Per query: one contiguous region the size of the artifacts the plan named,
built and dropped inside `query()`. Nothing is retained between queries by
default — `cacheArtifacts` is opt-in — and the linear memory of the wasm
module does not grow with the number of questions. That is a gate, not a
hope: `tests/store-http/over-http.mjs` reads `HEAPU8.length` before and
after twenty-five further queries and fails if it moved. (The leak repair
that made this true landed the same day; without it this check is the one
that would have caught the regression.)

## Integrity

The manifest commits a SHA-256 per artifact. The host computes SHA-256 of
every object it fetched with `crypto.subtle` and compares it against that
commitment before the bytes reach the module. A mismatch throws
`DIGEST_MISMATCH` naming the key and carrying both digests, and the bytes
are discarded: they never enter the wasm heap and are never cached.

The check is an early refusal, not the authority. `storeQuery` verifies
every artifact it opens against the same commitment regardless, and says
so in the engine's own words (`artifact '<key>' does not match the
SHA-256 …`). Passing `{verify: false}` therefore changes WHEN a
substituted object is caught, not WHETHER. Both refusals are tested, on
the same damaged store.

What is not covered: the manifest itself. A reader who fetches
`manifest.sbm2` over a transport nobody controls has no independent
commitment to check it against — the digests inside it are only as
trustworthy as it is. The generation identity `storeOpen` reports is the
hook a future signed-pointer scheme would hang on; nothing signs `CURRENT`
today.

## Public access and CORS on R2

Verified against the live bucket on 2026-09-07. Base URL:

```
https://pub-ce682919a85f481f9864add9d9a66737.r2.dev/skosall/
```

The checks a reader can run:

```bash
BASE=https://pub-ce682919a85f481f9864add9d9a66737.r2.dev/skosall

# public read, and the activated generation
curl -sI "$BASE/CURRENT"
curl -s  "$BASE/CURRENT"

# byte ranges
curl -sI -H 'Range: bytes=0-1023' "$BASE/gen-1/predicate-0.ibk5"

# the browser preflight, from the page's real origin
curl -s -o /dev/null -D - -X OPTIONS \
  -H 'Origin: https://danbri.github.io' \
  -H 'Access-Control-Request-Method: GET' \
  -H 'Access-Control-Request-Headers: range' \
  "$BASE/gen-1/manifest.sbm2"

# and the exposure a ranged read needs on the GET itself
curl -s -o /dev/null -D - -H 'Origin: https://danbri.github.io' \
  -H 'Range: bytes=0-15' "$BASE/gen-1/manifest.sbm2"
```

What the bucket must answer, and does:

| requirement | why the page needs it |
|---|---|
| public read on `<prefix>/CURRENT` and `<prefix>/<gen>/*` | there is no server process to proxy through |
| `Access-Control-Allow-Origin: https://danbri.github.io` | the hub is served from GitHub Pages |
| `Access-Control-Allow-Methods: GET, HEAD` | reads only; the write path is not built |
| `Access-Control-Allow-Headers: range` | without it the preflight for a ranged GET fails |
| `Access-Control-Expose-Headers: Content-Length, Content-Range, ETag, Accept-Ranges` | a cross-origin reader cannot see an unexposed response header |
| `Access-Control-Max-Age: 86400` | one preflight per object per day, not per request |
| `Accept-Ranges: bytes` | the range path, when the engine starts naming windows |

**The allowance is origin-specific, and that has a consequence.** Measured
by hand:

```text
Origin: https://danbri.github.io   -> 206, Access-Control-Allow-Origin: https://danbri.github.io
                                          Access-Control-Expose-Headers: Content-Length,Content-Range,ETag,Accept-Ranges
Origin: http://127.0.0.1:8941      -> 206, and NO Access-Control-* header at all
```

The bytes come back either way; the browser is what refuses them. So the
deployed hub page can read the bucket and a LOCAL PREVIEW of the same page
cannot — confirmed in a real browser, where the live twin served from
`127.0.0.1` gets `blocked by CORS policy: No 'Access-Control-Allow-Origin'
header is present`. Add the preview origin to the bucket's rule, or accept
that the R2 preset is a deployed-page-only path. This is why the
notebook's default target is a store served from the site itself.

Two more operational points the measurements turned up.

**`r2.dev` is rate-limited by Cloudflare.** It is a development URL, not a
production one. The notebook keeps at most four requests in flight for
that reason; a real deployment puts a custom domain in front of the
bucket, which also lets the response headers be set per route.

**R2 sends no `Cache-Control`.** Measured: fetching the 25.5 MB manifest a
second time cost 4.9 s, no less than the first. Every object under a
generation directory is immutable — a generation never changes after it is
published — so each should carry
`Cache-Control: public, max-age=31536000, immutable`, and `CURRENT`, the
one mutable name in the design, should carry `no-cache`. That is a bucket
or custom-domain setting, not a code change. The mock bucket already sets
both, so the notebook's behaviour against a correctly configured bucket is
what the tests exercise. Beyond the HTTP cache, the browser Cache API is
where a page would keep a decoded generation across reloads; nothing does
that yet.

## Measured: the bundled sample store

Nine SKOS query shapes, taken from the skosdex web application's SPARQL
cookbook and rewritten for one default graph. The store is five IPTC
NewsCodes vocabularies: 4,434 triples, thirteen predicate-local blocks,
455,818 bytes, a 6,044-byte manifest. Served by the mock bucket.

| question | plan mode | objects | bytes | rows |
|---|---|---|---|---|
| Concept census | `ibk3-paged-merkle(1)` | 1 | 48,565 | 1 |
| The indexer shape | `ibk3-paged-merkle(3)` | 3 | 291,306 | 20 |
| Scheme inventory | `ibk3-paged-merkle(1)` | 1 | 48,380 | 5 |
| One concept, every language | `ibk3-paged-merkle(1)` | 1 | 143,503 | 2 |
| Same label, which concept | `ibk3-paged-merkle(1)` | 1 | 143,503 | 1 |
| Language coverage | `ibk3-paged-merkle(1)` | 1 | 143,503 | 2 |
| Predicate census | `ibk3-paged-merkle-full-manifest(13)` | 13 | 455,818 | 13 |
| Top concepts of every scheme | `ibk3-paged-merkle(2)` | 2 | 191,888 | 20 |
| Definitions that mention video | `ibk3-paged-merkle(1)` | 1 | 99,238 | 20 |

Opening costs two requests. Eight of the nine questions read one, two or
three of the thirteen objects; the ninth has an unbound predicate, which
any block can answer, so the plan selects the whole manifest and names the
mode `…-full-manifest(13)` rather than guessing.

Those numbers are not prose. `tests/hub/post54_test.mjs` parses the table
out of the notebook's own markdown and fails if a measured request count
or byte count disagrees with it.

**Confirmed in a real browser**, not only under Node. The built page was
served under its real `/factoidal/` path prefix and driven headless: the
cell mounts with no `.observable-cell-error`, no console error and no
horizontal overflow at a 390-CSS-pixel viewport, and "Run all nine"
produced the same nine plan modes, object counts, byte counts and row
counts as the table above, in 77 ms to 1,073 ms per question. Every
artifact was digest-checked in the tab with `crypto.subtle` before it
reached the module.

## Measured: the skosall generation in R2

662 named graphs, 219,530,671 quads, 18,642,130,989 bytes of blocks in
36,106 artifacts, wire version 10, layout
`quad-ibk5-ptd2-lgi2-gbi1-merkle-v0`. Manifest 25,533,404 bytes.

| step | measured, 2026-09-07, one laptop |
|---|---|
| `GET CURRENT` | 316 ms, 5 bytes |
| `GET manifest.sbm2` | 4,325 ms, 25,533,404 bytes (5.9 MB/s) |
| the same manifest again | 4,856 ms — no `Cache-Control`, nothing reused |
| `hexOfBytes(manifest)` | 4,552 ms, 51,066,808 characters |
| **`storeManifestInspect`** | **537,868 ms** |

The network is 0.8 percent of that. Decoding a 25.5 MB manifest of 36,106
entries takes nine minutes inside the engine, and it is paid per
operation, so one question costs a multiple of it.

`storeQueryPlan` is worse than `storeManifestInspect`, not equal to it. A
single bound-predicate, bound-graph query
(`SELECT ?c ?l WHERE { GRAPH <http://aims.fao.org/aos/agrovoc> { ?c
skos:prefLabel ?l } } LIMIT 20`) was left in `storeQueryPlan` on the same
manifest for **55 minutes without returning** and was then stopped. The
plan does more per entry than the inspect does — it reads the query's
patterns against 36,106 entries' predicate declarations and subject and
object zone maps — and nothing about that work is amortised. A query
against this generation was therefore never observed to complete at all,
by any route.

Before that, it does not fit in the default call stack. `openStoreOverHttp`
against this generation on plain `node` fails with `Maximum call stack size
exceeded` from inside `storeManifestInspect`. The measurement above was
taken on a worker thread with a 64 MB stack, the route
`npm/factoidal/bin/store-worker-host.mjs` already takes for the same reason
on the query path (<https://github.com/danbri/factoidal/issues/653>).
`node --stack-size=60000` on the MAIN thread does not work on macOS: the
main thread's stack is fixed by the operating system at 8 MB, so the flag
produces a segmentation fault rather than a bigger stack.

A browser tab has neither control. The R2 preset in the notebook is real
and correct and will hang a tab, and the notebook says so where a reader
meets it.

## What has to change, in order

The blockers are all engine-side. None of them is in the host, the
transport or the bucket.

1. **Carry the manifest as bytes, not as hexadecimal.** The blob ABI
   already exists and `storeQuery` uses it for artifacts. The manifest
   argument of all three operations is still a hex string, which doubles
   25.5 MB into a 51 MB JavaScript string and copies it into the wasm heap
   per call. Cost measured above: 4.6 s per call, before any decode.
2. **Decode the manifest once and retain it.** `storeOpen` already keeps
   decoded state behind a handle, but it opens ARTIFACTS eagerly, which a
   19 GB generation cannot do. A manifest-only handle — open, then
   `storeHandleQuery` against it — turns a 9-minute cost paid three times
   per question into one paid once per session.
3. **Make the decode cheaper and non-recursive**, so a fixed frame budget
   is enough. Same defect family as issue 653.
4. **Split the manifest.** A reader who wants one vocabulary should fetch
   one vocabulary's declarations. §4 of
   [the hierarchical named graphs note](2026-09-07-hierarchical-named-graphs.md)
   is where that argument belongs; this note is the measurement that makes
   it urgent.

Items 1 and 2 are the ones that make the browser path usable at this
scale; 3 is what makes it usable without a worker; 4 is what makes it
fast.

## What this note does NOT claim

- No write path. Publishing a generation over HTTP, and the conditional
  write that activation needs, are designed in the 2026-09-04 note and
  not built.
- No signature over `CURRENT` or over the manifest. Artifact integrity is
  covered; manifest authenticity is not.
- The R2 figures are one laptop, one run, one network. The engine-side
  figure (537.9 s) is the one that matters and it is not a network
  measurement.
- Nothing here was run in a real browser against R2. The browser path is
  exercised against the same-origin sample store; the R2 numbers above are
  from Node using the identical module.
