# The store handle's cap is retained bytes, and where 128 MiB comes from

Issue: <https://github.com/danbri/factoidal/issues/657>.
Caps as first recorded: <https://github.com/danbri/factoidal/issues/648>.
Code: [`formal/lean4/Wasm/Ops/StoreHandles.lean`](../../formal/lean4/Wasm/Ops/StoreHandles.lean)
carries the same derivation in its banner, next to the constant.

## The blocker

`storeOpen` applied `storeQuery`'s three caps: 64 artifacts, 8,388,608 bytes,
100,000 rows. On the full skosdex corpus (7,315,251 quads, 3,286 blocks, 204
named graphs, 1.0 GB, SBM8 with an LGI1 index per block) the predicate
`skos:prefLabel` occupies 257 blocks — one per graph, because the split cuts
at graph boundaries — so a corpus-wide handle could not open:

    storeOpen: the call supplies 257 artifacts, the cap is 64

A vocabulary-scoped query worked and was fast. A corpus-wide one could not
start.

## Why the number was wrong

The three caps were derived for the STATELESS path. `storeQuery` re-reads,
re-hashes and re-decodes its blocks on every call, so a wide plan means a
large cost paid AGAIN for every question, and a tight artifact count was a
reasonable bound on one call. A handle removes the repetition: the blocks are
verified and decoded ONCE at open and then answer many queries. What is left
to bound is residency.

An artifact COUNT is the wrong shape for residency. 257 small blocks may
retain far less memory than four large ones. `maxStoreHandleBytes` — retained
bytes, process-wide — already existed; the count was carried over and never
re-derived.

## What changed

* `storeOpen` no longer calls `checkEntryCaps`. Its only byte bound is
  `maxStoreHandleBytes`, and its only other bound is `maxStoreHandles` (8),
  which bounds the fixed per-handle cost the byte count does not see.
* `maxStoreRows` is dropped for the handle path: a row cannot be smaller than
  a few packed bytes, so the byte cap bounds rows too, and `storeHandleList`
  reports the retained row count.
* The byte check moved BEFORE `readRetained`. It was applied after the whole
  set had been hashed and decoded, which paid the memory before refusing it.
  It is now decided from the manifest's own declarations, so a refusal costs
  the manifest decode and nothing more.
* `storeQuery`'s caps do not move. See below.

## Where 128 MiB comes from

`maxStoreHandleBytes` counts ADMITTED ARTIFACT BYTES — what the manifest
declares and what the host transferred. It is a PROXY for resident memory,
and the multiplier between them is measured.

Measured 2026-09-05 on `factoidal-skosfull`, one handle over the corpus-wide
`skos:prefLabel` plan, through `l4block-literal-gate --probe` under
`/usr/bin/time -l` (Darwin 24.6.0, 16 GiB):

| | retained artifact bytes | peak resident | resident per retained byte |
|---|---|---|---|
| one handle, 257 IBK4 blocks + 257 LGI1 | 103,341,302 | 1,675,345,920 | 16.2 |
| the same, second run | 103,341,302 | 1,369,391,104 | 13.3 |
| two handles (the row-identity gate) | 206,682,604 | 2,569,797,632 | 12.4 |

Three readings on one shared machine spread from 12.4 to 16.2. The cap is
derived from the largest.

wasm32 gives 4,294,967,296 bytes of address space in total, and a browser tab
in practice holds less. Half is reserved for the host's own allocations, for
the incoming region before the engine consumes it, and for growth:

    2,147,483,648 / 16.2  =  132,464,438 bytes

The cap is the nearest power of two, **134,217,728 (128 MiB)** — 1.3 percent
above the computed bound, predicting 2,175,907,586 bytes resident, 50.7
percent of the address space. It admits the corpus-wide `skos:prefLabel` set
with 30,876,426 bytes of headroom, and refuses a SECOND handle over the same
set.

A single small block measures a much larger multiple — about 32 for a 5.5 MB
block — because it carries the fixed cost of the process. The marginal figure
is the one a cap is derived from. The multiplier stays data-dependent: many
short literals over a large dictionary cost more per packed byte than few
long ones. A host that must bound its OWN memory reads `storeHandleList` and
measures its own process; this cap bounds the engine, not the host.

## Why `storeQuery`'s caps did not change

They answer a different question. `storeQuery` pays the hash and the decode
on every call, so its caps bound ONE CALL's latency, and 8 MiB is set by the
throughput of the pure Lean SHA-256, not by memory. Raising them would make a
single stateless call slower without making any second call faster. A host
with a wide query opens a handle.

## Measured after the change

A corpus-wide handle opens at the shipped cap. `l4block-literal-gate --probe
/Users/danbri/working/factoidal-skosfull skos:prefLabel …`:

    blocks 257, sidecars 257, region 159,673,831 bytes
    storeOpen                  57,067 ms   103,341,302 retained, 741,179 rows
    search "water"                1,148 ms   2,138 rows
    search "bicycle"                941 ms      42 rows
    search "zzqqxnosuchneedle"      916 ms       0 rows

A miss costs what a hit costs, which is the LGI1 candidate filter deciding
from the index rather than from the rows. The single-graph figures issue 657
recorded were 4,988 ms to open and 545 to 592 ms a search; the corpus-wide
open is 11 times the one-graph open for 257 times the blocks, and a search is
under twice the time. The first run of the same probe, on a less loaded
machine, measured 51,835 ms to open and 490 to 587 ms a search.

## Gates

* Old behaviour unchanged, compared as ROWS (anti-pattern 34): the whole
  answer envelope of six queries against `factoidal-skosgraphs` and
  `factoidal-skoscross`, through `storeOpen` + `storeHandleQuery`, byte for
  byte between the pre-change binary and this one — 12 pass, 0 fail (out of
  12). The same script shows the change itself: a handle over the whole
  `factoidal-skosgraphs` generation (119 blocks, 28,394,316 bytes) is refused
  by the old binary ("the call supplies 119 artifacts, the cap is 64") and
  admitted by the new one.
* The refusal is tested at the constant: `#guard`s in
  `Wasm/Ops/StoreHandles.lean` check that exactly the cap is admitted, that
  one byte more is refused with BOTH the value and the cap named, that the
  bound is over every open handle rather than one, that 512 artifacts are
  admitted where the inherited count refused them, and that a second handle
  over the corpus-wide set is refused.
* SPARQL 1.1 `manifest-all.ttl`: 631 pass, 0 fail (out of 631).
* `Wasm/native-smoke.sh`: 85 pass, 0 fail (out of 85).

## `l4block-literal-gate --probe`

The measurement is reproducible. `--probe` opens ONE handle over the whole
plan with its sidecars and reports the open cost, the retained bytes and the
per-needle search cost, so `/usr/bin/time -l` around it reports the resident
cost of one retained artifact set. It compares nothing and gates nothing; the
gate is the no-flag form, which is unchanged.
