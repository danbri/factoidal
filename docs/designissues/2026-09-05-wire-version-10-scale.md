# Wire version 10: the format that scales past the source

2026-09-05. Owner, 2026-09-05, verbatim: "we are developing the wire and
file formats specifically to scale. It would be madness to freeze a
database with zero users at a format that doesn't scale and nobody uses.
Just consider what other changes to make at same time, if any"; "Rdf 1.2
not star"; "can we deal with a multi megabyte literal? Giga? Terra? What
assumptions are we forgetting to articulate?"

This record decides one wire version that answers all three. Tracking
issue: <https://github.com/danbri/factoidal/issues/658>. It follows
[`2026-09-05-shard-pack-profile-and-memory.md`](2026-09-05-shard-pack-profile-and-memory.md)
(the memory measurement that forced it) and
[`2026-09-04-blocks-per-predicate.md`](2026-09-04-blocks-per-predicate.md)
(the block-set decision it builds on).

## 1. The target

YAGO 4.5: 132 million facts, 49 million entities, 142 GB of Turtle, in
five files. At the measured slope of 3.76 bytes of peak memory per source
byte the current packer needs 534 GB. The machine has 16 GB.

The format must satisfy four requirements that the current one does not:

1. **Peak packer memory is bounded by a constant the operator chooses**,
   not by the source.
2. **A bound-subject lookup on a large predicate reads a bounded number of
   blocks**, not every block of that predicate.
3. **RDF 1.2 terms round-trip**: triple terms and directional language
   literals are stored, not refused.
4. **Every size ceiling is a stated number with a stated behaviour above
   it**, and a large literal does not make a block unqueryable or an index
   useless.

## 2. The ceilings, stated

These are the assumptions the current format leaves unarticulated, each
now a named constant with a defined behaviour.

| Quantity | Ceiling | Where | Above it |
|---|---|---|---|
| inline lexical form of a literal | `maxInlineLexicalBytes` = 65,536 bytes | term codec v2 | stored out-of-line (section 4.3), never inline |
| out-of-line literal | `maxBlobBytes` = 2^32 − 1 bytes | manifest blob table | the packer refuses, naming the literal's subject and predicate |
| any length-prefixed string on the wire (IRI, blank-node label, language tag, datatype IRI) | 2^32 − 1 bytes | term codec | refused by the encoder (`serializeLString?` admission), never truncated |
| rows in one block | `maxBlockRows` = 16,384 | packer cut policy | a new block |
| estimated block bytes | `maxBlockWireBytes` = 2,097,152 | packer cut policy | a new block; one quad above the target still forms a block of its own |
| terms in one block dictionary | 2^32 − 1 (local ID width) | IBK5 | unreachable under the row and byte targets |
| one artifact's bytes | 2^32 − 1 | SHA-256 binding (`Crypto.SHA2Native`: HACL* takes a `uint32_t` length and returns an EMPTY digest above it) | refused by the packer; activation refuses an empty digest |
| entries in one manifest | 2^32 − 1 | SBM | unreachable at the sizes above (YAGO is about 60,000 entries) |
| one source statement (Turtle) | the packer's memory | `PackStream.lean` line 257 | still an intentional bounded-input exception: a Turtle statement is retained until it completes |
| the wasm address space | 4 GiB | wasm32 | the same caps as the native tools, plus the stated `maxPack*` and `maxStoreHandle*` caps |

Four independent u32 ceilings met at 4 GB by coincidence; now they are one
row each in this table, and the format's constants name them.

Terabyte literals are refused by design at `maxBlobBytes`. Multi-megabyte
literals are the case the format now handles: out-of-line, chunk-verified,
range-readable, not indexed by grams, and not counted against the block's
byte target.

## 3. What changes and what does not

| Layer | Now | Version 10 | Reason |
|---|---|---|---|
| term codec | v1 (`DeltaLog.serializeTerm`): refuses triple terms and directions | **v2** (`Storage/TermWireV2.lean`): triple terms recursive, direction flag, out-of-line literal tag | requirements 3 and 4 |
| dictionary | PTD1 over v1 terms | **PTD2**: the PTD1 page layout over v2 terms | the codec is what changes |
| block | IBK4 | **IBK5**: the IBK4 layout with a PTD2 dictionary | a byte change is a new version |
| literal index | LGI1, fixed u32 gaps, 55% of the block bytes on `skos:prefLabel` | **LGI2**: LEB128 gaps (measured design target: about 22%), plus the list of opaque (out-of-line) literal IDs the candidate set always includes | index size; superset theorem must survive blobs |
| geometry index | GBI1 | GBI1, unchanged | see section 7 |
| manifest | SBM9 | **SBM10**: per-entry subject and object ZONE MAPS, a manifest-level BLOB TABLE, per-entry blob references | requirements 2 and 4 |
| layout label | `quad-ibk4-ptd1-lgi1-gbi1-merkle-v0` | `quad-ibk5-ptd2-lgi2-gbi1-merkle-v0` | |
| packer publication point | end of source | **every batch** (section 5) | requirement 1; NOT a wire change |
| DLOG delta log | v1 terms | unchanged | the delta log is IBK3-only today; it moves to v2 when it moves to quads |
| IBK3 / SBM6 | readable | readable, unchanged | lineage and differential oracle |

Every earlier version stays readable exactly as before. `l4block-shard-pack`
takes the layout tag `ibk5` to write version 10 and keeps the tag `ibk4`
writing version 9, which is what makes the two comparable on one corpus with
one binary: version 9 is the differential oracle of gate 4 below. The alpha
allows repacking, so nothing depends on version 9 staying writable beyond
that use.

## 4. Term codec v2

Module `L4Factoidal/Storage/TermWireV2.lean`. Every integer little-endian.
`lstring` is the v1 length-prefixed UTF-8 string: u32 byte length, bytes.

| Tag | Term | Body |
|---|---|---|
| 0 | IRI | `lstring` |
| 1 | blank node | `lstring` label |
| 2 | literal, inline | `lstring` lexical form; `lstring` datatype IRI; u8 flag; if flag ≥ 1, `lstring` language tag |
| 3 | triple term | subject: u8 (0 IRI, 1 blank node) + `lstring`; predicate `lstring`; object: one v2 term, recursively |
| 4 | literal, out-of-line | `lstring` datatype IRI; u8 flag; if flag ≥ 1, `lstring` language tag; u64 byte length of the UTF-8 lexical form; 32 bytes SHA-256 of that lexical form |

Flag: 0 no language tag; 1 language tag, no direction (`rdf:langString`);
2 language tag, direction `ltr`; 3 language tag, direction `rtl` (both
`rdf:dirLangString`). The decoder builds the literal through the
well-formedness test `RDF.literalWf`, so a flag that disagrees with the
datatype is refused, as in v1.

### 4.1 Canonical choice between tags 2 and 4

A literal whose lexical form is at most `maxInlineLexicalBytes` UTF-8 bytes
is written with tag 2 and MUST NOT be written with tag 4; a longer one is
written with tag 4 and MUST NOT be written with tag 2. The decoder refuses
the other choice. One term, one encoding: TLI-style key comparison and
dictionary de-duplication depend on it.

### 4.2 The decoded type

The decoder cannot produce an RDF `Term` for tag 4 without the blob's bytes,
and the storage layer does not change `RDF.Term` (its constructors are the
RDF 1.2 abstract syntax). So the decoded type is

```lean
structure BlobLiteral where
  datatype  : WfIri
  langTag   : Option String
  direction : Option TextDirection
  byteLength : Nat          -- < 2^64 on the wire; ≤ maxBlobBytes by admission
  sha256    : ByteArray     -- 32 bytes

inductive WireTerm where
  | inline (t : Term)
  | blob (b : BlobLiteral)
```

with `resolve (lookup : ByteArray → Option String) : WireTerm → Option Term`
that builds `Term.literal` from the blob's lexical form, and refuses when
the bytes are absent, have the wrong length, or hash differently. Theorems:

* `parseTerm_serializeTerm : serializeTerm? w = some bs → parseTerm (bs ++ rest) = some (w, rest)`;
* `resolve_toWire : resolve (lookupOf t) (toWire t) = some t` for the packer's
  `toWire`, which chooses the tag by section 4.1 and whose `lookupOf`
  returns the literal's own lexical form.

### 4.3 Out-of-line literals

The lexical form of a tag-4 literal is one artifact, `blob-<sha256 hex>.lit`,
holding exactly the UTF-8 bytes, committed in the manifest blob table
(section 6.2) with byte extent, SHA-256 and the fixed-chunk Merkle
commitment every artifact carries. Content addressing de-duplicates a
literal that several blocks or graphs share, and the term's own digest is
the artifact identity, so a reader that has the term can name the file.

## 5. Publication every batch

The packer publishes blocks DURING the ingest pass instead of at its end.
No byte of any artifact depends on this: the block set changes, which every
manifest since SBM2 admits ("a reader MUST take the union of the entries
for a predicate", specification section 6.1.1). It is recorded here because
it is what closes requirement 1 and it decides the block set the format's
readers will see.

Policy, deterministic in the input and the two operator numbers:

1. Quads accumulate into buckets as they parse
   (`PredicateQuadBlocks.Buckets`). Since 2026-09-05 a bucket is keyed by
   the PAIR (predicate, graph), not by the predicate alone.
2. A bucket is cut into blocks by the two size targets: 16,384 rows,
   2,097,152 estimated bytes. A block whose rows are complete under those
   targets is published at once and its rows released. There is no graph
   rule: a bucket's rows are all one graph by construction
   (`PredicateQuadBlocksTheorems.bucket_one_graph`).
3. When `batchSourceBytes` (default 268,435,456, `--batch-bytes`) of source
   have been fed since the last batch end, every bucket holding at least
   `minBatchRows` (4,096) rows is published; smaller buckets carry over.
4. Carried rows are bounded: when their total passes `maxCarriedRows`
   (1,048,576) every bucket is published regardless of size.
5. At end of source every bucket is published.

Rule 3 keeps rare buckets from producing one tiny block per batch: with
YAGO's few hundred predicates and 550 batches that would be tens of
thousands of near-empty entries. Rule 4 bounds what rule 3 retains, for a
source with hundreds of thousands of buckets.

Peak memory is then about one batch of source plus carried rows plus the
blocks being encoded, which the ladder of section 9 measures. The wasm
`maxPackSourceBytes` cap (128 MiB, buffered-source only) goes away for the
streamed grammars; the wasm host already drains `packNext` after every feed.

What is proved: the DATASET denoted by the union of the published blocks
equals the dataset the buffered route denotes for the same source
(`PackStreamTheorems`, stated over `RDF.Dataset` as set equality per
graph). Byte identity between the two routes holds only for a source
smaller than one batch; above it the block SET differs and rows are
compared, as gate 2 of the blocks-per-predicate record did.

Interleaved graphs in N-Quads (g1, g2, g1, ...) do NOT produce more blocks.
Until 2026-09-05 they did, and badly: the bucket key was the predicate alone
and rule 2 cut a run at every graph change, so an interleaved source gave one
block per graph RUN. The subsection "The shuffled source" below has the
measurement and the repair. With the (predicate, graph) key, interleaving
never closes a run. Each block still holds one graph, so the manifest
`graphSet` has one member and `GRAPH <iri>` selection stays exact; there may
be several blocks per key when a bucket passes a size target.

Order. The buffered route (`blocksOfDataset`, still used by the TriG path and
by the theorems) publishes in the FIRST-OCCURRENCE ORDER OF THE KEY in the
graph-major `quadsOfDataset` flattening. The streamed route publishes a run
when rule 2 closes it, and at a flush in the same first-occurrence key order.
For a source below one batch the two routes write the same blocks with the
same rows; the block ORDER, and with it the ordinals and the artifact names,
differs.

## 6. SBM10

Everything SBM9 carries, plus:

### 6.1 Per-entry zone maps

After the GBI1 sidecar reference and before the quad tail:

| Width | Field |
|---|---|
| 4 + n | `subjectMin`: the first `zoneBytes` (64) bytes of the smallest subject key in the block |
| 4 + n | `subjectMax`: the first 64 bytes of the largest subject key |
| 4 + n | `objectMin` |
| 4 + n | `objectMax` |

A key is the v2 encoding of the term (section 4). Order is lexicographic
on bytes — the TLI1 canonical key order, restated over v2 bytes. Bounds are
64-byte PREFIXES, so a 64 KiB literal does not put 64 KiB into every entry
that holds it; truncation is sound because the lexicographic order is
preserved by taking prefixes of equal length: `a ≤ b → a.take n ≤ b.take n`.

Planner use: a pattern with a constant subject `s` excludes every entry
with `key(s).take 64 < subjectMin` or `> subjectMax`; likewise a constant
object. Theorem `zoneMap_sound`: a row whose subject is in the block has a
key inside the entry's bounds. Selectivity depends on the source order — a
subject-grouped Turtle file, which is what serialisers emit, gives
disjoint ranges per block; a shuffled source gives overlapping ranges and
a scan, which is correct and no worse than today. It is measured in
section 9, not assumed.

### 6.2 The blob table and per-entry blob references

Manifest-level, after the entry list: u32 count, then one artifact
reference per blob (`ArtifactRef`: key, bytes, SHA-256, chunk commitment),
ascending by SHA-256, no repeats. Per entry, before the zone maps: u32
count, then u32 indices into the blob table, ascending, no repeats — the
blobs this block's dictionary refers to.

Activation checks, for every entry: every tag-4 term in the decoded
dictionary names a digest that is the SHA-256 of an artifact in the blob
table; that artifact's bytes hash to its stated SHA-256, which equals the
hex in its key; its byte extent equals the term's `byteLength`; and the
entry's index list is exactly the set of blobs its dictionary names.

Planner use: `storeQueryPlan` lists, after the selected block keys, the
blob keys those entries reference, so a host fetches everything a query
can touch without decoding a block. The stateless `storeQuery` caps count
blob bytes.

### 6.3 Admission

Encoder admission equals decoder admission, as for every version. SBM10
adds: zone-map fields are at most 64 bytes and `min ≤ max`; blob indices
are in range, ascending, distinct; blob table keys are `blob-<64 hex>.lit`
with the hex equal to the SHA-256; the blob table is ascending and
distinct by SHA-256. Versions 0 through 9 MUST NOT carry any of these
fields (the same rule SBM7 states for its fields).

## 7. Considered and deferred

* **GBI1 hull box per entry.** A box per block would let the planner skip
  a block from the manifest alone. A block's geometries may carry several
  CRSs and a hull is per CRS, so the field is a list, not a box, and the
  monotonicity lemma is per CRS. Deferred; not a wire-blocking decision,
  because a manifest field can be added in the next version.
* **A graph-name index.** With one graph per block the manifest already
  names every block's graph; `GRAPH ?g { ?s :p ?o }` must open every block
  of `:p` whatever the index says. Nothing to add.
* **Payload compression.** A measured decision: the literal-heavy blocks
  of skosdex are the case for it, the dictionary is already de-duplicated,
  and a compressed page is not range-readable. Measure zstd and LZ4 on
  the corpus ladder before deciding; a flag added later is a version bump
  later, which the alpha allows.
* **Optional Merkle sidecars.** Issue 646 measured 20% of activation
  wasted. Independent of this version.
* **A Bloom filter per block over subjects.** Sort-independent, unlike a
  zone map. About 1 byte per row, so it is a sidecar, not a manifest
  field; the planner would then read one sidecar per candidate block.
  Deferred until the zone map is measured on a shuffled source.
* **Sorting the source.** External sort is what makes zone maps selective
  on any source. Out of scope for the packer; a `sort -k1` on N-Quads is
  the operator's tool today.

## 8. Implementation map

| Piece | Module | Theorem |
|---|---|---|
| term codec v2 | `Storage/TermWireV2.lean` + `TermWireV2Theorems.lean` | `parseTerm_serializeTerm`, `resolve_toWire` |
| PTD2 | `Storage/PagedTermDictionary.lean` generalised over a codec structure, instantiated twice; PTD1 bytes unchanged | the existing `decode?_encode?` once, over the abstraction |
| IBK5 | `Storage/IndexedBlockWireV5.lean` + theorems | `decode_encode?`, `denotes_decode_encode?` at `WireTerm`, plus resolution |
| LGI2 | `Storage/LiteralGramIndexWire.lean` version 2 | round trip; `mem_candidatesSpec` restated with the opaque list |
| SBM10 | `Storage/ShardManifest.lean` | `decode?_encode?` extended; `zoneMap_sound` |
| publication every batch | `Storage/PackStream.lean`, `PredicateQuadBlocks.lean`, `Harness/PredicateShardPack.lean`, `Wasm/Ops/Pack.lean` | dataset equality with the buffered route |
| readers | `Harness/ShardActivate.lean`, `Harness/QuadQuery.lean`, `SPARQL/StoreDataset.lean`, `Wasm/Ops/Store.lean`, `Wasm/Ops/StoreHandles.lean`, `npm/factoidal/bin/*.mjs` | gates below |

## 9. Gates

1. `lake build` clean; `tools/lean-hygiene-audit.py` at or below baseline.
2. Every existing `#guard` and the committed hub blocks under
   `docs/web/hub/assets/blocks/lifesci-crossgraph/` byte-identical (PTD1
   and IBK3 untouched).
3. `tools/blockengine-ibk4-quad-smoke.sh` updated to version 10: the
   quad fixture packs, activates, answers the same rows; the tamper test
   still refuses; a fixture with a triple term, a directional literal and
   a 70,000-byte literal round-trips through pack, activate and query.
4. Row identity: the four skosdex vocabularies of the blocks-per-predicate
   record packed by version 9 and by version 10, the same ten queries,
   identical answer rows.
5. Memory ladder: 52 MB, 105 MB, 210 MB, 1,543 MB of skosdex N-Quads,
   peak footprint against source; the slope must be zero within the
   constant of one batch.
6. Zone-map selectivity: a bound-subject query on `skos:prefLabel` over the
   full skosdex corpus, blocks opened before and after.
7. `bash formal/lean4/Wasm/native-smoke.sh`, `tools/wasm-store-query-smoke.sh`,
   `node tests/store-host/conformance.mjs`, `node tests/store-host/cli.mjs`
   after a wasm rebuild.
8. Specification sections 6.1, 6.2, 6.3 and 10 updated; the ceilings
   table of section 2 copied into the specification.

## 10. Gate results, 2026-09-05

Measured on the MacBook Air the project runs on, with one binary per row.
Every number is from the run named beside it; nothing is an estimate.

### The packer and the readers

| Gate | Result |
|---|---|
| 1 `lake build` | clean |
| 1 `tools/lean-hygiene-audit.py` | `sorry` 0, user `axiom` 0, `native_decide` 0, `unsafe` 0, `@[implemented_by]` 0, `partial def` 172 (baseline 172) |
| 2 committed hub blocks | unchanged; PTD1 and IBK3 were not touched |
| 3 `tools/blockengine-ibk4-quad-smoke.sh` | pass, unchanged from wire version 9 |
| 3 `tools/blockengine-ibk5-quad-smoke.sh` (new) | pass |
| 3 `tools/blockengine-ibk5-w3c-trig-smoke.sh` (new) | 241 pass, 0 fail (out of 241) |
| 3 `tools/blockengine-ibk4-w3c-trig-smoke.sh` | 241 pass, 0 fail (out of 241) |
| 7 `formal/lean4/Wasm/native-smoke.sh` | 85 pass, 0 fail (out of 85) |
| 7 wasm and npm host | NOT RUN; the WebAssembly and host side is the next piece of work |

### Gate 4 — row identity, version 9 against version 10

The 209,715,187-byte skosdex N-Quads prefix, cut at a line boundary, packed
under both tags and activated, then the ten query shapes of
[`2026-09-05-pack-publication-every-batch.md`](2026-09-05-pack-publication-every-batch.md)
section 6 run against both with ONE binary, the `shards=` header line
stripped.

**The two outputs are identical over 186 lines. GATE 4 PASSES.**

Answers: 17,648 rows, 0, 2,634, 1,392, 4,887, `true`, `false`, 0, 17,426 and
1. Two of the ten answer zero rows and are therefore weak comparisons; they
are reported as they ran rather than replaced afterwards. Query 2 asks for
`skos:broader` in a graph that uses none, and query 8 asks for a
`skos:prefLabel` subject in `iptc-mediatopic` with no `skos:definition`, of
which there are none.

| | wire version 9 | wire version 10 |
|---|---|---|
| pack wall clock | 83.57 s | 84.77 s |
| pack peak memory footprint | 349,143,040 bytes | 242,778,112 bytes |
| generation size | 167,488 KiB | 143,236 KiB |
| rows | 942,869 | 942,869 |
| blocks | 1,252 | 1,252 |
| activation wall clock | 23.60 s | 52.68 s |

Version 10 is 14.5% SMALLER, which is LGI2's LEB128 posting gaps against
LGI1's fixed u32, and it packs in the same time. Activation costs 2.2x
because it REBUILDS the LGI2 and the GBI1 index of every block and compares
them, which SBM8 and SBM9 activation does not do; 52.68 s for a 1,252-block
generation is what made that affordable.

The block set is identical, predicate by predicate, to version 9's. The
version-2 term width in `PredicateQuadBlocks.quadWireBytes` moved no block
boundary on this corpus, whose largest literal is 38,201 bytes.

### The cost that was NOT the format

The first version-10 pack of that prefix took 243.57 s against version 9's
72.62 s. `/usr/bin/sample` put 10,159 of 15,405 samples inside one
`List.length`: `readNQuad12` passed `cs.length + 1` as the fuel bounding
`<<( ... )>>` nesting, where `cs` is the whole remaining input, so it walked
the rest of the buffer once per statement. Version 10 reads its source as
RDF 1.2 (section 4), which made it the first route through that reader.

Counting to the next line break instead took a 52,428,626-byte pack from
53.96 s to 23.08 s with every artifact byte-identical. Version 9 packs the
same prefix in 17.07 s, so the format's own cost is 1.35x at 52 MB and 1.01x
at 210 MB, not 3.16x.

Recorded because the first reading of the 3.35x was "the new codec is
slower", and that reading was wrong. A pack profile costs one `sample` run.

### Gate 5 — memory against source

Wire version 10, N-Quads, the default 268,435,456-byte batch. Peak footprint
is bounded by one batch plus the carried rows, not by the source.

| source bytes | quads | blocks | pack wall clock | peak footprint |
|---|---|---|---|---|
| 52,428,626 | 260,286 | 1,018 | 23.08 s | 188,874,752 bytes |
| 209,715,187 | 942,869 | 1,252 | 84.77 s | 242,778,112 bytes |
| 1,543,478,120 | 7,316,318 | 3,306 | 743.83 s | 396,869,632 bytes |

29.4x the source for 2.1x the memory. The 105 MB rung of the stated ladder
was not run.

The full corpus activated in 390.90 s (3,306 blocks, 758,894,348 verified
logical bytes) and its generation is 922,920 KiB.

### Gate 6 — zone-map selectivity

`SELECT ?l WHERE { GRAPH ?g { <http://cv.iptc.org/newscodes/mediatopic/>
skos:prefLabel ?l } }` against the full corpus, beside the same shape with an
unbound subject. Entries SELECTED is what the planner opens; entries EXCLUDED
is what the zone maps dropped after the predicate and graph collectors kept
them.

| | entries selected | entries excluded by the zone maps | bytes read | wall clock |
|---|---|---|---|---|
| unbound subject | 258 | 0 | 103,341,569 | 43.92 s |
| bound subject | 28 | 230 | 14,264,765 | 7.41 s |

9.2x fewer entries, 7.2x fewer bytes, 5.9x faster. **GATE 6 PASSES** on a
source in its natural, graph-grouped order.

### The shuffled source, and what it says about the BLOCK SET

The degenerate case was to be a shuffled 210 MB prefix. It was killed after
it had written 152,714 files, because `shuf` had turned it into something
else: the packer cuts a block at every GRAPH CHANGE, and a shuffled N-Quads
source changes graph on nearly every line, so almost every run closes at one
or two rows. Measured on a 10,485,723-byte prefix and its shuffled twin,
both packed at wire version 10:

| | natural order | shuffled |
|---|---|---|
| quads | 50,386 | 47,166 |
| blocks | 483 | 25,813 |
| pack wall clock | 4.21 s | 102.09 s |
| pack peak footprint | 117,932,032 bytes | 1,346,781,184 bytes |
| generation size | 20,376 KiB | 650,928 KiB |
| activation | 3.43 s | 80.68 s |

(The two prefixes hold different statements — 10 MB of a shuffled file is not
a permutation of 10 MB of the sorted one — so the row counts differ by 6%.
The re-measurement below fixes that: it shuffles the natural prefix itself,
so both inputs hold the same 50,386 statements.)

The zone maps themselves do NOT degrade. On the shuffled generation the
bound-subject query selected 5 entries of 5,601 and the maps excluded 5,596,
against 9 of 73 with 64 excluded in natural order: a block of two rows has a
very narrow subject range. What degrades is the BLOCK SET, and with it the
manifest: 25,813 entries, and both queries then spent about 150 s, almost all
of it decoding and validating that manifest rather than reading blocks — the
bound query read 2,303 bytes of block data in 183.66 s.

So the zone map's dependence on source order, which section 6.1 predicted,
is not the finding. The finding is that the graph-change cut rule has no
lower bound on block size, and that an interleaved N-Quads source therefore
produces one block per graph run. `minBatchRows` bounds what the BATCH rule
publishes and does not bound this. Two candidates were listed here: a
minimum row count before the graph-change rule may close a run, or a block
that holds several graphs with a graph column already in every row. Tracked
at <https://github.com/danbri/factoidal/issues/658>.

### The repair, measured 2026-09-05: bucket by (predicate, graph)

Neither candidate was taken. The bucket key is now the PAIR (predicate,
graph), so a bucket's rows are all one graph by construction and rule 2 has
no graph rule left — only the row and byte targets. Interleaving never closes
a run.

Re-measured on the 10,485,664-byte natural prefix (`head -c 10485723 | sed
'$d'`) and its `sort -R` permutation, which hold the SAME 50,386 statements
(`sort | md5` agrees). Both packed at wire version 10 (`ibk5`), by the packer
at `claude/main` and by this one, and queried with ONE binary.

| | natural, main | natural, this | shuffled, main | shuffled, this |
|---|---|---|---|---|
| quads | 50,386 | 50,386 | 50,386 | 50,386 |
| blocks | 483 | 483 | 11,636 | 483 |
| pack wall clock | 3.79 s | 3.76 s | 20.15 s | 3.92 s |
| pack peak footprint | 115,720,192 bytes | 115,949,568 bytes | 591,052,800 bytes | 122,617,856 bytes |
| generation size | 20,376 KiB | 20,376 KiB | 304,820 KiB | 20,792 KiB |
| activation | 3.00 s | 2.99 s | 21.88 s | 3.28 s |

The shuffled block count is now the natural one, 483: the bucket SET is the
set of (predicate, graph) pairs the source holds, and no bucket of this
prefix reaches a size target, so source order cannot change it. The shuffled
generation is 416 KiB larger than the natural one because the row order
inside a block follows the source, which changes each block's dictionary.

The queries, `skos:prefLabel` with a bound subject
(`<http://cv.iptc.org/newscodes/authoritystatus/>`) and with an unbound one,
both inside `GRAPH ?g`:

| | entries selected | entries excluded by the zone maps | rows | wall clock |
|---|---|---|---|---|
| natural, main, bound | 21 | 52 | 1 | 0.42 s |
| natural, this, bound | 21 | 52 | 1 | 0.40 s |
| shuffled, main, bound | 2 | 4,448 | 1 | 23.76 s |
| shuffled, this, bound | 21 | 52 | 1 | 0.50 s |
| natural, main, unbound | 73 | 0 | 20,002 | 0.90 s |
| natural, this, unbound | 73 | 0 | 20,002 | 0.90 s |
| shuffled, main, unbound | 4,450 | 0 | 20,002 | 25.57 s |
| shuffled, this, unbound | 73 | 0 | 20,002 | 1.09 s |

Rows agree in every cell. On the shuffled source the bound query goes from
23.76 s to 0.50 s and the unbound one from 25.57 s to 1.09 s, and the
selected-entry counts become the natural-order ones. The shuffled main run
selects FEWER entries for the bound query (2 of 4,450) and is still 47 times
slower, because the cost is the manifest, not the block data — the same
effect the 150 s figure above reports.

