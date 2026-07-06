# HDT (Header-Dictionary-Triples) program plan

Scoping doc for HDT as a **read-only compact backend beside COTTAS**,
modeled on the stage structure in
[`2026-07-05-vc-program-plan.md`](2026-07-05-vc-program-plan.md).
Opens the track that
[`2026-07-05-disk-backed-db-perf-review.md`](2026-07-05-disk-backed-db-perf-review.md)
§4.b scoped and sequenced as roadmap item 7 ("Dictionary-ID COTTAS v2 +
HDT reader track … both need their own design docs before code"). This
is that design doc, plus stage 1 landed alongside it.

**What HDT buys here** (perf-review §4.b, measured motivation §2.c):
mmap-able read-only querying with no parse-to-RAM — the antidote to the
O(store) materialization wall (731 MiB peak RSS for a 1-row answer on
the 889k-triple gene corpus); very compact single-file artifacts
(front-coded dictionary + bitmap-encoded triples); a mature
publication/exchange ecosystem (LOD Laundromat, Wikidata dumps,
Triple Pattern Fragments servers); and rank/select navigation instead
of column decode.

**What it costs:** read-only (no UPDATE — the writable story stays
COTTAS + SPARQL UPDATE; see "Out of scope"); triples only in HDT 1.0
(no named graphs — quads need the HDTq extension or per-graph HDT
sets, deferred); index/rank-select build cost at load time unless the
`.hdt.index` sidecar convention is adopted later.

**Prior art in this repo, and what this plan replaces.**
[`Parser.BallyhooHDT.fst`](../../formal/fstar/Parser.BallyhooHDT.fst)
(173 lines) is an interface-only module: types + 10 `assume val`s,
realised by shelling out to an external `hdtSearch` CLI via
`experimental_ocaml_glue/ballyhoo_hdt_runtime.sh` (555 lines of OCaml
— the rule-#11 debt tracked in #253,
[`2026-05-13-issue-253-hdt-runtime-retirement-plan.md`](2026-05-13-issue-253-hdt-runtime-retirement-plan.md)).
That plan migrated the *term cache shape* to F\* but kept the byte
format behind `assume val parse_front_coded_section`. This program
goes further per iron rules #1/#2/#4: the **byte format itself is
parsed in F\***, the way `Parquet.Footer.fst` (~2,600 lines) parses
Parquet — leaving only the generic file-range read as `assume val`
I/O. When stage 4 lands, `Parser.BallyhooHDT`'s assume-vals and the
555-line runtime script retire together, closing #253 by superseding
it.

## Format landscape

| Document | Status | Role for us |
|---|---|---|
| HDT W3C Member Submission (30 March 2011) | Member Submission, not Rec-track | Concept reference; byte details superseded |
| [rdfhdt.org HDT binary format](https://www.rdfhdt.org/hdt-binary-format/) (draft 03/07/2015, "v1.0") | de-facto spec, self-described as superseding the Submission's binary details | Primary byte-layout reference |
| hdt-cpp (reference C++ implementation; 1.3.x line) | the implementation every published `.hdt` file comes from (directly or via hdt-java, which interoperates) | **Normative-in-practice.** Where the draft page and hdt-cpp disagree, files on disk follow hdt-cpp |
| HDTq / "HDT with quads" (Fernández et al.) | research extension | Out of scope (triples only this program) |

**Spec-page vs hdt-cpp discrepancies found while scoping (read from
vendored hdt-cpp-1.3.3 sources, see Test strategy for provenance).**
These are exactly the traps a spec-only implementation would fall
into, so they are recorded here and pinned by stage-1 tests:

1. The spec page says a DictionarySection "starts with an unsigned
   32bit value preamble denoting the type". hdt-cpp writes and reads
   **one byte** (`CSD.h`: `unsigned char type`; PFC = 2).
2. hdt-cpp's PFC section preamble carries **three** VBytes
   (`numstrings`, `bytes`, `blocksize`) — the spec page lists only
   two, relegating blockSize to header metadata.
3. The spec page requires a `numTriples` property in the Triples
   control information; hdt-cpp 1.3.3's `BitmapTriples::save` writes
   only `order`. The authoritative triple count lives in the Header
   RDF metadata (`hdt:triplesnumTriples`).
4. A zero-bit bitmap still stores **1 data byte**
   (`BitSequence375::numBytes(0) = 1`), where the byte-count formula
   `ceil(bits/8)` would give 0. The log-array formula has no such
   special case (`ceil(bits*entries/8)`).

### Byte layout (as implemented by hdt-cpp, the layout stage 1 parses)

All multibyte integers little-endian. Three CRC flavours:
CRC8 (poly 0x07, init 0x00, unreflected), CRC16-ANSI/ARC (poly
0x8005 reflected — table equivalent of poly 0xA001 — init 0x0000,
xorout 0), CRC32C Castagnoli (poly 0x1EDC6F41 reflected, init
0xFFFFFFFF, final xor 0xFFFFFFFF). **VByte** is 7-bit
little-endian groups where continuation bytes have the high bit
**clear** and the final byte has the high bit **set** — the inverse
of the protobuf/Parquet varint convention; misreading this parses
every count wrong.

```
file            := global-ci header-section dictionary-section triples-section
control-info    := '$HDT'(4) type(1: 0=Unknown 1=Global 2=Header
                   3=Dictionary 4=Triples 5=Index)
                   format-URI NUL properties NUL crc16(2)
                   -- properties: "key1=value1;key2=value2;" (ASCII, may be empty)
                   -- crc16 covers cookie..second NUL inclusive
global-ci       := control-info with type=Global,
                   format=<http://purl.org/HDT/hdt#HDTv1>
header-section  := control-info(type=Header, format="ntriples",
                   props: length=<bytes>) header-bytes[length]
                   -- header-bytes: N-Triples text, NO trailing CRC
dictionary      := control-info(type=Dictionary,
                   format=<http://purl.org/HDT/hdt#dictionaryFour>,
                   props: mapping=…, sizeStrings=…, elements? )
                   pfc-section(shared) pfc-section(subjects)
                   pfc-section(predicates) pfc-section(objects)
pfc-section     := type(1: 2=PFC) vbyte(numstrings) vbyte(bytes)
                   vbyte(blocksize) crc8(1)
                   log-array(block-start-offsets)
                   packed-blocks[bytes] crc32(4)
log-array       := type(1: 1=LOG64) numbits(1) vbyte(numentries) crc8(1)
                   data[ceil(numbits*numentries/8)] crc32(4)
triples         := control-info(type=Triples,
                   format=<http://purl.org/HDT/hdt#triplesBitmap>,
                   props: order=1(SPO))
                   bitmap(Y) bitmap(Z) log-array(Y) log-array(Z)
bitmap          := type(1: 1=plain) vbyte(numbits) crc8(1)
                   data[bits=0 ? 1 : ceil(numbits/8)] crc32(4)
```

Packed-blocks content (stage 2): strings sorted, grouped in blocks of
`blocksize`; first string of each block plain + NUL, the rest as
`vbyte(common-prefix-len) suffix NUL`. IDs are 1-based per section;
with the standard mapping, subject ID space = shared ∪ subjects,
object ID space = shared ∪ objects, so a term lookup consults two
sections.

BitmapTriples content (stage 3): SPO forest as two levels. `ArrayY` =
predicate IDs, `BitmapY[i]=1` marks the last predicate of each
subject; `ArrayZ` = object IDs, `BitmapZ[i]=1` marks the last object
of each (subject, predicate) pair. Arrays are log-width packed
integers (width = `numbits` per entry, little-endian bit order within
64-bit words). Navigation from subject *s*: `select1(BitmapY, s-1)+1
.. select1(BitmapY, s)` gives the Y range; each Y position maps
through `rank1/select1(BitmapZ)` to its Z (object) range. Bound-S
patterns are one select + a range walk; other orders need either a
scan or the FoQ-style extra index (out of scope until stage 5+).

## Test strategy (iron rule #6: real files)

### What was reachable from this sandbox (2026-07-06, all attempts logged)

- `github.com/rdfhdt/*` and `codeload.github.com`: **HTTP 403 through
  the proxy** (clone/tarball unavailable). `api.github.com`: 403. The
  session's GitHub MCP is scoped to `danbri/factoidal` only.
- `raw.githubusercontent.com`: reachable (200), but the libhdt/hdt-java
  test-fixture paths could not be enumerated without the API, and
  spot-guessed paths 404'd.
- `rdfhdt.org`: reachable. The datasets page publishes only
  **corpus-scale** `.hdt` dumps (Wikidata ~GBs, DBpedia 2016-10, via
  `hdt-dumps.cluster.ai.wu.ac.at` / `gaia.infor.uva.es`) — real but
  far too large to vendor. No small example `.hdt` files are linked
  from the downloads page (the old hdt-it/hdt-java example bundles
  point at dead Google Code URLs).
- **PyPI: reachable — and decisive.** The `hdt` 2.3 sdist (pyHDT,
  Thomas Minier, MIT) **vendors the complete reference
  `hdt-cpp-1.3.3` C++ sources** (libhdt + libcds, including
  `HDTManager::generateHDT`, the PFC dictionary writer, BitmapTriples
  writer, and all three CRC implementations). A ~30-line driver
  compiled against those sources (plus Ubuntu's `libserd-dev` for the
  reference N-Triples front end) yields a working reference
  `rdf2hdt`, producing byte-real `.hdt` files.

### Vendoring set (what stage 1 commits)

`third_party/testing/hdt/` with a provenance README, containing
fixtures **generated by the reference implementation** (hdt-cpp-1.3.3
via the pyHDT sdist) from RDF files **already vendored in this
repository**:

| Fixture | Source input (already in-tree) | Why |
|---|---|---|
| `rml-core-ontology.hdt` | `third_party/testing/rml-modules/rml-core/ontology/documentation/ontology.nt` (44 KB, 343 triples) | Mid-size real ontology: literals with language tags + datatypes, bnodes, shared subject-objects — exercises all four dictionary sections |
| `rdf-mt-test002.hdt` | `third_party/testing/w3c/rdf/rdf11/rdf-mt/datatypes/test002.nt` (W3C rdf-tests) | Minimal real W3C file; small enough to hand-verify every section offset |

Ground truth for each fixture is its input `.nt` (known triple set,
parseable by our own verified `Parser.NTriples`) plus the stats the
reference tool writes into the fixture's own Header section
(`void:triples`, `hdt:dictionarynumSharedSubjectObject`, …), which
stage-1/2 tests cross-check against section-derived numbers.

**Upgrade path:** when GitHub is reachable (CI, or a session without
the proxy restriction), add `rdfhdt/libhdt`'s `tests/` data and/or an
hdt-java-generated sibling of the same inputs to pin cross-
implementation compatibility. Recorded as a stage-2 acceptance
criterion, not a blocker.

### Regeneration recipe (documented in the fixture README)

pip-download `hdt==2.3` sdist → compile the vendored
`hdt-cpp-1.3.3` sources + a `mini_rdf2hdt.cpp` driver
(`g++ -std=c++11 -include cstdint -DHAVE_SERD … -lserd-0`) → run
`mini_rdf2hdt <input.nt> <output.hdt> <baseURI>`. No network beyond
PyPI + apt. The driver source is committed next to the fixtures.

## Stages

Stage boundaries follow the container's own structure, so each stage
is a commit-sized deliverable with its own fixtures-derived
acceptance test (the perf-review's "verified F\* spec first, OCaml
reduced to write_bytes/read_bytes" discipline, and anti-pattern
#23/#24 for dispatch).

### Stage 1 — container + header (THIS COMMIT)

New module [`HDT.Container.fst`](../../formal/fstar/HDT.Container.fst)
(naming: follows the `Parquet.Footer` precedent — binary container
modules are named by format, the `Parser.*` namespace stays reserved
for W3C concrete text syntaxes; `Parser.BallyhooHDT` remains the
store-boundary interface until stage 4 supersedes it):

- Control-information block parser over hex-encoded bytes (same byte
  representation as `Parquet.Footer`, same generic `assume val` file
  readers **reused from `Parquet.Footer`** — zero new `assume val`s,
  zero new glue; the module is pure F\* on top of the existing I/O
  boundary).
- **CRC16-ANSI validated in pure F\*** on every control-information
  block (cheap: CI blocks are tens of bytes; bitwise reflected
  implementation, no table). CRC8/CRC32C over section payloads are
  **not** validated in stage 1 — they guard payloads stage 1 does not
  decode — and move to stage 2/3 alongside payload decoding, with the
  io-verification hash pattern of
  [`2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md)
  as the model (stage-1.5 item if a need appears earlier).
- VByte decoder (HDT convention), log-array and bitmap **skippers**
  (header-arithmetic only: type/width/count + size formulas above),
  PFC-section skipper — enough to compute every section boundary
  without decoding strings.
- Header section decoded as N-Triples text via the verified
  `Parser.NTriples.parse_ntriples` (iron rule #4 dividend: the header
  parser costs zero new lines).
- Section inventory record exposing: global/header/dictionary/triples
  CI offsets + formats + properties, header byte range + parsed
  header triples, per-PFC-section `numstrings/bytes/blocksize` +
  byte ranges, triples CI offset + declared order.
- Probe consumer `bin/hdt-probe/` (outside the verified boundary per
  rule #11) printing the inventory of a real `.hdt` file.

**Acceptance:** verifies clean (z3 4.13.3, no `--lax`); on both
vendored fixtures the probe reports the full section inventory;
header triple count parsed from the Header RDF equals the fixture
input's triple count; every CI CRC16 validates; regression pins for
section offsets + dictionary counts + a loud truncation failure.

**Status 2026-07-06: landed and measured.** `HDT.Container.fst` (521
lines) verifies clean; on `rml-core-ontology.hdt` the probe reports
the exact tiling (header data 69..1770, dictionary sections
1846..8353 with shared/subjects/predicates/objects =
39/45/22/134 strings, triples data at 8409, order SPO), all four CI
CRC16s validate, and the Header decodes through `Parser.NTriples` to
metadata agreeing with the section-derived numbers (`void:triples`
343 = input count; `distinctSubjects` 84 = 39 shared + 45 subjects;
`distinctObjects` 173 = 39 + 134; `void:properties` 22 = predicate
section size). `bin/hdt-probe/check.sh`: 25 checks, 25 pass, 0 fail
(including truncation-must-fail-loudly). Registration in
`build-ocaml.sh` / `tests/unit/run-all.sh` is the coordinator's
landing step.

### Stage 2 — PFC dictionary decode + ID↔term lookup

Front-coded block decode in F\*: `pfc_extract (section) (id) : option
string` (select block via log-array, walk ≤ blocksize suffixes) and
`pfc_locate (section) (term) : option nat` (binary search on block
heads + in-block walk). Four-section composition with the
shared-section ID arithmetic (`mapping` handling). CRC8/CRC32C
validation of dictionary payloads lands here. Term↔`rdf_term`
mapping reuses the N-Triples term grammar (dictionary strings are
stored in N-Triples-like surface syntax, except plain IRIs are
unbracketed and the leading type marker distinguishes
literal/IRI/bnode — pin against fixtures).

**Acceptance:** for every fixture, dumping all four sections
reproduces exactly the term set of the input `.nt` (compared via our
own parser); `pfc_locate (pfc_extract i) = i` for all IDs, both
directions, pinned in unit tests; CRCs validate; cross-check
`dictionarynumSharedSubjectObject` etc. against the Header metadata.
Stretch: vendor a libhdt-tests or hdt-java-generated fixture when
reachable (cross-implementation pin).

### Stage 3 — BitmapTriples navigation, naive rank/select in F\*

Decode the two bitmaps + two log-arrays (log-width packed integer
`get i`, bitmap `access/rank1/select1`) with **naive O(n) or
O(n/word) implementations first** — correctness before speed,
measured separately per the perf-benchmarking discipline. SPO-tree
navigation: `subject_slice`, `(s,p)_slice`, full enumeration; pattern
resolution for bound-S shapes; scan fallback for the rest.

**Acceptance:** enumerating all triples of each fixture through
BitmapTriples equals the input `.nt` triple set (via ID→term from
stage 2); rank/select unit lemmas (`rank1 (select1 b k) = k+1` on the
fixture bitmaps); payload CRC32C validated.

### Stage 4 — SPO pattern resolution → the planner's typed access path

Wire HDT pattern resolution into the store-capability surface the F\*
planner already consumes:
[`SPARQL.Plan.AccessPath.fst`](../../formal/fstar/SPARQL.Plan.AccessPath.fst)'s
typed `access_path` ADT (`AP_Skip` / `AP_OffsetJump` / `AP_FullScan`)
is the recovery-plan Phase-6 pattern to follow — a pure decision
function from "what's bound" + "what the store advertises" to a typed
plan value, consumed by the reader. HDT adds its own access-path
alternatives (bound-S select-jump vs scan), either as an HDT-shaped
sibling ADT or by generalising `access_path` — decide at
implementation time, in F\*. This stage replaces
`Parser.BallyhooHDT`'s 10 `assume val`s with calls into stages 1-3
and **deletes `ballyhoo_hdt_runtime.sh` (555 lines), closing #253**;
the LazyTermCache glue (~80 lines per the #253 plan) survives as the
only HDT-specific OCaml.

**Acceptance:** SPARQL SELECT over an `--data-hdt` store answers
byte-identically to the same query over the fixture's `.nt` loaded
in-memory (backend-parity regression, same pattern as
`tests/local/backend_parity_regressions.sh`); W3C floors unchanged;
`ballyhoo_hdt_runtime.sh` deleted; #253 closed.

### Stage 5 — optimized rank/select, joining the Roaring/KaRaMeL track

Replace naive rank/select with indexed structures (BitSequence375-
style superblock/block counters — the same structure the reference
implementation uses, hence the name). This is the **shared core with
the Roaring track**:
[`2026-05-07-c-build-and-roaring-plan.md`](2026-05-07-c-build-and-roaring-plan.md)
Phase B's bitmap container already lands a verified pure-F\*
`popcount_u64` (`formal/roaring/src/Bits.fst`, PR #137) with lemmas
tying popcount to set denotation — rank = prefix-sum of popcounts,
select = search over ranks, so one verified popcount/rank/select core
serves the Roaring bitmap store AND the HDT BitmapTriples reader AND
(KaRaMeL-compatible, `noeq`-free) the C/wasm extraction pilot.
Measure before/after per perf-benchmarking; consider the `.hdt.index`
(FoQ) sidecar for non-SPO access orders as a follow-up decision.

**Acceptance:** measured speedup on a corpus-scale HDT (e.g. a
generated gene-corpus HDT, 889k triples) for bound-S and bound-P
patterns vs stage-3 naive, with W3C + parity floors unchanged; the
rank/select module verifies standalone and extracts to krml cleanly
(Roaring plan §2.1 constraints).

## The wasm/js story

Nothing HDT-specific blocks either target, by construction:

- Stage-1+ logic is pure F\* over hex strings; the only I/O is the
  existing `parquet_read_range_hex`-style file-range assume-val,
  which js_of_ocaml/wasm_of_ocaml already realise for COTTAS (the
  browser demo ships `Parquet.Footer`). An HDT file in the browser is
  a fetched `ArrayBuffer` behind the same range-read boundary.
- HDT is the *better* browser backend long-term: one compact
  immutable file, HTTP range-request friendly (the Triple Pattern
  Fragments ecosystem serves exactly this way), no zstd dependency
  (HDT payload bytes are raw; the whole-file `.gz` convention is
  handled before the boundary).
- The stage-5 rank/select core is deliberately KaRaMeL-compatible
  (no `noeq`, machine integers), keeping the C/wasm-via-C route open
  per the Roaring plan.
- Per-target parity lands with stage 4's backend-parity regression
  run under node + wasm (the `test-suites` cross-runtime discipline).

## Out of scope (explicitly)

- **Writing HDT.** HDT is read-optimized; a verified HDT *writer*
  (`serialize : hdt -> Tot (list u8)` per rule #11) is a clean later
  program but not this one. Our writable story remains COTTAS +
  SPARQL UPDATE (#100 Phase 4). One plan = one deliverable track per
  anti-pattern #23/#24.
- **HDTq / named graphs.** HDT 1.0 carries triples only; the fixture
  and stages 1-5 target the default graph. Datasets-of-HDTs and HDTq
  are follow-up design docs.
- **FoQ index sidecar (`.hdt.index.v1-1`)** parsing — revisit at
  stage 5.
- **Literal dictionary variants** (HTFC, FM-index, …): stage 2
  rejects non-PFC section types loudly (`None`), the same
  dispatch-on-declared-encoding rule the Parquet reader adopted in
  the 2026-07-05 RLE_DICTIONARY fix.

## Open decisions

1. **Generalise `SPARQL.Plan.AccessPath.access_path` vs an HDT-shaped
   sibling ADT** (stage 4). Leaning sibling-then-unify: the COTTAS
   variant is offset-index-shaped; premature unification would couple
   the two backends' planners.
2. **Corpus-scale generated fixture** (gene corpus → ~889k-triple
   HDT, ~10-20 MB): vendor vs regenerate-on-demand. Leaning
   regenerate (recipe committed, artifact gitignored) to keep the
   repo lean; decide when stage 5 needs it.
3. **`$HDT` cookie vs `HDT` global format IRI check strictness**:
   hdt-java historically wrote minor property variations; loosen only
   against evidence from real files, never preemptively.

## Cross-references

- [`2026-07-05-disk-backed-db-perf-review.md`](2026-07-05-disk-backed-db-perf-review.md)
  §4.b (the case for HDT), §2.c (the O(store) wall it addresses),
  roadmap item 7 (sequencing).
- [`2026-05-07-c-build-and-roaring-plan.md`](2026-05-07-c-build-and-roaring-plan.md)
  — the rank/select / popcount shared core (stage 5).
- [`2026-05-13-issue-253-hdt-runtime-retirement-plan.md`](2026-05-13-issue-253-hdt-runtime-retirement-plan.md)
  — superseded by stage 4 (this plan deletes the runtime it planned
  to shrink).
- [`2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md)
  — hash round-trip witness pattern for payload CRCs (stages 2-3).
- [`2026-04-19-hdt-fstar-status.md`](2026-04-19-hdt-fstar-status.md)
  — the pre-plan status doc this supersedes.
- [`formal/fstar/HDT.Container.fst`](../../formal/fstar/HDT.Container.fst)
  — stage 1 implementation.
- [`third_party/testing/hdt/README.md`](../../third_party/testing/hdt/README.md)
  — fixture provenance.
