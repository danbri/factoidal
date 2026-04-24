# Critical Review: "Second Backend Options" vs F\*-First Iron Rules

**Date:** 2026-04-25
**Reviewer:** Agent Chi
**Subject:** [`2026-04-25-second-backend-options-oxigraph-qlever.md`](2026-04-25-second-backend-options-oxigraph-qlever.md)
**Related diagnoses:**
[`2026-04-25-cottas-parquet-load-path-perf.md`](2026-04-25-cottas-parquet-load-path-perf.md) (Codex),
[`2026-04-24-turtle-parser-perf-diagnosis.md`](2026-04-24-turtle-parser-perf-diagnosis.md) (Delta),
[`2026-04-25-protocol-http-rdf-update-scoping.md`](2026-04-25-protocol-http-rdf-update-scoping.md) (Tau).

The source doc is well intentioned — it diagnoses a real problem and reaches
for well-known prior art. The problem is that the framing ("second backend
options") imports a vocabulary that is, in this project, dangerous. This
review re-grounds the conversation in CLAUDE.md's iron rules.

---

## 1. The legitimate problem

It is real and uncontested:

- `factoidal --data-cottas` on the 3.14 M-quad UK Parliament artifact spends
  ~90 s in `load_cottas_dataset` / `load_cache` before any algebra evaluation
  begins (Codex).
- The hot frames are `Parquet_Footer.skip_varint_hex` /
  `decode_varint_hex` / `BatUTF8.nth_aux` — i.e. **per-cell** footer probing
  through hex-string/UTF-8 traversals. ~12.6 M per-cell fetches for one
  `COUNT(*)`.
- This compounds with the **graph-construction layer** O(N²) hotspot Delta
  identified in `RDF.Graph.Executable.fst:248-249` (`graph_add` linearly
  dedupes and tail-appends every quad).

A user typing `COUNT(*)` and waiting ~90 s on a mid-sized public corpus is a
real failure mode. We must fix it. The disagreement is not on **whether**;
it is on **how**, and on what the source doc proposes to call the fix.

---

## 2. The source doc's proposal, examined under the iron rules

The source doc's recommendation (§ "Recommendation", § "Concrete
recommendation") is to build:

> a Factoidal-native immutable permutation backend (QLever-shape, Oxigraph
> permutation coverage), with a Python or Rust external builder and a
> verified F\* reader.

Read carefully, **this is not actually a "second backend" in the dangerous
sense.** Phase 4 explicitly says the *reader* is in F\*, and Phase 3 only
sends the *builder* (the offline indexer) to Python/Rust. That is much
closer to F\*-first orthodoxy than the title suggests. But the doc's framing
and option-comparison structure invite three drift modes that the iron rules
forbid, and these need to be called out before implementation begins.

### 2a. RocksDB / Oxigraph-as-engine — correctly rejected

The source doc already concludes: "Bad binary/runtime target". I concur and
strengthen it: an LSM KV with mutable compaction snapshots is not just a
"bad target" — it is a non-target under rule #1. Verifying RocksDB's
compaction and snapshot semantics is years of work outside the SPARQL
problem. Any proposal to **link librocksdb_sys** (the Rust crate) into an
extracted OCaml binary should be rejected; that gives us an unverified C++
core under our nominally verified surface and makes KaRaMeL → C / Wasm
extraction (the medium-term goal) impossible.

### 2b. QLever-shape immutable permutations — direction is fine, framing is risky

Sorted dictionary-encoded permutation files **are** a verification-friendly
shape. The actual concern is that the source doc treats this as parallel to
COTTAS, when it should be presented as **the next iteration of the same
verified column-store path COTTAS already started**. Two on-disk formats
maintained side by side is the cobbling rule #7 cautions against, even if
both readers are F\*. Recommendation: rename in any successor doc from
"second backend" to "v2 on-disk format" and explicitly retire the v1
load-path once v2 is wired.

### 2c. The unstated drift risk — query engine swap-in

Nowhere does the source doc *propose* routing SPARQL to oxigraph at query
time. But the title and the option-comparison framing leave the door open
for a future agent to read this as licence to embed pyoxigraph as a query
backend "for the slow case". That would violate rule #1 outright: F\* is
the product. **The review's strongest non-negotiable is: SPARQL evaluation
stays in `SPARQL11.Algebra.fst`, full stop.** This needs to be written down
before a follow-up agent does a `pip install pyoxigraph` in `factoidal_cli`.

---

## 3. The F\*-first alternative path (what should actually happen)

The source doc's Phase 1 ("make the diagnosis visible") and the Phase 4–5
verified reader are the parts to keep. Sequenced against Codex's and Delta's
diagnoses, the F\*-first work order is:

### Step A — fix what's already wrong, in F\* (no new format)

These fixes are local to existing F\* modules and unblock both load paths:

1. **Parquet footer cache** — `Parquet.Footer.fst`. Decode the footer once
   per file open, memoize column metadata. F\*-implementable; the hot
   `skip_varint_hex` / `decode_varint_hex` chain is currently called per
   cell because the footer state is not cached. This is the single largest
   leverage point Codex named (#1 in his ranked list).
2. **Per-page column decode** — `Parquet.Footer.fst`. Decode an entire
   column page into an array of values once, index it by row offset. This
   is what Parquet is *for*; the current "expensive random-access string
   store" misuse is in F\* code we control.
3. **`graph_add_unchecked` + post-load canonicalise** — `RDF.Graph.Executable.fst`.
   Delta's #1 mitigation. Be aware this was previously attempted (commit
   `a5cf381`) and reverted (`bb6f9d7`) because reversed insertion order
   broke 19 rdf-xml round-trip tests. The fix is two-tier API + an explicit
   `graph_canonicalise` called once after bulk parse, **not** changing the
   default `graph_add`.
4. **Verified BTree / hash-trie graph store** — `RDF.Graph.Executable.fst`
   (or a new `RDF.Graph.Indexed.fst`). The list-of-triples representation
   is the root cause of both `mem_triple` linearity and `graph_add`
   tail-append. A verified persistent map keyed on subject (or on a
   permutation triple) drops `mem_triple` to O(log N) and removes the
   need for `graph_add_unchecked` entirely. This is the F\*-native
   answer to "why do we even need an external index format?".

Steps A.1–A.3 are days of work; A.4 is weeks but is the right long-term
home of the perf fix. None of them require a new on-disk format.

### Step B — leverage Ballyhoo HDT (already partially extracted)

`Parser.BallyhooHDT.fst` already exists — we have an in-tree columnar
RDF format with bitmap-triples + dictionary that matches QLever's logical
shape much better than Parquet does. Per memory, the current branch fixes
API shape but shells out to `hdtSearch` for the binary read (audit
2026-04-19). The F\*-first move is **finish the F\* HDT reader**, not
invent a third format. HDT already has:

- dictionary-encoded terms (matches the source doc's `terms.dict`),
- sorted permutations (matches the source doc's `spo.idx`),
- block-addressable structure,
- a published spec we can read from disk (rule #6 analogue),
- existing test fixtures.

Any argument for the source doc's "Factoidal-native permutation format"
must first explain why HDT — which already has all the properties the
doc enumerates — is insufficient. The source doc does not address this.

### Step C — only then consider a v2 format

If after Steps A and B we still need a new format, design it as a
**replacement** for COTTAS, not a sibling.

---

## 4. The three classes of "second backend" — disposition

Per the brief, distinguishing the three classes:

| Class | Description | Rule alignment | Disposition |
|-------|-------------|----------------|-------------|
| **(a) Benchmark / oracle** | Run oxigraph (or Apache Jena, or rdflib) in the test harness. Compare row-counts and wallclock against factoidal on the same query. **No OCaml/F\* linkage.** Pure subprocess + JSON diff. | Compatible with rule #6 (we already shell out to W3C reference data) and rule #1 (F\* product is unchanged). It's just a yardstick. | **Pursue.** Adds confidence to perf claims, catches semantic regressions during the BTree migration. Already half-present via `tools/corpus_pipeline.py`'s use of pyoxigraph. |
| **(b) Pre-converter** | External tool (oxigraph, rdflib, raptor) parses TriG → N-Quads or builds a COTTAS/HDT artifact offline. Factoidal only ever queries the pre-built artifact. | Compatible with rule #4 — RDF parsers belong in F\*, but **build-time** tools are explicitly out of scope of "the runtime". The pipeline is offline corpus prep, not query path. Already implemented in `tools/corpus_pipeline.py`. The source doc's "Phase 3: external Python/Rust index builder" falls in this class. | **Pursue conservatively.** Keep the dependency at the corpus-prep boundary, never in the query binary. If it ever appears in `bin/<platform>/factoidal*`, that's a violation. |
| **(c) Query-engine swap-in** | Route incoming SPARQL to oxigraph (or Jena) at query time when the local engine is "too slow". | **Direct violation of rule #1 and rule #7.** F\* is no longer the source of truth for query results; we are now an oxigraph wrapper with extra steps. KaRaMeL extraction becomes pointless (the verified core is bypassed). | **Forbid.** This is the drift the source doc's framing risks enabling. Any future PR proposing this should be closed with a pointer to this review. |

---

## 5. Concrete recommendation

**Pursue class (a) and class (b) only.** Add an oxigraph-as-oracle harness
(class a) so we can publish honest perf comparisons and catch result-set
regressions when we land Steps A.1–A.4. Keep `tools/corpus_pipeline.py` as
the pre-converter (class b) — it is already the right shape. **Do not build
"a second on-disk backend" as a separate parallel format**; instead invest
the same engineering hours in (1) Codex's footer-cache + per-page decode in
`Parquet.Footer.fst`, (2) Delta's `graph_add_unchecked` + `graph_canonicalise`
two-tier API, (3) a verified indexed-graph type in F\* that fixes
`mem_triple` at the root, and (4) finishing the F\* HDT reader, which
already gives us QLever-shape immutable permutations without inventing a
new file format. The source doc's Phases 1, 4, 5 ("make diagnosis visible",
"verified reader", "evaluator bridge") survive into this plan. Its Phases 2
and 3 ("define new file format", "external Rust/Python builder") should be
deferred until we have proven that Steps A and B are insufficient — which,
on the evidence to date, has not been shown. **Above all, do not embed
oxigraph or RocksDB as a query backend at any point**; that path ends with
factoidal's verification thesis silently dissolved.

---

## 6. Pushback the source doc needs

- **Title is wrong.** "Second backend options" invites class-(c) drift.
  Rename to "On-disk format evolution: COTTAS v2 shape".
- **Phase 3 ("external Python/Rust builder")** needs a hard scope statement:
  builder is offline, never linked into `factoidal*` binaries, never on
  `PATH` of the runtime user. Without that statement, Phase 3 reads as
  permission to ship a Rust dependency.
- **HDT is unmentioned.** A doc proposing immutable sorted permutations
  must address why `Parser.BallyhooHDT.fst` does not already cover this.
- **The Parquet diagnosis is conflated with the format choice.** Codex's
  fixes (footer cache, per-page decode) are F\*-implementable in
  `Parquet.Footer.fst` and would deliver most of the wallclock win
  without any new format. The source doc says "even with better caching,
  Parquet remains a less natural backend" — that may be true long-term,
  but it is not the right framing for the *next* commit.
- **Rule #1 is not cited anywhere.** A design doc proposing backend
  changes should explicitly affirm that SPARQL evaluation remains in
  `SPARQL11.Algebra.fst` and that no third-party query engine is being
  embedded. Silence on this is how drift starts.
