# MillenniumDB study — what factoidal can learn for its F\*-first storage / query path

**Agent:** Psi
**Date:** 2026-04-25
**Sources studied:**

- Vrgoč et al., *MillenniumDB: A Multi-modal, Multi-model Graph Database*,
  SIGMOD-Companion '24 (4-page demo paper).
  PDF: <https://aidanhogan.com/docs/millenniumdb-demo.pdf>.
  Local extracted text: `/tmp/mdb-demo-pages.txt`.
- Vrgoč et al., *MillenniumDB: An Open-Source Graph Database System*,
  Data Intelligence 5(3):560–610, 2023 (the long architecture paper, [17]
  in the demo paper's references). PDF: <https://aidanhogan.com/docs/millenniumdb.pdf>.
  Local extracted text: `/tmp/mdb-full.txt`.
- GitHub: <https://github.com/MillenniumDB/MillenniumDB> (C++, ANTLR;
  README only — wiki not crawled).

The demo paper is high-level; almost all storage/index detail in this note
comes from the Data Intelligence (DI) paper sections 3 and 5. Page numbers
below refer to the DI paper unless flagged "(demo)".

**Related local context:** `2026-04-25-second-backend-options-oxigraph-qlever.md`
(Codex), `2026-04-25-second-backend-options-review.md` (Agent Chi,
commit `baa5062`), `2026-04-25-cottas-parquet-load-path-perf.md` (Codex),
and `formal/fstar/Parser.BallyhooHDT.fst` (partial F\* HDT shape, still
shells out to `hdtSearch`). This is **information gathering only.**

---

## 1. What MillenniumDB actually is

MillenniumDB (MDB) is a multi-model graph database from PUC Chile / IMFD /
U. Chile (Hogan, Navarro, Vrgoč, Reutter, Arenas et al.). It is written
in C++ (75% of the repo per GitHub), with ANTLR for parsers, and is
**deployed in production** powering Wikidata / BibKG / TelarKG endpoints
at `mdb.imfd.cl` (demo § 3.2, page 3).

Its central design idea is the **domain graph data model** (DI § 3.1,
Definition 5, page 8):

> A domain graph G = (O, γ) consists of a finite set of objects O ⊆ Obj
> and a partial mapping γ : O → O × O × O.

i.e. **edges are first-class objects**: every edge `e` is a member of
`O` and `γ(e) = (source, type, target)`. This is structurally identical
to **RDF reification with built-in singleton edge ids** — the *eid* (the
4th component of every quad) is a primary key. This single design choice
drives almost everything about MDB's storage layout.

DI § 5 (pp. 20–24) is the only place an RDF/SPARQL implementer should
read carefully. The demo paper (SIGMOD '24) just confirms that this
2023 design is what now ships in the SIGMOD demo (demo § 2.1, page 2:
"MillenniumDB stores the graph internally as tuples of 8-byte
identifiers… we use B+ trees to store graphs.").

---

## 2. On-disk format

### 2.1 Identifiers (DI § 5, p. 20)

- **Every object — node, edge, value — is an 8-byte (64-bit) id.**
- The **first byte** is a *class tag* (named-node / anonymous-node /
  edge / inlined-value / external-value).
- **Inlined values** fit in the remaining 7 bytes (short strings,
  small ints).
- **External values** (long strings) are pointers into a single
  file: `OBJECT FILE`.

### 2.2 OBJECT FILE (DI p. 22)

> a single binary file called OBJECT FILE, which contains all such
> strings concatenated together. The internal id of an external value
> is then equal to the position where it is written in the OBJECT FILE.

- One file, append-only at load time.
- Id = byte offset in file → trivial random-access decode.
- A separate **hash table on load** maps string → id (used to dedupe and
  to translate query-time literals).
- "Only strings are currently supported, but the implementation
  interface allows for adding support for different value types in a
  relatively simple manner." — i.e. typed literal handling is *future
  work* in MDB itself. (DI p. 22)
- At server start, the OBJECT FILE *can* be loaded fully into RAM for
  fast id→string decode (DI p. 22).

### 2.3 B+ trees (DI § 5, pp. 21–22)

Everything else is **fixed-size-record B+ trees** parametrised on a
single template. Page size is **4 kB by default, parametrised** (DI p. 22):

> All of the data is stored on pages of fixed (but parametrized) size
> (currently 4kB). The data from disk is loaded into a shared main
> memory buffer, whose size can be specified upon initializing the
> MillenniumDB server. The buffer uses the standard clock page
> replacement policy.

Four relations are indexed (DI pp. 21–22):

| Relation | Tuple | Permutations indexed |
|----------|-------|---------------------|
| `OBJECTS` | `(id)` | 1 |
| `DOMAIN GRAPH` | `(source, type, target, eid)` | **4** (see below) |
| `LABELS` | `(object, label)` | 2 (both) |
| `PROPERTIES` | `(object, property, value)` | 2 (PK + property-value lookup) |
| `EDGE TABLE` | `(source, type, target)` (positional, indexed by `eid`) | 1 (array) |

**Total: ten B+ trees.** (DI p. 22.)

The four DOMAIN GRAPH permutations (DI p. 21) are:

- `source, target, type, eid`
- `target, type, source, eid`
- `type, source, target, eid`
- `type, target, source, eid`

Note: this is **NOT** the standard SPO / POS / OSP RDF triple-store
ordering. Because the *eid* is always the last position, the four
permutations cover the three "starting points" (source, target, type)
plus a `type-target-source` for the worst-case-optimal join's variable
ordering needs. There is no `source-type-target` because that is
spelled `type-source-target` with type first. The four permutations
were chosen specifically to feed the **leapfrog trie join** (LTJ)
algorithm, not "all six".

### 2.4 EDGE TABLE — a positional array (DI p. 22)

> we also store a table called EDGE TABLE, which contains triples of
> the form (source, type, target), such that the position in the table
> equals to the identifier of the object e such that γ(e) = (source,
> type, target). This implies that edge identifiers must be assigned
> consecutive ids starting from zero internally by MillenniumDB.

I.e. given `eid`, recover `(s, t, o)` in O(1). This is the *only*
non-B+-tree structure in the storage layer and it works because edge ids
are dense (0..N-1).

### 2.5 Bulk import (DI p. 22)

> All the B+ trees are created through a bulk-import phase, which loads
> multiple tuples of sorted data, rather than inserting records one by
> one.

So MDB has the same offline-immutable shape as QLever / HDT for the
build step, even though the runtime allows online updates via the
buffer manager. The DI paper does not describe the update path in
detail.

### 2.6 Storage cost (DI Table 3, p. 25)

On the Wikidata Truthy dump (≈ 1.25 B triples):

| Engine | Disk |
|--------|------|
| MillenniumDB | **203 GB** |
| Jena LF (six perms) | 195 GB |
| Jena TDB (default) | 110 GB |
| Neo4j | 112 GB |
| Blazegraph | 70 GB |
| Virtuoso | 70 GB |

MDB is the largest by ~3× the smallest. The DI paper attributes this
explicitly to the four permutations needed for LTJ (DI p. 25).

---

## 3. Named graphs / N-Quads — the surprising answer

**MDB does NOT support N-Quads as a storage class.** Quoting DI §3.2
(p. 10):

> Named graphs could be supported in domain graphs using a reserved
> term `graph`, and edges of the form `γ(e3) = (e1, graph, g1),
> γ(e4) = (e2, graph, g1)`; **optionally, named domain graphs could be
> considered in the future to support multiple domain graphs.**

I.e. the *eid* slot in MDB is **already used** as the singleton-named-graph
id in spirit. Every quad has a unique edge id; multiple top-level named
graphs are not modelled. The DI paper notes (p. 10) that this is a
deliberate trade-off:

> Comparing RDF datasets and domain graphs, the latter sacrifices the
> "Graph as node" feature without reserved vocabulary to **reduce
> indexing permutations** (discussed in Section 5).

DI Table 1 (p. 11) is explicit: domain graphs do **NOT** support
"Graph as node". MDB picks "edge ids as quad ids" over "named graphs as
first-class".

For SPARQL 1.1 (which MDB serves at wikidata.imfd.cl per demo § 3.2),
this means the engine treats Wikidata as a single graph; named-graph
SPARQL features (`FROM NAMED`, `GRAPH ?g`) are evidently not the engine's
sweet spot. The demo paper does not say what MDB does here, but DI § 3.2
(p. 9, footnote 7) admits SPARQL "does not support querying paths that
span different named graphs", which is consistent with MDB choosing not
to model them.

**This is a sharp contrast with how factoidal has been thinking about
its on-disk format**: the Codex second-backend doc proposes 9
permutations including separate `gspo`, `gpos`, `gosp`. MDB's authors
deliberately did not.

---

## 4. Loading model — paged, NOT all-in-memory

DI § 5 is unambiguous (p. 22):

> All of the stored relations are accessed through linear iterators
> which provide access to one tuple at a time. All of the data is
> stored on pages of fixed (but parametrized) size (currently 4kB).
> The data from disk is loaded into a shared main memory buffer, whose
> size can be specified upon initializing the MillenniumDB server. The
> buffer uses the standard clock page replacement policy [32].

Concretely:

- 4 kB pages in B+ trees.
- A single shared **buffer pool** with **clock replacement**.
- **Linear iterators** are the unit of access — one tuple at a time,
  pages faulted in lazily.
- OBJECT FILE *can* be optionally fully RAM-resident at server start
  for fast id→string decode (DI p. 22).

This is precisely the operating mode that **factoidal does NOT have**
today (see `docs/designissues/2026-04-25-cottas-parquet-load-path-perf.md`):
our COTTAS path materialises all 3.14 M quads up-front before any query
runs. MDB on the same scale (Wikidata, 1000× larger) doesn't materialise
anything — pages fault in as the iterator scans them.

---

## 5. Property paths / 2RPQ evaluation (DI § 5, pp. 23–24)

The "M&M" of "MillenniumDB" is path queries. The algorithm is:

1. **Compile the regular path expression to a finite automaton.**
2. **Build a virtual product** of the automaton × the graph
   on-the-fly.
3. **BFS-traverse** the product, emitting solutions when an accept
   state is reached.
4. Optionally DFS variant for benchmarking (DI § 6).
5. Returning *one* shortest path "comes almost for free" using BFS
   bookkeeping (DI p. 24).
6. Returning *all* shortest paths needs a predecessor-list per node.

Critically (DI p. 24):

> The implemented algorithm only requires **two permutations** of the
> DOMAIN-GRAPH relation: one for retrieving all of a node's successors
> via an edge of a specified type; and another for retrieving all such
> predecessors of a given node.

I.e. **path queries do not need all four permutations.** Two are
enough. The other two are for LTJ over BGPs only.

Path patterns are pushed to the **end** of the join plan and joined
nested-loop with the rest, because they are not directly indexed
(DI p. 22, footnote 7). The authors call this "not the best option…
but adequate in practice".

---

## 6. Worst-case-optimal joins (DI § 5, pp. 23)

MDB uses **leapfrog trie join (LTJ)** — Veldhuizen 2014 [48 in DI refs]
— wherever the variable order can be supported by the four DOMAIN-GRAPH
permutations. Otherwise it falls back to:

- Selinger-style dynamic-programming optimiser, or
- a greedy planner [16] for very large joins.

The variable-order heuristic mixes greedy + GYO reduction (DI p. 23).

**Why this matters for factoidal:** LTJ is what makes MDB's four
permutations *worth their disk cost*. If we don't implement LTJ, having
many permutations buys far less. Plain hash-/merge-join only needs one
or two permutations per access pattern. **A Codex-style 9-permutation
backend without LTJ would be all cost, no benefit.**

---

## 7. Comparison with HDT

**HDT is not mentioned anywhere in the DI paper or demo paper.** I
grepped both extracted texts; neither cites HDT, Fernández, "Header
Dictionary Triples", or compressed RDF. This is striking given Hogan's
co-authorship on adjacent compressed-RDF work.

The probable reason: HDT is **read-only**, dictionary-encoded, and
optimised for **compression + scan**. MDB needs **random page-level
read/write** for buffer-pool semantics and for incremental updates
(even if the demo paper doesn't dwell on updates, the architecture
clearly assumes them — clock replacement only matters if pages are
dirty-able). The two systems sit at opposite ends:

| | HDT | MillenniumDB |
|---|---|---|
| Mutability | immutable snapshot | online, page-level |
| Encoding | bitmap-triples + compressed dict | 8-byte ids + B+ trees |
| Indexes shipped | 1 (SPO via bitmap), more derivable | 4 perms × DOMAIN GRAPH + others |
| Quad / named graph | no (HDT-MR / multi-file required) | no (eid is the quad id) |
| Loading | full RAM-load typical (or mmap) | paged via buffer pool |
| Compression | strong (Huffman + Front-Coding) | none (plain id arrays) |
| Query algo | SPO-based scans | LTJ + Selinger + greedy |
| Path queries | not its thing | first-class (BFS over automaton-graph product) |

So the right framing is: **MDB is to property-graphs-with-SPARQL what
QLever is to pure RDF-SPARQL** — both are page-paged, B+-tree- /
sorted-relation-based, deliberately uncompressed, designed for
LTJ-style scans.

**HDT and MDB are not substitutes.** HDT is an interchange/snapshot
format. MDB is a runtime engine.

---

## 8. Comparison with factoidal's current state

### 8.1 vs. COTTAS/Parquet (current verified path)

| | COTTAS today | MDB |
|---|---|---|
| File format | Parquet (single 4-col table) | proprietary B+ tree files + OBJECT FILE |
| Encoding | dictionary-encoded byte strings (delta-length-byte-array) | 8-byte fixed-id, class-tagged |
| Loading | **eager full materialisation** before query | **paged via buffer pool**, lazy |
| Random access | per-cell footer probe (~12 M for COUNT(\*)) | O(1) via b-tree + EDGE TABLE |
| Indexed for SPARQL? | no — list-of-quads at runtime | yes — 10 B+ trees |

The Codex perf doc (`2026-04-25-cottas-parquet-load-path-perf.md`)
diagnosed that we are using Parquet as a "random-access string store".
**MDB is what Parquet-as-random-access-string-store would look like if
done deliberately**: fixed-size records, page-faulting buffer pool,
one binary OBJECT FILE for the strings, and no Parquet at all.

### 8.2 vs. HDT (`Parser.BallyhooHDT.fst`, partial)

`Parser.BallyhooHDT.fst` already encodes:

- 6-permutation enum `BO_SPO | BO_SOP | BO_PSO | BO_POS | BO_OSP |
  BO_OPS` (more than MDB ships, less than Codex's proposal).
- An opaque `hdt_handle` and `hdt_term_ref = nat`.
- A bound triple-pattern access type `hdt_bound_tp`.
- Per memory note (2026-04-19): the actual binary read is shelled out
  to `hdtSearch`, not in F\*.

MDB suggests **two simplifications** for our HDT path:

1. **Drop SOP/PSO/OPS** (3 of the 6 enum cases). MDB ships 4 perms
   for LTJ; without LTJ, 2 perms (one starting with subject, one with
   object) cover all bound-pattern access. Per DI p. 24: even path
   queries only need 2 perms.
2. **Fix-size everything as 8-byte ids before joins start.** HDT
   already encodes terms as ids (per HDT spec); the F\* port should
   commit to that representation end-to-end, not convert back to
   RDF terms in the middle of a scan.

### 8.3 What MDB does NOT have that we should keep

- **Verified parsers** in F\* (rule #4). MDB uses ANTLR.
- **N-Quads / multiple named graphs** as a first-class concept. MDB
  explicitly trades this away (DI Table 1, p. 11). Factoidal already
  has a multi-graph TriG demo and the lifesci browser page; we should
  not regress on this for storage-layer reasons.
- **Verification.** All of MDB is plain C++ — no formal model.

---

## 9. What to copy / not copy / extend

### 9.1 COPY (high-leverage, low-risk for an F\*-first project)

1. **8-byte fixed-size, class-tagged ids.** First byte tags the
   class (named-IRI / blank / inlined-literal / external-literal).
   7 bytes for inlined values fits short literals trivially. F\* has
   `UInt64.t`; encoding/decoding is straightforward and easily
   verified.
2. **Single OBJECT FILE for external strings, id = byte offset.**
   This is the simplest external-dictionary scheme that exists. No
   bitmap, no Huffman, no Front-Coding. Strict O(1) decode. Verified
   reader is a one-page F\* function.
3. **EDGE TABLE = positional array indexed by eid.** If we ever
   model quads with first-class quad ids, this is the pattern to
   use. Pure F\* `seq nat`.
4. **4 kB B+ tree pages, parametrised.** This is the standard from
   Knuth onward; no reason to invent.
5. **Bulk-import-only first**, online update later. Matches our
   COTTAS / HDT shape.

### 9.2 DO NOT COPY

1. **The domain-graph data model.** Our north star is RDF/SPARQL 1.1
   (rule #5). Domain graphs subsume RDF only via an artificial eid
   per triple, and MDB drops named-graph support (DI Table 1, p. 11) —
   a regression we can't accept.
2. **Four permutations *without* LTJ.** Disk cost is ~3× single-SPO
   (DI Table 3, p. 25 — 203 GB vs. 70 GB), pays back only with LTJ.
   LTJ in F\* is multi-week work, not on the critical path.
3. **C++ codebase / ANTLR parsers** — rules #1 + #4.
4. **MDB's binary file format.** Per Agent Chi's review: we don't
   target binary compatibility with *any* third-party engine. Copy
   patterns, not byte layouts.
5. **Mutable buffer-pool semantics.** Clock replacement + updates is
   much harder to verify than a read-only mmap reader.

### 9.3 EXTEND (in our HDT path, before any new format)

1. **Trim `Parser.BallyhooHDT.fst`'s permutation enum from 6 to
   2 or 3.** MDB's 4-for-LTJ vs. the path-query 2-for-BFS argument
   (DI p. 24) is the precedent. We don't need 6.
2. **Add an `object_file` byte-offset model to the HDT artefact
   summary.** The HDT spec already has dictionary sections — we can
   model them in F\* as `seq byte` with offset-keyed access without
   changing the binary format on disk.
3. **Implement page-paged scan iterators in F\***, even if backed by
   `mmap` from the OCaml/C glue. The verified surface is the
   `next : iterator -> option row` — exactly the "linear iterator"
   pattern MDB describes (DI p. 22). This is the single largest
   architectural shift and it lets us **stop materialising whole
   datasets eagerly** without designing a new file format.
4. **Optional in-RAM dictionary** at runtime, mirroring MDB's
   "OBJECT FILE in RAM" toggle (DI p. 22). Cheap and immediately
   useful for benchmarks.

---

## 10. Reconciling with the existing second-backend discussion

The Codex doc (`2026-04-25-second-backend-options-oxigraph-qlever.md`)
proposes a Factoidal-native immutable permutation backend with up to
9 permutations. Agent Chi's review (`2026-04-25-second-backend-options-review.md`)
correctly pushes back on the title and on adding a parallel format.

This MDB study points the same way as Chi's review, but with a
specific empirical anchor: **MDB, the most-cited modern engine that
combines RDF and property-graph storage, ships *four* permutations
(not six, not nine), and only needs *two* for path queries.** The 4
perms are not sufficient to ship N-Quads — MDB knowingly drops them
(DI p. 10).

So the answer to "should we ship 3, 6, or 9 perms?" looks like:
**ship 1–2 first, in the existing HDT path, as MDB ships 2 for path
queries.** Add more only if LTJ becomes a goal — and LTJ is not on
the critical path today.

The MDB paper also confirms Chi's class-(c) "do not embed an external
engine" position by *omission*: MDB itself is what we'd be embedding
if we went down that road. It's a 60k-line C++ codebase. The
factoidal architectural distinctive — verification — is the *opposite*
of what MDB offers.

---

## 11. What to do next (5 bullets)

1. **Cite this doc in any future "second backend" discussion.** MDB
   ships 4 perms (DI p. 21), needs only 2 for path queries (DI p. 24),
   and explicitly drops named graphs (DI Table 1, p. 11). These are
   the empirical anchors — not "pick a number between 3 and 9".

2. **In `Parser.BallyhooHDT.fst`, decide whether to trim the 6-perm
   enum to 2–3.** Add a comment block citing MDB's 2-perm path-query
   result. Out of scope here — flag for the HDT-finishing work item.

3. **Run a small experiment: `OBJECT_FILE`-style verified reader.**
   Write an F\* function `read_string_at : seq byte -> nat -> option
   string` decoding a length-prefixed string at a given byte offset.
   Verify it. Smallest piece of MDB's storage layer that maps cleanly
   into "F\* is the source of truth" — replaces COTTAS's per-cell
   footer probing for string lookups specifically. (B+ tree side is
   much harder — leave for later.)

4. **Refute the "9-perm second backend" framing.** The highest-
   performing modern open-source engine that does *both* property-graph
   and RDF ships 4 perms, not 9, and trades quads away to keep the
   number low. Retire the 9-perm sketch unless someone volunteers to
   also implement LTJ in F\*.

5. **File the buffer-pool / page-paged iterator pattern as a
   factoidal issue.** A `next : iter -> option row` interface with
   lazy page faulting fixes the COTTAS eager-materialisation perf bug
   without touching the file format. File under "graph store
   interface", not "second backend".

---

**Bottom line.** The most useful single idea in MDB is **not** the
four permutations (don't copy without LTJ); it is the **paged
buffer-pool + linear-iterator + 8-byte-id + single OBJECT FILE for
external strings** combination. That gets us out of the eager-
materialisation hole without adopting a new on-disk format and
without violating any iron rule. MDB also serves as an empirical
ceiling on "how few permutations is enough" (2 for paths, 4 for LTJ,
**never** 9 in any shipped engine the paper cites).
