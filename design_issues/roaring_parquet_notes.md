# Roaring, COTTAS, Parquet, and ID encoding — design notes

Status: **exploration / option-mapping**. Nothing here is decided.
The point of this document is to capture the design space deliberately
so we don't lock in the wrong thing under pressure. Several earlier
drafts of this thinking over-committed and were corrected; the
revisions are recorded in §15.

Date: 2026-05-06.

Working branch: `claude/fstar-roaring-bitmap-D3f23`.

Companion artefacts:
- `experimental/roaring-fstar/README.md` — Roaring paper summary +
  Rust crate API + an initial F\* layering sketch.
- `experimental/roaring-fstar/paper/roaring.{pdf,txt}` — full text of
  the Lemire/Ssi-Yan-Kai/Kaser arXiv:1603.06549.

> **Note on path.** This file is at `design_issues/` per explicit
> request. The repo's existing convention is `docs/designissues/` with
> a `YYYY-MM-DD-` filename prefix. Either rename / move later or
> normalise the convention; not addressed here.

---

## 1. Why this document exists

A genuine design tension came up while scoping a possible F\* port of
Roaring bitmaps:

- Our existing on-disk story (COTTAS-on-Parquet) is row-grouped and
  shaped like analytical OLAP storage.
- Our possible future is a hybrid DB / search engine, where storage
  may not be Parquet, and indexes (especially posting lists) may want
  to span the whole corpus rather than be per-block.
- ID-width choices (32-bit vs 64-bit, sorted-position vs tagged) have
  long half-lives and are coupled to format choices, indexing
  choices, virtual-named-graph features, and the Roaring vs
  Roaring64 question.

The risk profile is asymmetric: a wrong choice on ID width or
posting-list universe is painful to undo (every persisted file would
need re-encoding); a wrong choice on container internals is cheap to
revisit. So this note is primarily about the choices in the first
category.

## 2. Scope

In scope:
- What Roaring is, what it gives us, what it costs to verify.
- Where Roaring could plug into the existing F\* + COTTAS + Parquet
  + SPARQL stack.
- ID-width choices and their interaction with virtual named graphs,
  search-engine-style global posting lists, and Roaring64 format
  fragmentation.
- The community/process angle (transparent, observable, testable
  format work).

Out of scope:
- Picking a winner among the alternatives.
- Implementation sequencing.
- Performance numbers on our actual workloads (not measured yet).

---

## 3. Background: what Roaring is (paper)

Full summary in `experimental/roaring-fstar/README.md`. Compressed
recap of the load-bearing facts:

### 3.1 Structure

Roaring is a compressed `Set u32`. The 32-bit integer splits into a
high-16 *key* (which 65 536-element chunk) and a low-16 *position*
within the chunk. The top level is a sorted `(key, container)` array,
binary-searched. Each container holds the low-16s of one chunk in one
of three formats:

| Container | Wire layout | Best when | Serialized size |
|---|---|---|---|
| Array | sorted `u16[]`, distinct, ≤ 4096 | sparse | `2 + 2c` bytes |
| Bitmap | `u64[1024]` (8 KiB, 2¹⁶ bits) | medium / dense | always 8192 bytes |
| Run | sorted `(u16 start, u16 length-1)` pairs | long compressible runs | `2 + 4r` bytes |

Conversion rules:

- Array ↔ Bitmap at cardinality 4096.
- Run only if it strictly beats both: needs `r ≤ 2047` when card > 4096,
  or `r < c/2` when card ≤ 4096.

Containers fit in L1 cache by construction; that's most of the speed
story.

### 3.2 Set-algebra (six interesting cases)

Each binary op (AND, OR, XOR, ANDNOT) has six per-pair routines:
`(array, array)`, `(array, bitmap)`, `(bitmap, bitmap)`, `(run, run)`,
`(run, array)`, `(run, bitmap)`. Output type is *predicted* up front
to avoid post-hoc conversion. Special-case: a run container holding
the single run `[0, 2¹⁶)` short-circuits union with anything to a
clone.

### 3.3 Three named algorithms (the F\* port targets)

The paper formalises three by name; everything else is prose.

- **Algorithm 1 — count runs in a bitmap.** Per word `Cᵢ`,
  `bitCount((Cᵢ << 1) ANDNOT Cᵢ)` plus a cross-word correction. Can
  short-circuit at 2047 (anything more disqualifies run conversion).
- **Algorithm 2 — extract runs from a bitmap.** Uses `tzcnt` of the
  word for run starts and `tzcnt(¬word)` for run ends.
- **Algorithm 3 — set/clear a range of bits in a bitmap.** Mask-based
  inner loop; same code parameterised by OR (set) or ANDNOT (clear).

### 3.4 Lazy union

For k-ary unions, defer cardinality computation; mark unknown bitmap
cardinalities with sentinel `-1`; do a single repair pass at the end.
Naive 2-by-2 vs heap-based aggregation: neither dominates (paper
Tables IIId–e, IVd–e). Naive wins on dense/unsorted; heap on
sparse/sorted; reference implementation defaults to naive.

### 3.5 Performance vs WAH/Concise/EWAH (paper §6)

Reading from Tables III, IV (Roaring+Run = 1.0):

- Random access: 870× faster than WAH/Concise in the worst case.
- Successive intersections: 3.5× to 460× faster than Concise.
- K-ary unions: 1.7× to 210× faster than Concise.
- Compression: near-best in every category. The only loss is
  CensusInc-sorted (Concise wins by 8%); even there Roaring+Run is
  6–8× faster.

### 3.6 Future-work flags from the paper

- Copy-on-write containers during unions.
- Container-level parallelism + SIMD (CRoaring 2.x has done this on
  x86-AVX-512 and ARM Neon since publication).
- **Lucene's "negated array container"** as a fourth container type.
  Relevant for us: files emitted by Lucene may include this variant,
  affecting on-disk format compatibility if we ever interop.

---

## 4. The Rust roaring crate — quick API surface

`docs.rs/roaring`:

- Two public types: `RoaringBitmap` (set of u32) and `RoaringTreemap`
  (set of u64, implemented as `BTreeMap<u32, RoaringBitmap>`).
- Standard Rust `BitOr / BitAnd / BitXor / Sub` and `*Assign` forms,
  range methods (`insert_range`, `remove_range`, `range`,
  `contains_range`), iteration, `select`, `rank`.
- `MultiOps` trait for k-ary union/intersection over iterators.
- `serialize_into` / `deserialize_from` use the official Roaring
  portable format, so files round-trip with the C/Java/Go impls.
- Optional `serde`, `bytemuck`, gated nightly `simd` feature
  (untested per the README).

If we did extract OCaml from F\* and wanted cross-impl conformance,
the Rust crate is one of the canonical reference implementations to
test against.

---

## 5. Where this sits in the existing codebase

### 5.1 What's already there

A non-trivial amount of bitmap-shaped infrastructure exists:

- **`RDF.CottasStore.PresenceBitmap.fst`** — F\* read API for a
  *dense* per-rg × per-token bit matrix companion file (`.presence`,
  magic `COTP`). Row-major bit `(rg * num_tokens + tok)` says "row
  group `rg` contains a row whose token id is `tok`." This is a
  coarse-grained pruning bitmap — answers "could this row group have
  a match?" — not a posting list.
- **`RDF.CottasStore.CompoundPresenceBitmap.fst`** — same shape lifted
  to (S,P), (P,O), (S,O) pairs. Quadratic-ish in token count.
- **`RDF.CottasStore.OnDiskIndex.fst`** — the companion-file format
  spec for the above, plus the dictionary companion (`.dict`, magic
  `COTD`) used for term ↔ id translation.
- **`RDF.CottasStore.fst`** + **`RDF.CottasInMem.fst`** — query-time
  interface; in-memory variant.
- **`Parser.BallyhooCOTTAS.fst`** — F\* model of the COTTAS columnar
  quad backend.
- **`97_indexed_graph_store.sh`** — *post-extraction OCaml patch*
  that installs `Hashtbl<string, triple list>` S/P/O indexes per
  in-memory `rdf_graph`. Flagged in
  `docs/designissues/2026-04-24-indexing-audit.md` as a candidate to
  promote into F\* (rule #11ish — semantic logic in OCaml).

### 5.2 What's *not* there

- Any row-level posting structure (`term-id → set of rowIDs`).
- Any compressed-bitmap library (Roaring or otherwise).
- Any global term-ID space — IDs today are local to a graph or to a
  COTTAS file's column dictionary.
- Any virtual-named-graph mechanism.

### 5.3 What COTTAS specifically gives us — being honest

When pushed on the question "what does COTTAS actually give us?", an
honest accounting:

| Comes from Parquet, not COTTAS | What COTTAS adds on top |
|---|---|
| Columnar layout, dictionary encoding, DLBA, page-level RLE | The 4-column schema convention (S/P/O/G as ints) |
| Memory-mapped reads, HTTP-range over the wire | `.dict` + `.presence` companion sidecars |
| Mature reader ecosystem (DuckDB / Spark / Arrow / Polars / Iceberg) | F\*-verified read path |
| Compression on disk | Naming/format convention so anyone can identify "this is RDF-as-Parquet" |

So COTTAS-the-format is essentially **"a Parquet file with this
specific 4-column schema, plus companion sidecars for fast term-id
↔ string and per-rowgroup token presence."** Most of the value is
Parquet doing the work; COTTAS is a thin RDF-shaped wrapper.

The original motivation for COTTAS over HDT was specifically that
**HDT does not natively handle quads / named graphs** (HDT-Q variants
exist but are less mature). That holds. COTTAS is "the smallest
RDF-shaped wrapper on Parquet that lets us claim a portable,
ecosystem-friendly on-disk format without inventing one from
scratch." That's its job; expecting more is mis-framing.

### 5.4 Implication for storage independence

Since most of the benefit is Parquet's, the question of "what if we
move off Parquet" is a real one. A hybrid DB / search-engine
direction may want:
- Tantivy/Lucene-shaped segment storage (immutable segments, merged
  in the background).
- Lance/Vortex (columnar, but optimised for ML/search rather than
  OLAP).
- Custom on-disk format where we control every byte.
- In-memory only (no on-disk format at all for some tiers).

**COTTAS is portable in the sense that we own the schema-and-sidecars
convention; the underlying Parquet is replaceable.** Roaring sidecars
would be similarly substrate-neutral as long as they use the
Roaring portable format. This is one of the arguments *for* Roaring:
it keeps the index layer decoupled from the storage substrate.

---

## 6. Where Roaring could plug in — five candidate placements

Listed without ranking. Each is independently evaluable; we don't
have to do all of them, and we shouldn't conflate them.

### 6.1 Replacement for the dense `.presence` sidecar

Today: `.presence` is a flat bit-matrix `num_rgs × num_tokens` bits.
For Wikidata-scale dictionaries this is enormous and mostly empty
for rare tokens.

Roaring version: per token, a Roaring bitmap over rg-IDs. For sparse
tokens (most of them), array containers; for `rdf:type` and other
hot tokens, run containers (long stretches of consecutive rgs).

**Smallest blast radius of all the candidates.** Same module, same
denotation, just a representation swap. F\* verification scope is
limited to "this Roaring-encoded file decodes to the same bitset as
the dense version did." Could be done with no change to the SPARQL
evaluator at all.

### 6.2 New row-level posting layer

The thing this whole conversation started about. Per column (S, P,
O, G), per term-id, a Roaring bitmap of rowIDs:

```
.posting per column:
  s_idx : term_id  ->  roaring(rowID)
  p_idx : term_id  ->  roaring(rowID)
  o_idx : term_id  ->  roaring(rowID)
  g_idx : term_id  ->  roaring(rowID)
```

BGP triple-pattern eval becomes a 1-to-4-way Roaring intersection.
Replaces the linear bucket-filter logic in patch #97. Also gives
exact-not-estimated cardinality bounds for query planning
(`min(|s_idx[s]|, |p_idx[p]|, |o_idx[o]|)`).

This is where the **universe-size** question lives — see §7.

### 6.3 Replacement for in-memory hashtable indexes

Patch #97's `Hashtbl<string, triple list>` becomes
`Hashtbl<term_id, RoaringBitmap>` (with rowIDs as positions in the
underlying triple sequence). Retires the rule-#11 patch; brings the
index into the verified F\* surface.

Depends on §6.2 in shape but doesn't strictly require on-disk persistence.

### 6.4 Virtual named graph membership

If virtual NGs are first-class (§9), each one is a *set of physical
graph-IDs*. That's a Roaring bitmap by construction. Whether 32-bit
or 64-bit depends on graph-ID space (§7, §9).

### 6.5 Result-set caching for SERVICE / federation

Cached SPARQL results from federated endpoints. A cached result is a
solution sequence; if represented as a row-set bitmap (over our local
row IDs) plus the projection, intersection-style join becomes free.
Less developed; mentioned for completeness.

---

## 7. The 32-bit vs 64-bit question

This is where the previous draft over-committed and got correctly
called out. The recovered framing:

### 7.1 Two distinct "ID width" questions

1. **Posting-list universe.** What's the universe of values the
   bitmap holds? For row-level posting lists (§6.2), this is
   "number of rows." For graph-membership bitmaps (§6.4), this is
   "number of physical graphs."
2. **Term-ID width.** What integer identifies an IRI/literal/blank
   node? Used as the *key* of an index, not as bitmap contents.

These are orthogonal. Conflating them produces confused conclusions.

### 7.2 Two arguments for 32-bit-with-sharding (the case I previously over-pushed)

- Parquet is row-grouped. If posting lists are per-row-group, the
  universe is "row index within this rg," typically much less than 1M.
- Cross-row-group queries iterate row-groups; per-rg bitmaps are
  always 32-bit-fits.
- Avoids the Roaring64 format zoo (Java's `Roaring64NavigableMap`,
  CRoaring's ART-based `roaring64.h`, Rust's `RoaringTreemap` — all
  incompatible on the wire).
- Verification scope stays at the single well-defined 32-bit
  portable format.

### 7.3 Why this argument was wrong to lock in

It assumed:
- Storage stays row-grouped *forever* (Parquet or Parquet-shaped).
- Posting universes are storage-block-local *forever* (no global
  posting structures).
- Term-IDs don't escape the corpus (no federation, no cross-corpus
  result caching, no global entity IDs).

A hybrid DB / search engine pushes against all three. Search engines
historically have *global* posting structures (inverted indexes
spanning the whole corpus, segment-merged in the background) — that
shape has 30+ years of accumulated wisdom and we shouldn't preclude
it casually.

### 7.4 The argument *for* engaging with 64-bit

- **QLever's encoding trick.** QLever (Bast et al.) achieves
  Wikidata-scale SPARQL speed with 64-bit term-IDs that pack a *type
  tag* in the high bits and either an inline value or a typed
  dictionary reference in the low bits. Range filters
  (`FILTER(?x > 1000)`), ORDER BY, equality on common datatypes all
  run on the integer comparisons directly — no dictionary decode.
  That's most of where their speed reputation comes from. **This
  benefit is independent of Roaring.**
- **Bitfield room for graph-ID structure.** Tagged graph-IDs that
  encode prefix-family, suffix-family, and a unique-within counter
  (§9) need ~32 bits of structure before you spend any bits on the
  unique ID. 32-bit total is too cramped; 64-bit is comfortable.
- **Sparse ID allocation with reserved gaps.** First-class virtual
  NGs and federation want to leave room in the ID space for
  unforeseen structure. 64-bit affords this.
- **Roaring64 over graph-IDs as the natural representation of virtual
  NG membership.** With tagged 64-bit IDs whose high bits carry
  prefix-family, the membership bitmap of "all graphs with prefix P"
  is naturally clustered in the high-prefix; Roaring64's branch-by-
  high-bits structure aligns with the data structure rather than
  fighting it. Run containers in the relevant chunks become the
  common case.

### 7.5 The Roaring64 format problem (real, not a reason to refuse)

The 64-bit Roaring format is fragmented:

- Java `Roaring64NavigableMap` — `TreeMap<Integer, RoaringBitmap>`
  semantics.
- Java `Roaring64Bitmap` — newer, ART-based.
- CRoaring `roaring64.h` — ART-based, performant. Iceberg picked
  this for some uses.
- Rust `RoaringTreemap` — `BTreeMap<u32, RoaringBitmap>`.

No single "the" format with universal adoption. This is a real cost
to engaging with 64-bit Roaring; not a reason to avoid the *design
space*. If we adopt 64-bit, we'd need to pick one flavour, document
the choice, and maintain conformance against it.

### 7.6 Things that are still open under this question

- Are posting-list universes per-row-group, per-segment, per-corpus,
  or global?
- Does that choice need to be the *same* for every kind of index
  (S/P/O/G posting, virtual-NG membership, federated result-set
  cache)? Plausibly not.
- If we adopt 64-bit term-IDs, do we *also* need 64-bit Roaring, or
  is term-ID width independent from posting-list-contents width?
  (Probably independent for row-posting; coupled for graph-membership
  bitmaps.)
- If we adopt Roaring64, which flavour, and how do we test
  conformance against the upstream we picked?

---

## 8. QLever-style term-ID encoding (independent of Roaring)

Worth pulling out as its own section because it's separable.

### 8.1 The technique

64-bit term-ID = high-bits type tag + low-bits payload.

- High bits identify the type: IRI, blank node, plain literal,
  language-tagged literal, `xsd:integer`, `xsd:decimal`, `xsd:double`,
  `xsd:date`, `xsd:dateTime`, `xsd:boolean`, …
- For values that fit, the payload *is the value*. E.g. small
  integers are stored as integers; dates are stored as days-since-
  epoch; booleans as a single bit. No dictionary lookup.
- For values that don't fit (long strings, IRIs, big integers), the
  payload is a typed dictionary reference. The type tag determines
  which dictionary.

### 8.2 What it buys us

- **Filter pushdown without decode.** `FILTER(?x > 1000)` on
  integer-tagged IDs is an integer comparison.
- **ORDER BY without decode.** Order-preserving encoding per type
  means SPARQL `ORDER BY` runs on the IDs.
- **Cheap type filtering.** "Only IRIs" is a tag-mask test.
- **Better dictionary footprint.** Common literals (small ints, dates,
  booleans) skip the dictionary entirely. Dictionary holds only the
  tail of long literals.
- **F\* refinement-typed sum-of-tags is exactly the kind of thing
  F\* is good at.** Tag invariants and order-preservation lemmas
  (`encode_lt: x < y ==> encode x < encode y` per type) are bounded,
  mechanical proofs.

### 8.3 What it costs

- Designing the tag scheme is a real upfront commitment. We'd want
  it stable across our ecosystem (browser/wasm/native) and likely
  Wikidata-compatible if we ever want to interop with their dumps.
- Order-preserving encodings exist for most XSD types but require
  care for edge cases (negative integers two's-complement vs
  sign-magnitude, IEEE 754 doubles, normalised vs canonical decimal).
- Dictionary becomes typed (one dict per long-tag), not a single flat
  dict.

### 8.4 What it does *not* depend on

- Roaring, of any width.
- COTTAS, Parquet, or any storage substrate.
- Whether we go 32-bit or 64-bit on Roaring posting universes.

This is genuinely orthogonal and can be discussed/implemented/
verified independently. The interaction with Roaring is only:

- If we're keeping `term-id → roaring(...)` indexes, the *keys* are
  64-bit term-IDs; the bitmap *contents* are still rowIDs (whose
  universe is whatever we pick in §7).

### 8.5 What QLever doesn't use

Worth explicit mention because it changes strategy: **QLever doesn't
use Roaring or anything like it.** Their indexes are sorted permutation
tables — packed (s, p, o)-id triples in sort order, with prefix/gap
compression, six (or fewer, derived) permutations. BGP joins are
sort-merge-joins.

| | Sorted permutation tables (QLever) | Roaring posting lists |
|---|---|---|
| Range queries on a column | Excellent (it's sorted) | OK (need decode + check) |
| BGP join via merge | Excellent — already sorted | N/A |
| BGP join via intersection | N/A | Excellent (`O(min)`) |
| Sparse term posting lists | Pays full per-triple bytes | Wins big (array/run) |
| Updates / streaming inserts | Painful (resort) | Cheap |
| Cross-impl interop | DIY format | Roaring portable spec |
| "Active set of rows" as first-class | Must materialise as list | Native |
| Deletion vectors / tombstones | Side structure | Native |

Roaring-vs-permutation-tables is itself a design choice we haven't
made.

---

## 9. Virtual named graphs by URI shape

Brought up as a real design pressure: the system may want to expose
"all graphs whose URI matches prefix P and/or suffix S" as a single
virtual NG that SPARQL can query.

### 9.1 Use cases

- **Temporal partitioning.** `https://acme.com/data/2024-01-01`,
  `.../2024-01-02`, … — shared prefix, varying suffix. Virtual NG =
  "January 2024."
- **Per-entity graphs.** `urn:wikidata:Q42`, `urn:wikidata:Q123`, …
  — entity-per-graph. Virtual NG = "all entities."
- **Per-tenant per-day.** `https://acme.com/tenant/foo/day/2024-01-01`
  — both prefix (tenant) and suffix (day) varying *independently*.
  Virtual NG = "all of foo's data" *or* "all of January 1st across
  tenants" *or* the intersection.
- **Per-source mirrors.** `http://dbpedia.org/data/Berlin`,
  `http://yago.org/data/Berlin` — same suffix across different
  prefixes (federated provenance).

The fourth case is decisive: **prefix and suffix are independent
dimensions.** Virtual NG selection is a 2-D query over named graphs.

### 9.2 Three structural choices for graph-IRI IDs

**A. Sorted-position IDs.** ID = sort-position of IRI string. Prefix
queries become a contiguous range; suffix queries don't help. Cheap
to build; helps one direction.

**B. Tagged tuple IDs.**

```
64-bit graph-id = | prefix_family : 16 | suffix_family : 16 | unique_within : 32 |
```

Both "all graphs with prefix P" (mask high 16) and "all graphs with
suffix S" (mask middle 16) become bitfield equality tests. **32-bit
forces choosing one dimension or cramping every dimension.** This is
the case where 64-bit isn't a luxury, it's structural.

**C. Hierarchical (Dewey-style) IDs.** Allocate ID *ranges* per
prefix-family with gaps for growth. Less expressive than B but easier
to keep sort-order-correct. Combine with a parallel
reverse-IRI-keyed ID space for suffix queries.

### 9.3 Prefix vs suffix asymmetry

Strings sort prefix-first. Plain sort or trie on graph-IRIs makes
prefix queries cheap and suffix queries linear. Standard fix:
maintain a parallel reverse-string index. In ID space this means
either two parallel ID assignments (with translation) *or* a tagged
tuple encoding (option B) where the families are pre-extracted so
the strings only need to sort by `unique_within`.

### 9.4 Where 64-bit specifically helps virtual NGs

Distinct reasons, worth keeping separate:

1. **Bitfield room.** Tagged tuple IDs need ~32 bits of structure
   before any unique-id room. 32-bit total is hopeless.
2. **Sparse allocation.** Reserved ranges per family with gaps for
   growth need address-space slack.
3. **Roaring64 over graph-IDs as virtual NG membership.** With
   tagged 64-bit IDs whose high bits carry structure, the membership
   bitmap of "all graphs with prefix P" is naturally clustered in
   the high-prefix range; Roaring64's branch-by-high-bits structure
   aligns rather than fights.
4. **Hybrid identifier space.** Once not strictly bound to a single
   corpus's row-IDs, document-IDs and term-IDs may want to share an
   address space without collision. 32-bit gets cramped.

### 9.5 Open questions, virtual NGs

- Are virtual NGs declared explicitly or inferred from URI shape?
- Are virtual NGs writable? (`INSERT DATA { GRAPH <virtual:...> { ... } }`
  goes where?)
- Can the prefix/suffix split be adjusted post-facto without
  re-encoding?
- Is the graph-IRI ID space global, per-tenant, or per-corpus?
- How does this interact with SPARQL `FROM NAMED` / `GRAPH ?g`
  semantics — does `?g` ever bind to a virtual IRI?

---

## 10. Formalisation strategy if/when we proceed

Sketch for context. Mirrors how the rest of the project is organised.

### 10.1 Layering

```
RoaringBitmap.Spec.fst         pure: a Roaring bitmap *means* a Set u32
RoaringBitmap.Container.fst    array | bitmap | run, with invariants
RoaringBitmap.Executable.fst   top-level (sorted assoc list of containers)
RoaringBitmap.Ops.fst          AND/OR/XOR/ANDNOT, k-ary, range
RoaringBitmap.Serialize.fst    portable format encode/decode
RoaringBitmap.Properties.fst   correctness lemmas vs Set u32 spec
```

### 10.2 Refinement-typed shapes

```fstar
type array_container =
  | AC : data:Seq.seq U16.t {
           sorted_strict data /\ Seq.length data <= 4096
         } -> array_container

type bitmap_container =
  | BC : words:Seq.seq U64.t { Seq.length words = 1024 }
       -> card:nat { card = popcount words /\ card > 4096 }
       -> bitmap_container

type run = { start : U16.t; length : U16.t { U16.v length > 0 } }

type run_container =
  | RC : runs:Seq.seq run {
           runs_sorted_non_adjacent runs
         } -> run_container

type container =
  | Array  of array_container
  | Bitmap of bitmap_container
  | Run    of run_container
```

### 10.3 The denotation function

`denote : roaring -> Set U32.t`. Every operation gets a lemma against
this; canonicalisation is a separate proof.

### 10.4 SPARQL-side correctness lemmas (if §6.2 lands)

```fstar
val s_idx_correct (g : rdf_graph) (idx : sparql_index{matches g idx})
                  (s : term_id) :
  Lemma (denote (lookup idx.s_idx s) ==
         { r | idx.rows r = Some t /\ t.s_id = s })

val bgp_intersect_correct (idx : sparql_index)
                          (pat : triple_pattern_bound) :
  Lemma (denote (intersect_bound idx pat) ==
         { r | idx.rows r = Some t /\ matches_pattern t pat })
```

The right-hand side is what `find_subjects`/`find_objects` already
specify in `RDF.Graph.Executable.fst`. Roaring is an implementation
of the same denotation.

### 10.5 What stays as `assume val`

Per iron rule #3:

- `popcount_u64 : U64.t -> n:nat{n <= 64}` (realised via OCaml
  `Int64.popcount` or compiler builtin).
- `tzcnt_u64`, `lzcnt_u64` for Algorithm 2.
- File-level byte I/O for serialize, same shape as existing parser
  glue.

No semantic logic in glue (rules #10/#11). Container selection,
threshold checks, merge logic stay in `.fst`.

### 10.6 Tractability table (current best guess, not measured)

| Feature | Tractable? | Notes |
|---|---|---|
| Container invariants | Yes | Same style as existing modules |
| Insert / remove / contains | Yes | Inductive proofs |
| Cardinality, rank, select | Yes | Inductive on shape |
| `(array, array)` ops | Yes | Two-pointer, straightforward |
| `(bitmap, bitmap)` ops | Yes | 1024-word loop; popcount as `assume val` |
| `(run, run)` ops | Likely | Trickier merge invariant |
| Promotion/demotion correctness | Yes | Pure case analysis |
| Portable serialize/deserialize | Yes | Mirrors `Parser.*.fst` |
| SIMD-accelerated popcount/AND | **No** — `assume val`, realise per-target |
| Roaring64 (any flavour) | Open | Adds another sorted-map layer + proofs |

---

## 11. Industry adoption / mindshare context

Roaring is roughly 12 years old and mature. Daniel Lemire's group;
first paper 2014, the SPE 2016 / arXiv 1603.06549 we're working from
is the consolidated version. High four-digit citation count, reference
implementations in five+ languages coordinated through the
RoaringBitmap GitHub org with a shared portable format spec.

### 11.1 Production adopters

- **Search / log / OLAP**: Apache Lucene (and so Elasticsearch /
  Solr) since ~2015, Apache Druid, Apache Pinot, Apache Kylin,
  Apache Spark, ClickHouse (`groupBitmap*` aggregates), Apache Doris
  and StarRocks (first-class `BITMAP` column type), InfluxDB.
  FeatureBase (formerly Pilosa) is a database built around Roaring.
- **Lakehouse**: Apache Iceberg v3 deletion vectors use Roaring's
  portable format directly (the format crossed from "popular library"
  to "de facto file-format standard" with Iceberg's adoption).
  Delta Lake's deletion vectors are similar but not byte-identical.
- **SQLite**: not in core. A community `sqlite-roaring` extension
  exists; not mainstream.
- **Graph databases**: very little adoption. Neo4j, JanusGraph,
  TigerGraph, ArangoDB, Memgraph all use other primary structures.
  FeatureBase markets graph-capable on Roaring but isn't really
  competing with property-graph DBs.
- **SPARQL / triple-stores**: **essentially none** at primary index
  level. Jena TDB, Oxigraph, Virtuoso, Blazegraph, GraphDB, Stardog
  use B-trees or hash. HDT uses succinct rank/select bitvectors,
  *not* Roaring. RDFox is hash-based in memory.

### 11.2 Position for us

A formally verified Roaring-backed SPARQL backend is credible as
original work — not because Roaring is novel (it isn't), but because
nobody has put verification + RDF + Roaring together. The pitch is
"the bitmap layer SQL has had since 2015, but verified, and aimed at
RDF." Risk profile: "boring choice with fresh application" rather
than "novelty bet."

### 11.3 Honest competitor

For "compressed RDF backend," the real comparison point is **HDT and
its successors** (HDT-FoQ, HDT-MR, HDT-Q variants), which use
succinct rank/select bitvectors. Roaring trades some compression for
better updateability and a much simpler conformance story (a
standard portable format, multiple reference implementations).

### 11.4 Weaknesses / standard caveats

- **64-bit story is fragmented** (§7.5).
- **Very small sets**: a sorted u16[] or hash beats Roaring's
  overhead.
- **Very uniformly dense sets**: a plain u64[] bitmap can be
  marginally faster.
- **No native concurrent modification.**
- **No built-in cardinality estimation, no histograms, no
  range-aggregate primitives** — implement on top.

---

## 12. Community / process angle

Brought up as a strategic concern: making the process of improving
on-disk formats and indices **transparent, observable, testable, and
collaboration-friendly**, as a possible focus for an open-source
community effort.

### 12.1 Four properties, made concrete

**Transparent.** Every on-disk format has three artefacts, kept in
sync mechanically:

1. Human-readable spec (`formats/spec/<name>.md`) — wire format,
   invariants, version history.
2. F\* source of truth (`formal/fstar/Format.<Name>.fst`) — the
   `.md` renders *from* `(* spec: ... *)` doc-comments in the F\*
   source so they cannot drift.
3. Reference test vectors checked into git
   (`formats/conformance/<name>/*.golden`) with sibling `.dump`
   files showing the parsed structure.

**Observable.** `factoidal dump <file>` works on every known format
and prints a stable diffable text rendering. `factoidal explain
'<sparql>' --on <store>` (a promotion of the existing Pe5) prints,
per BGP triple, which index was used, how many row groups were
pruned, how many candidate rows survived intersection, where the
time went. Performance regressions become a `git diff` of explain
output rather than a wall-clock anecdote.

**Testable.** Three layers, each one a thing a contributor can
submit a PR against:

- Round-trip property: `decode(encode(b)) == b`. F\* lemma where
  possible, fuzz harness where not.
- Cross-impl conformance: read files written by upstream reference
  implementations (Java RoaringBitmap, Rust roaring, Iceberg, etc.);
  write files those implementations can read. CI pulls a small
  corpus from each upstream nightly.
- Corpus benchmarks: canonical inputs (Wikidata-1M slice, BSBM, the
  W3C suites we use), canonical workloads, results stored as JSONL
  with `(format, version, corpus, suite, metric, value)`. A history
  file in the repo; a tiny static page reads it and draws trend
  lines.

**Collaboration-friendly.** A bot does the boring work:

- A PR that touches `formal/fstar/Format.*` or `formats/*` triggers
  conformance + a fixed benchmark suite; a bot comments a markdown
  delta table (file size, encode/decode time, BGP-join median,
  before/after).
- Format proposals live as `experimental/formats/<name>/` with a
  `PROPOSAL.md` template (motivation, wire format, expected
  size/perf, risks). Anyone can open one without touching the
  verified path.
- A graduation checklist (`spec doc / F\* parser / round-trip lemma
  / golden vectors / cross-impl conformance / benchmark numbers /
  two reviewers`) gates promotion from `experimental/` →
  `formats/`. Status of each format (experimental / candidate /
  stable / deprecated) on a single landing page.

### 12.2 Why Roaring is the right pilot format for this process

It satisfies almost every property by construction:

- The portable serialization format already exists with reference
  implementations in five languages → cross-impl conformance is
  almost free (drop in a Java-emitted file, our reader must
  round-trip).
- Tiny public surface (set of u32, four binary ops). Contributors can
  grok the whole thing in an afternoon.
- Small enough to actually exercise the spec / code / conformance /
  benchmark pipeline end-to-end. Large enough to actually use.

If we can't make Roaring observable and collaborative, we can't make
COTTAS observable and collaborative — so the pilot is also a
derisking exercise for the bigger COTTAS-format work.

### 12.3 Costs

CI / bot / dashboard is real work — probably 1–2 weeks before the
first PR sees a useful comment. The bet is that the same
infrastructure unlocks community contribution at a scale that pays
for itself many times over: contributors can write golden files,
propose format tweaks, run benchmarks on their own hardware, all
without learning F\*.

---

## 13. What we are explicitly NOT deciding in this document

To make the un-decidedness visible:

- 32-bit vs 64-bit on any axis.
- Per-row-group vs global posting universes.
- Whether to commit to Parquet long-term, or build for substrate
  independence.
- Whether to adopt QLever-style tagged term-IDs.
- Whether to support virtual named graphs at all, and if so how.
- Whether Roaring is the right index structure vs sorted permutation
  tables (QLever-style) vs HDT-style succinct bitvectors vs something
  else.
- Whether to engage with Roaring64, and which flavour.
- Whether to retire the dense `.presence` companion in favour of
  Roaring (§6.1).
- Whether to add a row-level posting layer (§6.2).
- Whether to retire patch #97 (§6.3).
- Whether `formats/`-style community process (§12) is worth the
  upfront investment.

Each of these is an independent decision that benefits from explicit
argument before commitment. Several are coupled (e.g. virtual NGs
push toward 64-bit term-IDs which couples to Roaring64), but the
coupling itself is worth tracing rather than collapsed.

---

## 14. References

- Lemire, D., Ssi-Yan-Kai, G., Kaser, O. *Consistently faster and
  smaller compressed bitmaps with Roaring.* arXiv:1603.06549.
  <https://arxiv.org/abs/1603.06549>
- *Better bitmap performance with Roaring bitmaps.* Software:
  Practice and Experience, 2016.
- Reference Java implementation:
  <https://github.com/RoaringBitmap/RoaringBitmap>
- Rust port: <https://github.com/RoaringBitmap/roaring-rs>
  (docs: <https://docs.rs/roaring/latest/roaring/>)
- Portable format spec:
  <https://github.com/RoaringBitmap/RoaringFormatSpec>
- Apache Iceberg v3 deletion vectors:
  <https://iceberg.apache.org/spec/#deletion-vectors>
- QLever (Bast et al., U Freiburg):
  <https://github.com/ad-freiburg/qlever>
- HDT (Header-Dictionary-Triples):
  <https://www.rdfhdt.org/>
- Existing Factoidal docs cross-referenced:
  - `docs/designissues/2026-04-19-cottas-parquet-wiring-plan.md`
  - `docs/designissues/2026-04-19-hdt-fstar-status.md`
  - `docs/designissues/2026-04-24-indexing-audit.md`
  - `docs/designissues/2026-04-20-shrink-unverified-boundary.md`
  - `experimental/roaring-fstar/README.md` (companion)

---

## 15. Revision history

- **2026-05-06**: First version. Captures discussion-to-date.
- **Course corrections during the discussion that this document tries
  to honour rather than paper over:**
  - The phrase "we don't need 64-bit Roaring at all" was used
    prematurely in an earlier draft; the contingencies on row-grouped
    storage and on Parquet-as-substrate were not sufficiently
    surfaced. Hybrid DB / search-engine directions invalidate that
    framing. §7 is the corrected version.
  - "What does COTTAS give us?" deserves an honest answer: most of
    the value is Parquet's. COTTAS is a thin RDF-shaped wrapper with
    sidecars. §5.3 is the corrected version.
  - The role of Roaring vs HDT-Q vs sorted permutation tables
    (QLever) was initially under-discussed. §8.5 and §11.3 are the
    corrected version.
- **Rule of construction**: when the discussion identified a closure
  that should not have been closed, this document reopens it
  explicitly rather than smoothing it over.
