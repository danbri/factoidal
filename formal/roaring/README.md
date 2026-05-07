# Roaring Bitmaps in F* — Exploration Notes

Status: **scoping / pre-design**. Nothing here is wired into the main
`formal/fstar/` tree yet. This folder is a sandbox to figure out
(a) how much of the Roaring data structure can plausibly be specified
and verified in F*, (b) what gets extracted vs. left as `assume val`,
and (c) where Roaring would slot into Factoidal's RDF/SPARQL +
COTTAS-on-disk + (eventual) Parquet story.

---

## 1. What Roaring Is — One-Paragraph Recap

Roaring is a compressed bitmap (set of `u32`) that beats run-length
families (WAH/Concise/EWAH) on both speed and size by **not committing
to one representation**. A `u32` is split into a high 16 bits (which
"chunk" of `2^16` it falls in) and a low 16 bits (position within the
chunk). The top level is a sorted associative array `(u16 high) →
container`. Each container holds the low-16 values for one chunk and
is **one of three** types, chosen to minimise space for that chunk's
density:

| Container | Layout                        | Best when            | Serialized size          |
|-----------|-------------------------------|----------------------|--------------------------|
| Array     | sorted `u16[]`, distinct      | sparse (≤ 4096 vals) | `2 + 2c` bytes (card field + data) |
| Bitmap    | `u64[1024]` (2^16 bits)       | medium / dense       | always 8192 bytes        |
| Run       | sorted `(start: u16, len-1: u16)` pairs, non-overlapping, non-adjacent | long compressible runs | `2 + 4r` bytes (run-count + pairs) |

The structure auto-converts. Insert/remove flips an array to a bitmap
once cardinality crosses 4096; remove flips bitmap → array when
cardinality drops to ≤ 4096. A `runOptimize()` pass swaps to a run
container under two precise rules from §4 of the paper:

- if cardinality > 4096: only allowed when `r ≤ ⌈(8192 − 2)/4⌉ = 2047`;
- if cardinality ≤ 4096: only allowed when `r < c/2`.

Per-chunk operations (AND/OR/XOR/ANDNOT) have separate hand-written
routines for each pair of container types — six interesting cases
since the algebra is symmetric: `(array, array)`, `(array, bitmap)`,
`(bitmap, bitmap)`, `(run, run)`, `(run, array)`, `(run, bitmap)`.
Each one predicts the output container type up front to avoid an
expensive post-hoc conversion.

**Paper:** Lemire, Ssi-Yan-Kai, Kaser. *Consistently faster and
smaller compressed bitmaps with Roaring.* arXiv:1603.06549. (Earlier:
*Better bitmap performance with Roaring bitmaps*, SPE 2016.)

---

## 2. Paper Summary (arXiv:1603.06549)

### 2.1 Two-level structure

- Top level: a **dynamic array of (key, container) pairs**, sorted by
  key. Key = high 16 bits of the integer. Lookup is binary search,
  `O(log K)` where `K` is number of non-empty chunks (≤ 65536).
- Each chunk owns one container that physically stores the low 16
  bits of the integers whose high 16 bits match the key.

### 2.2 The three containers

1. **Array container.** `u16[]`, sorted ascending, distinct.
   Cardinality bounded at 4096 by construction. Operations are
   merge-style scans; membership is binary search.
2. **Bitmap container.** Fixed-size `u64[1024]` = 8 KiB =
   `2^16` bits. Bit `i` set iff the value `i` is present.
   Constant-time membership via `(word[i >> 6] >> (i & 63)) & 1`.
   Cardinality stored alongside (popcount cached) so AND/OR don't have
   to rescan to learn size.
3. **Run container.** Sorted array of `(start, length-1)` `u16` pairs,
   each pair encoding a maximal run `[start, start + length - 1]`.
   Runs are non-overlapping and non-adjacent (i.e. canonical).
   **Cardinality is *not* cached at runtime** — only computed on the
   fly or written into the serialized form. The paper argues this is
   fine because run containers are expected to have few runs.

### 2.3 Conversion rules

- Array → Bitmap when insertion would exceed 4096.
- Bitmap → Array when a remove drops cardinality at-or-below 4096
  (lazy: typically only on `runOptimize` / serialization).
- Any → Run when `4 * num_runs + 4 < size_of_current_repr`.
  Computed by a single linear pass that counts runs.

The 4096 threshold is the cross-over where a sorted `u16[]` (2 bytes
each) costs the same as a fixed 8 KiB bitmap.

### 2.4 Set algebra — the six cases

For each of AND, OR, XOR, ANDNOT and each unordered pair of container
types, the paper gives a dedicated routine. Output type is *predicted
up front*; if the prediction is wrong the result is converted at the
end. Key choices from §5:

- `(array, array)` AND: simple two-pointer merge if cardinalities are
  similar (`c1/64 < c2 < 64·c1`), galloping intersection otherwise.
  Output is always an array.
- `(array, array)` OR: if `c1 + c2 ≤ 4096`, sorted merge into a new
  array; else materialise into a bitmap, then demote to array if
  popcount turns out to be ≤ 4096.
- `(bitmap, bitmap)` AND: 1024-word loop computing pairwise AND, with
  popcount accumulated *first* to decide if the output is a bitmap or
  an array (exact-size allocation).
- `(bitmap, bitmap)` OR: 1024-word loop, popcount alongside.
- `(array, bitmap)` AND: scan the array, test each value against the
  bitmap; output is an array sized to the input array.
- `(array, bitmap)` OR: clone the bitmap, set the array's bits.
- `(run, run)` AND: walk both run lists, emit overlap. Convert at the
  end to bitmap (if too many runs) or array (if too few values).
- `(run, run)` OR: walk both, append to output run, extending the
  previous run when ranges touch. No conversion to array possible — by
  construction the average run length only grows.
- `(run, array)` AND: scan the array, advance the run pointer; output
  is always an array.
- `(run, array)` OR: treat array as a degenerate run container (all
  length-1 runs), run the (run, run) OR algorithm, then check whether
  the result wants demotion to bitmap *or* array.
- `(run, bitmap)` AND: if `card_run ≤ 4096`, materialise array by
  iterating run values and testing the bitmap; else clone the bitmap
  and AND-NOT-out everything outside the runs (Algorithm 3).
- `(run, bitmap)` OR: clone the bitmap, OR the run ranges in
  (Algorithm 3).

**Special-case optimisation.** If a run container holds the single run
`[0, 2^16)` (i.e. the whole chunk is full), every union with it is
just the other operand. Cheap to detect (one comparison), and it
catches very common cross-container long-run cases cheaply.

The paper proves the algebra closes correctly under the canonicalisation
rule (always choose the smallest representation for the result).

### 2.4a The three named algorithms (these are the load-bearing F* port targets)

The paper formalises three by-name algorithms; everything else in §5
is described prose-style. These three are the natural unit of F\*
formalisation:

- **Algorithm 1: count runs in a bitmap container.** Per word `Cᵢ`,
  compute `bitCount((Cᵢ << 1) ANDNOT Cᵢ)` and add a cross-word
  correction `(Cᵢ >> 63) ANDNOT Cᵢ₊₁`. The paper notes that you can
  *short-circuit* once a lower bound exceeds 2047 — beyond that
  threshold the answer "don't convert" is already determined.
- **Algorithm 2: extract runs from a bitmap container.** Iterates
  using `tzcnt` (least-significant 1-bit) to find run starts, then
  `tzcnt` of the negated word to find run ends. Touches each word a
  constant number of times.
- **Algorithm 3: set/clear a range `[i, j)` of bits in a bitmap.**
  Bit-twiddly mask construction `(Z << (i mod 64))` and
  `(Z >> ((-(j mod 64)) mod 64))`, then a fast inner loop over the
  fully-covered words. Used for both `OR` (set range) and `ANDNOT`
  (clear range), parameterised by the operator.

### 2.5 Auxiliary operations

- **cardinality** is `O(K)` (sum of per-container cached counts).
- **rank(x)** = `count of set bits ≤ x` — sum cardinalities of chunks
  with key < `high(x)`, plus rank within the matching container
  (binary search for array, popcount of prefix words for bitmap, prefix
  sum of run lengths for run).
- **select(j)** — find the `j`-th set bit — symmetric: skip whole
  chunks by cardinality, then locate within the container.

### 2.6 Portable serialization (the "spec")

The paper §4 describes the on-the-wire layout (the cookies and exact
byte offsets are pinned down by the separate
`RoaringFormatSpec` repo, not the paper itself). Two variants:

- **No-run variant** (`0x3BC0` cookie): `(key, cardinality - 1)`
  pairs interleaved at the directory level — cardinalities stored as
  `u16` for compactness — then payloads. The 16-bit cardinality field
  works because no container exceeds 2^16 values.
- **With-run variant** (`0x3BF0` cookie): same, plus an
  uncompressed bit-per-container "is-this-a-run-container?" bitmap
  immediately after the directory, before the payloads.

Container payloads:
- Array: raw `u16[c]` (cardinality is in the directory).
- Bitmap: raw `u64[1024]`.
- Run: `u16 num_runs` then `num_runs × (u16 start, u16 length-1)` pairs.

For run containers, *cardinality is computed and written to the
directory at serialize time*, so memory-mapped readers don't pay the
recompute cost.

### 2.6a Lazy union (k-ary aggregation)

The k-ary `union` of many bitmaps is a hot path. Recomputing
cardinality after every pairwise union wastes ~30% (Chambi et al.,
confirmed in this paper). The "lazy union" optimisation:

- Skip cardinality maintenance during pairwise unions; mark the
  affected bitmap container's cardinality field with the sentinel `-1`
  ("unknown").
- For `(run, array)` unions inside the chain, always emit a run
  container (or bitmap if too many runs) — even when an array would
  be smaller — to avoid intermediate type churn.
- After the whole chain finishes, run a single "repair" pass: popcount
  any bitmap whose cardinality is `-1`, and demote any over-budget
  run containers.

This pattern (work-with-sloppy-invariant, repair-at-end) is *also* a
nice F\* formalisation target: the lazy form is observationally
equivalent to the strict form, with the equivalence lemma deferred
until after the repair.

### 2.6b Naive vs heap-based k-ary union

For `N` bitmaps of size `B`, naive 2-by-2 union has time `O(B·N²)`
(when results grow) and memory `O(B)`. Heap-based pulls the two
smallest off a min-heap each round: time `O(B·N·log N)`, memory
`O(B·N)`. The paper finds *neither dominates* — naive wins on dense /
unsorted data because pairwise unions become bitmap-vs-bitmap and stay
in-place; heap wins on sparse-sorted data because intermediates remain
small. Default in the reference implementation is naive.

### 2.6c Array-container growth heuristic (capacity vs. cardinality)

Worth mentioning because it's the kind of detail where a verified
spec usually papers over the engineering choice. The paper actually
specifies it:

- < 64 entries: double on growth.
- 64–1067 entries: ×3/2 on growth.
- ≥ 1067 entries: ×5/4 on growth.
- Cap at 4096; if grown above 3840, allocate the full 4096 immediately.

This trades a small amount of speed for ~13% average overhead instead
of the ~50% you get from naive doubling. For F\* purposes this is
internal-implementation detail (the spec says nothing about capacity);
worth knowing because the behaviour shows up in benchmarks.

### 2.7 Performance results

Datasets used: CensusInc, Census1881, Weather, Wikileaks (each in
original and lex-sorted variants — sorting matters a lot for RLE
formats).

| Test (best-of-table) | Roaring+Run vs Concise/WAH | Roaring+Run vs EWAH |
|---|---|---|
| Random access (in-heap)        | up to ~870× faster | up to ~360× faster |
| Successive intersections       | 3.5× to ~460×      | 1.4× to ~150×      |
| Successive unions              | 1.7× to ~210×      | 1.0× to ~43×       |
| K-ary union (naïve)            | 2.7× to ~210×      | 0.88× to ~13× (one EWAH win) |
| Memory-mapped intersection     | 5.3× to ~140×      | 1.3× to ~79×       |

Compression is near-best for both sorted and unsorted data — the only
case in the paper where Concise beats Roaring+Run on size is
CensusInc-sorted (by 8%), and Roaring+Run is still 6–8× faster there.
On Census1881 (sparse, unsorted) Roaring+Run uses ~60% the space of
Concise *and* is dozens to hundreds of times faster.

Container-mix observations from the appendix (worth noting for our
RDF use case): on the very sparse `Wikileaks` dataset, **100% of
Roaring containers are array containers** (no bitmaps at all). After
runOptimize, **89.5% become run containers**, which compresses 3×
better. This is the kind of profile RDF posting lists for rare
predicates will look like.

### 2.8 Future directions explicitly called out

The conclusion section flags what the authors expect to add (most of
which has happened by 2026):

- Copy-on-write containers during unions.
- Postponing/omitting cardinality calculation more aggressively.
- Run-compression of intermediate results.
- Dynamically-sized bitmap containers (only cover the used range).
- **Lucene's "negated array container"** as a fourth container type
  (an array of *absent* low-16 values, useful for near-full chunks).
- Container-level parallelism, SIMD (CRoaring 2.x has done this on
  x86/AVX-512 and ARM Neon), GPU/Xeon Phi adaptations.

For our F\* port the negated-array container is worth flagging: it's
an opt-in compatibility issue — files written by Lucene with negated
arrays would need an extra container variant in our spec.

---

## 3. Rust `roaring` Crate Summary (docs.rs/roaring)

The crate is the Rust port of the Java reference implementation. Two
public types:

- **`RoaringBitmap`** — set of `u32`. The core type.
- **`RoaringTreemap`** — set of `u64`, implemented as a
  `BTreeMap<u32, RoaringBitmap>` (third-level split).

Both implement the standard `BitOr`, `BitAnd`, `BitXor`, `Sub` (and
their `*Assign` forms), `IntoIterator`, `FromIterator`, `Extend`, plus
range methods (`insert_range`, `remove_range`, `range`,
`contains_range`). The **`MultiOps` trait** offers bulk variants
(`union`, `intersection`, etc.) on iterators of bitmaps for cheaper
many-way merges.

Serialization: `serialize_into` / `deserialize_from` use the official
**Roaring portable format**, so files round-trip with the C/Java/Go
implementations. `serde` and `bytemuck` integrations are feature-gated.

Errors of interest: `NonSortedIntegers` (when an API requires sorted
input) and `IntegerTooSmall` (e.g. `try_push` of a value not strictly
greater than the current max). A `simd` feature exists but is gated to
nightly and explicitly marked untested.

What the crate gives us that we'd want to mirror in F*:
- `insert / remove / contains / len` with the canonicalisation
  invariant maintained.
- `union / intersection / difference / symmetric_difference` over
  pairs and over k-ary iterators.
- `iter`, `range(a..b)`, `select(n)`, `rank(x)`.
- Portable serialize/deserialize.

---

## 4. Why Factoidal Cares

Several places in the project either already want a compressed integer
set or will once we push on scale:

### 4.1 RDF triple/quad indexes (COTTAS, SPO/POS/OSP)

Each RDF graph compiles to interned term IDs (see
`RDF.Graph.Executable.fst`). A triple becomes `(s_id, p_id, o_id)` of
`u32`s. For a fixed predicate, the set of triples mentioning it is
**exactly** a set of triple-row IDs — i.e. a `RoaringBitmap` over
row positions. The same is true for "all triples whose subject =
`s_id`" or "all triples in named graph `g_id`". BGP join evaluation
is then **bitmap intersection** of one bitmap per pattern position
that's bound to a constant — Roaring's strongest case.

This would replace (or accelerate) the OCaml-side
`RDF_CottasStore.ml` posting structures that currently violate iron
rule #11 (semantic logic on the OCaml side). A verified F* Roaring
spec is the principled way to migrate that logic back into the F*
runtime.

### 4.2 SPARQL evaluator

`SPARQL11.Algebra.fst`'s join, filter-pushdown and DISTINCT operators
all benefit from set-of-row-IDs intermediates rather than materialised
`solution_mapping list`s. Roaring gives us O(min) intersection,
deterministic memory, and serializable intermediates (relevant for
SERVICE / federation caching).

### 4.3 Parquet / on-disk story

Parquet itself doesn't ship Roaring as part of the core spec, but the
ecosystem around it does:

- **Apache Iceberg "deletion vectors"** (v3) use Roaring (specifically
  the EWAH-compatible portable format) to mark deleted row positions
  per data file.
- **Apache Druid, Apache Pinot, Apache Spark, Apache Lucene** all use
  Roaring as a row-set / posting-list primitive layered on columnar
  storage.
- **Apache Parquet's BloomFilter and ColumnIndex page-skipping** play
  well with Roaring as the "which row groups still survive" carrier
  after predicate pushdown.

For Factoidal, the question is: when we lower COTTAS to an on-disk
columnar format (Parquet candidate, also our existing companion-file
layout), do we want the **post-predicate row selection** carried as a
Roaring bitmap? If so, an F*-verified Roaring becomes load-bearing.

### 4.4 Term-dictionary posting lists

The interner maps IRIs/literals to `u32` term IDs. Inverted indexes
("which triples mention term `t`") are sets of `u32` — Roaring
again. Same for full-text / regex indexes if we ever add them.

---

## 5. F* Porting Strategy — Sketch

### 5.1 Layering

The plan mirrors how the rest of the project is organised: a **pure
mathematical spec** layer, an **executable** layer with refinement
types pinning the canonical form, then **extraction**.

```
RoaringBitmap.Spec.fst         pure: a Roaring bitmap *means* a Set u32
RoaringBitmap.Container.fst    array | bitmap | run, with invariants
RoaringBitmap.Executable.fst   top-level (sorted assoc list of containers)
RoaringBitmap.Ops.fst          AND/OR/XOR/ANDNOT, k-ary, range
RoaringBitmap.Serialize.fst    portable format encode/decode
RoaringBitmap.Properties.fst   correctness lemmas vs Set u32 spec
```

### 5.2 Types (sketch)

```fstar
type array_container =
  | AC : data:Seq.seq U16.t {
           sorted_strict data /\ Seq.length data <= 4096
         } -> array_container

type bitmap_container =
  | BC : words:Seq.seq U64.t { Seq.length words = 1024 }
       -> card:nat { card = popcount words /\ card > 4096 }
       -> bitmap_container

type run =
  { start  : U16.t
  ; length : U16.t { U16.v length > 0 } }   // length, not length-1, for sanity

type run_container =
  | RC : runs:Seq.seq run {
           runs_sorted_non_adjacent runs
         } -> run_container

type container =
  | Array  of array_container
  | Bitmap of bitmap_container
  | Run    of run_container

type roaring =
  { chunks : Seq.seq (U16.t * container) {
      sorted_strict_by_key chunks /\
      forall_canonical chunks  // each chunk uses smallest repr
    } }
```

The invariants matter: they're what makes `union` and `intersection`
provably correct without runtime checks, and what lets the proofs
discharge the "no representation drift" guarantee that the paper
assumes informally.

### 5.3 Spec relation

Define `denote : roaring -> Set U32.t` mapping each Roaring value to
the abstract integer set it represents. Every operation gets a lemma:

```fstar
val union_correct (a b : roaring) :
  Lemma (denote (union a b) == Set.union (denote a) (denote b))
```

This is the **only** definition of correctness — performance and
canonicalisation are below it.

### 5.4 What's tractable in F*

| Feature                        | Tractable today? | Notes                               |
|--------------------------------|------------------|-------------------------------------|
| Type invariants (sorted, etc.) | Yes              | Same style as `RDF.Graph.Executable`|
| Insert / remove / contains     | Yes              | Straightforward inductive proofs    |
| Cardinality, rank, select      | Yes              | Inductive on container shape        |
| `(array, array)` ops           | Yes              | Two-pointer merge, inductive proof  |
| `(bitmap, bitmap)` ops         | Yes              | 1024-word loop; popcount as `assume val` initially |
| `(run, run)` ops               | Likely           | Trickier merge invariant; doable    |
| Promotion/demotion correctness | Yes              | Pure, by case analysis              |
| Portable serialize/deserialize | Yes              | Mirrors existing parser combinators in `Parser.*.fst` |
| SIMD-accelerated popcount/AND  | **No** — extract `assume val` and realise in OCaml/C glue per rule #3 |

### 5.5 Extraction targets

- **OCaml** via `--codegen OCaml` — same path as the rest of the
  project. `Seq U64.t` extracts to OCaml arrays via existing patches.
- **C / WASM** via KaRaMeL — feasible *if* we keep containers
  non-`noeq` (anti-pattern: `noeq` blocks KaRaMeL). The fixed-size
  bitmap container maps cleanly to a C `uint64_t[1024]`.

### 5.6 Glue / `assume val` budget

Following rule #3, expect to leave (and document with issue numbers):

- `popcount_u64 : U64.t -> n:nat{n <= 64}` — `assume val`, realise via
  OCaml `Int64.popcount` or compiler builtin.
- (Optionally) `tzcnt_u64`, `lzcnt_u64` for fast iteration over set
  bits.
- File-level `read_bytes` / `write_bytes` for serialize, same shape
  as existing parser glue.

No semantic logic in glue — that's rule #10 / #11. All container
selection, threshold checks, and merge logic stays in `.fst`.

---

## 6. Open Questions

1. **Scope vs. cost.** A complete verified Roaring is ~3–5k LoC of
   F*; the proofs are nontrivial but well within what the rest of
   the repo already does. Is the *full* portable format necessary, or
   do we only need an in-memory subset for the COTTAS evaluator?
2. **Parquet alignment.** Iceberg's deletion-vector format is *almost*
   the standard Roaring portable format. If we target Parquet/Iceberg
   compatibility, we should serialize byte-identical to that flavour.
3. **`assume val` boundary for popcount/SIMD.** A pure F* popcount
   verifies fine but extracts to a slow loop. Where do we want the
   verified-but-slow vs. unverified-but-vectorised cut? Likely
   `assume val popcount` with an OCaml realisation, then a separate
   pure F* `popcount_pure` proven equivalent (left as a lemma, never
   called at runtime).
4. **Interaction with COTTAS on-disk caches.** Today's
   `RDF_CottasStore.ml` and Yod6/Tet3/Lamed3 sidecars already do
   posting-list-shaped work in OCaml. Roaring-in-F* is a candidate
   replacement — but it lands inside the rule-#11 freeze zone and
   should be prioritised relative to the boundary audit
   (`docs/designissues/fstar-ocaml-boundary-audit.md`).
5. **Treemap (u64) variant.** RDF term IDs are currently `u32`. If we
   ever go to 64-bit IDs (graphs > 4B triples), we'd need a treemap
   wrapper, which adds another sorted-map layer and another set of
   proofs. Defer until we hit the scale.

---

## 7. References

- Lemire, D., Ssi-Yan-Kai, G., Kaser, O. *Consistently faster and
  smaller compressed bitmaps with Roaring.* arXiv:1603.06549.
  <https://arxiv.org/abs/1603.06549>
- *Better bitmap performance with Roaring bitmaps.* Software:
  Practice and Experience, 2016.
- Reference Java implementation: <https://github.com/RoaringBitmap/RoaringBitmap>
- Rust port (this is what we'd cross-check extraction against):
  <https://github.com/RoaringBitmap/roaring-rs> /
  <https://docs.rs/roaring/latest/roaring/>
- Portable format spec:
  <https://github.com/RoaringBitmap/RoaringFormatSpec>
- Apache Iceberg deletion vectors (Roaring on disk):
  <https://iceberg.apache.org/spec/#deletion-vectors>

---

## 8. Suggested Next Step

Stand up `formal/roaring/Spec.fst` with **just** the
container types + invariants + `denote` function, and prove
`contains_correct` and `union_correct (Array, Array)`. That's the
smallest possible end-to-end demonstration that the project's existing
F* + extraction toolchain handles a Roaring-shaped problem, and it's
enough to estimate the cost of the full port.
