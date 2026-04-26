# Compound `(p, o)` presence bitmap — F\* design (issue #104)

**Date:** 2026-04-26
**Phase:** 2.6 follow-on (after Tet3 single-bitmap redirect lands at all 3 call sites)
**Author handle:** nun4
**Status:** DESIGN ONLY — no source modifications. Implementation deferred.

## TL;DR

To close Q03's 4.2s gap (issue #104), build a per-row-group **compound
`(predicate_token, object_token)` presence index** as a sibling F\*
module `RDF.CottasStore.CompoundPresenceBitmap.fst` mirroring Psi3's
single-column `RDF.CottasStore.PresenceBitmap.fst`. The companion file
is a new `.po.presence` written next to the existing `.cottas` /
`.{s,p,o,g}.presence` siblings.

Recommended encoding: **sparse-roaring sorted `(p_id, o_id)` pair list
per rg** (exact, ~12 MB total for parliament). Bloom filter per rg is
the documented fallback if sparse encoding's worst case bites.

## 1. Storage format

### 1a. Encoding decision

Three candidates evaluated against parliament corpus dimensions
(232 predicate dict tokens, 956 K object dict tokens, 26 row groups,
~122 K rows/rg, 3.14 M quads total):

| Encoding | Size estimate | Exact? | Verdict |
|---|---|---|---|
| Flat 2D bitmap per rg, `pred_dict_size × obj_dict_size` bits | 232 × 956 000 / 8 × 26 = **0.72 GB** | Yes | Too big. Most cells are empty; pay full quadratic cost. **Rule out.** |
| Bloom filter per rg, m=256 KB, k=4 hashes | 256 KB × 26 = **6.5 MB** | No (~0.1% FP) | Tractable. Tunable. **Fallback.** |
| Sparse-roaring sorted `(p_id, o_id)` per rg | per rg: ≤ unique (p,o) pairs × 8 bytes (u32 each); parliament has ~3.14 M total quads / 26 rgs ≈ 121 K rows/rg, with very heavy `(p_id)` skew (top predicates dominate) so distinct `(p,o)` per rg ≈ 60–100 K. **Total ~12–20 MB.** | Yes | Tractable. **Primary recommendation.** |

**Why sparse-roaring is primary:** parliament's empirical density is
~half a percent of the flat 2D space (~50 K – 100 K distinct pairs out
of 232 × 956 K possible). Exactness eliminates Q03's whole class of
failure mode (a Bloom false positive on `(rdf:type, geo:wktLiteral)`
in rg=22 would re-open the bug for marginal cases). Read cost is one
binary-search per `(rg, p_id, o_id)` query, ~17 reads max per rg lookup
on ~100 K-element sorted list — strictly cheaper than the existing
Tet3 per-column lookup which is two Hashtbl probes.

**Why Bloom is the fallback, not primary:** Bloom is preferable if
either (i) parliament-class sparsity assumption breaks on a future
corpus where every rg has, say, 1 M distinct `(p,o)` pairs (sparse
list grows to GBs), or (ii) we want a fixed per-rg byte cost that is
independent of data shape. The fallback path is implemented as a
sibling encoding tag in the file format header so a corpus can choose;
default `enc=sparse_roaring`.

### 1b. File layout — `.po.presence`

Little-endian throughout; mirrors the discipline of
`RDF.CottasStore.OnDiskIndex.fst` (cf. dict + presence formats lines
26–51 of that file).

```
[ magic        : u32   ASCII 'COPP' = 0x50504f43 ]
[ version      : u32   layout version, currently 1 ]
[ encoding     : u32   1 = sparse_roaring, 2 = bloom ]
[ num_rgs      : u32 ]
[ pred_dict_size : u32   == .p.presence num_tokens (cross-checked at open) ]
[ obj_dict_size  : u32   == .o.presence num_tokens (cross-checked at open) ]
[ rg_index_offset : u64  byte offset to rg_index[] from file start ]
[ pad to 8-byte boundary ]
[ rg_index[]   : (u64 start_off, u64 end_off) × num_rgs
                 byte offsets of each rg's payload section ]
[ rg_payload   : per encoding:
   sparse_roaring:
     [ npairs : u32 ]
     [ pairs  : (u32 p_id, u32 o_id) × npairs, sorted by (p_id, o_id) ]
   bloom:
     [ m_bits      : u32 ]
     [ k_hashes    : u32 ]
     [ bitmap      : ceil(m_bits / 8) bytes ] ]
```

Header is 40 bytes pre-padding, 48 with 8-byte alignment for the
`rg_index_offset` value. Total header + per-rg index = 48 + 16 × num_rgs
= 464 bytes for parliament's 26 rgs. Then payload follows.

The two natural cross-validation invariants checked at open time:
- `compound_header.pred_dict_size == p.presence.num_tokens`
- `compound_header.obj_dict_size  == o.presence.num_tokens`

If either fails, the compound bitmap is treated as absent (same safe
fallback as Psi3: caller proceeds with per-column Tet3 prune).

## 2. F\* API surface — `RDF.CottasStore.CompoundPresenceBitmap.fst`

Mirrors Psi3's `PresenceBitmap.fst` shape exactly. Pseudo-signatures
below (NOT real F\* — design sketch only; implementation is a separate
commit).

```fstar
module RDF.CottasStore.CompoundPresenceBitmap

open RDF.CottasStore.OnDiskIndex
open FStar.Mul

// COPP magic for compound presence
let copp_magic_u32 : nat = 0x50504f43
let layout_version : nat = 1
let enc_sparse_roaring : nat = 1
let enc_bloom : nat = 2

type compound_header = {
  ch_magic           : nat;
  ch_version         : nat;
  ch_encoding        : nat;       // 1 or 2
  ch_num_rgs         : nat;
  ch_pred_dict_size  : nat;
  ch_obj_dict_size   : nat;
  ch_rg_index_offset : nat;
}

let compound_header_ok (h : compound_header) : Tot bool =
  h.ch_magic = copp_magic_u32 &&
  h.ch_version = layout_version &&
  (h.ch_encoding = enc_sparse_roaring || h.ch_encoding = enc_bloom)

type compound_handle = {
  ph_path   : string;
  ph_header : compound_header;
}

let compound_handle_ok (h : compound_handle) : Tot bool =
  compound_header_ok h.ph_header

let valid_compound_handle = h:compound_handle{ compound_handle_ok h }

// ----- open / close (composes assume vals from OnDiskIndex.fst) -----

val open_compound : path:string -> Tot (option compound_handle)
val close_compound : h:compound_handle -> Tot unit

// ----- core lookup primitive -----

// rg_could_contain_pair: per-rg test that some row in rg has both
// (predicate_token = p) AND (object_token = o).
//
// Semantics:
//   - rg out of range -> false (no such rg, vacuously no row)
//   - p out of pred_dict_size -> false (token id not present at write time)
//   - o out of obj_dict_size  -> false
//   - Otherwise: read this rg's payload, dispatch on encoding:
//     * enc_sparse_roaring: binary search the sorted (p_id, o_id) list
//     * enc_bloom: test k bit positions
//   - On any I/O failure: returns true (safe over-include, same
//     discipline as Psi3 line 112).
val rg_could_contain_pair :
  h:valid_compound_handle ->
  rg:nat ->
  p:nat ->
  o:nat ->
  Tot bool

// rg_passes_pair: caller-shaped wrapper. `bound_p` and `bound_o` are
// option-typed token ids. Returns true if the rg cannot be ruled out.
//
// Semantics:
//   - Both bound: rg_could_contain_pair
//   - Only p bound, o unbound: defer to per-column predicate test
//     (caller already has Psi3 handle); this function returns true
//     so the AND with Psi3's per-column result is the operative gate.
//   - Both unbound: true (every rg passes a wildcard)
val rg_passes_pair :
  h:valid_compound_handle ->
  rg:nat ->
  bound_p:option nat ->
  bound_o:option nat ->
  Tot bool

// option-handle convenience (mirrors Psi3 rg_could_contain shape)
val compound_rg_passes_pair :
  oh:option compound_handle ->
  rg:nat ->
  bound_p:option nat ->
  bound_o:option nat ->
  Tot bool   // true if oh = None / handle invalid (safe over-include)

// dimension accessors
val compound_num_rgs        : valid_compound_handle -> Tot nat
val compound_pred_dict_size : valid_compound_handle -> Tot nat
val compound_obj_dict_size  : valid_compound_handle -> Tot nat
```

### 2a. Soundness lemma — invariant statement

Mirrors Psi3 lines 178–219. The producer-side obligation is:

```fstar
// Spec ground truth: "row-group rg contains at least one row whose
// predicate-token-id is p AND object-token-id is o."
let pair_occurs_pred_t = nat -> nat -> nat -> bool
//                       rg     p      o     -> bool

let compound_built_correctly
  (h : valid_compound_handle)
  (pair_occurs : pair_occurs_pred_t) : Type0 =
  forall (rg p o : nat).
    rg < h.ph_header.ch_num_rgs /\
    p  < h.ph_header.ch_pred_dict_size /\
    o  < h.ph_header.ch_obj_dict_size ==>
    (rg_could_contain_pair h rg p o = pair_occurs rg p o)

// Soundness: a `false` result is sound to trust at the call site.
val rg_could_contain_pair_sound :
  h:valid_compound_handle ->
  pair_occurs:pair_occurs_pred_t ->
  rg:nat -> p:nat -> o:nat ->
  Lemma
    (requires compound_built_correctly h pair_occurs /\
              rg < h.ph_header.ch_num_rgs /\
              p  < h.ph_header.ch_pred_dict_size /\
              o  < h.ph_header.ch_obj_dict_size /\
              rg_could_contain_pair h rg p o = false)
    (ensures pair_occurs rg p o = false)
```

The lemma BODY is `()` — it discharges from the universal hypothesis,
exactly as Psi3 lines 209–219 explain. The remaining honest gap is
the writer-side proof that `compound_built_correctly` actually holds
for any given on-disk `.po.presence` file; that proof is the writer's
obligation (see Section 3).

### 2b. Cross-product with Psi3 — composed `rg_passes_compound_and_per_column`

Triple patterns where p and o are both bound get their tightest gate
from compound; subj-bound queries still need Psi3's per-column gate.
The composition is straightforward AND:

```fstar
val rg_passes_compound_and_per_column :
  rg:nat ->
  oh_compound : option compound_handle ->
  oh_s : option PresenceBitmap.bitmap_handle -> bound_s:option nat ->
  oh_p : option PresenceBitmap.bitmap_handle -> bound_p:option nat ->
  oh_o : option PresenceBitmap.bitmap_handle -> bound_o:option nat ->
  Tot bool
  // Returns true iff:
  //   PresenceBitmap.rg_passes_all rg ... per_column ... &&
  //   compound_rg_passes_pair oh_compound rg bound_p bound_o
  //
  // Intuition: compound is strictly more selective WHEN both p and o
  // are bound; otherwise it returns true (vacuous), and the per-column
  // gate carries the work. Rule of safe under-prune: false from EITHER
  // gate is sound to skip.
```

## 3. Writer

**Recommendation: stay in the OCaml glue** as a rule-#11(b)-allowed
companion-file writer. Justification:

- The per-column `.{s,p,o}.presence` writers are already in OCaml
  (Vav3, see `experimental_ocaml_glue/cottas_ondisk_zzzzz_ondisk_index.sh`).
  Writing the compound file uses the same column-decode loop already
  present, plus per-rg `(p_id, o_id)` collection into a sorted list.
- The reader path is the load-bearing logic; it lives in F\* per
  rule #11. No semantic decisions in the writer beyond "enumerate
  every (p, o) pair appearing in this rg" which is mechanical.
- Migrating writers to F\* is a separate, larger project (Vav3 itself
  hasn't been migrated). Don't expand scope.

The writer becomes a single new patch:
`experimental_ocaml_glue/cottas_ondisk_NNN_compound_po_writer.sh`
(numbering chosen at implementation time to follow lexical ordering
after Vav3). It hooks into the same `ensure_objects_loaded` /
`ensure_predicates_loaded` walk that Tet3 already does — adding a
joint `(p_id, o_id)` collector per rg, sorted at the end and written
out. Cost: O(N log N) per rg where N is rows/rg ≈ 122 K, dominated
by the existing column decode.

**Producer-side proof obligation (open):** the OCaml writer must
satisfy `compound_built_correctly`. We can't prove it in F\* directly
(writer is OCaml), but we mitigate via:
- a "verify on read" pass at first open that ensures the sorted-list
  invariant (binary search depends on it);
- a `--cottas-rebuild-compound` CLI flag that writes the file from
  scratch via the F\* per-column readers (Psi3 `rg_contains_token`)
  paired across the same row decode — a tighter dependency on already-
  trusted code.

When the broader writer migration phase happens, the F\* writer can
replace this OCaml producer without touching the reader API.

## 4. Reader integration — call sites

Two redirects, in order of rollout:

### 4a. `mem5_estimate_fast_inner` per-rg candidate test

Today (post Tet3 redirect, see
`docs/designissues/2026-04-26-tet3-redirect-estimate-fast-inner.md`)
this loop tests `could_p && could_s && could_o` via Psi3 per-column.

Compound additionally evaluates `compound_rg_passes_pair oh_compound rg
bound_p_id bound_o_id`. Skip if `compound = false`. The composed gate
is:

```
candidate_rg(rg) =
  PresenceBitmap.rg_passes_all rg oh_s bound_s oh_p bound_p oh_o bound_o
  && CompoundPresenceBitmap.compound_rg_passes_pair oh_compound rg bound_p bound_o
```

For Q03: compound returns `false` for all 26 rgs (no rg has the
`(rdf:type, geo:wktLiteral)` pair). Mem5 returns
`length(candidates) * (total / rg_count) = 0 * x = 0`. Planner sees
estimate=0 → short-circuits BGP eval → 0ms.

### 4b. `search_fast_inner` per-rg gate

Same composed gate; skip rg without column decode. For Q03 this saves
the 4 column decodes × 122 880 rows in rg=22 — the actual 4s cost.

### 4c. Fallback discipline

In each redirect call site:
```
if compound handle present and valid AND both p and o bound:
   gate := compound test  // strictly more selective
else:
   gate := Psi3 per-column composed (status quo post-Tet3 redirect)
```

This is still rule-#11(c) "trivial dispatch shim" — no decisions, just
"prefer the more selective bitmap when available". Logic in F\*
(`rg_passes_compound_and_per_column`).

## 5. Sequencing — when does compound work start

Acknowledging Phase 2.6 Tet3 redirect work in flight (commit `c99dc31`
landed redirect for `estimate_fast_inner`; `search_fast_inner` x2
gates and `search_fast_limited_inner` x1 gate still pending in
`cottas_ondisk_zzzzzzzzzzz_tet3_fstar_redirect_search.sh` per `git
status`).

### Recommended order

1. **Finish Tet3 redirect at all 3 remaining call sites.** Land the
   pending search redirect patch. This produces a proven integration
   shape (OCaml call-site -> F\* `rg_could_contain` -> companion mmap
   bytes) — exactly the shape we'll reuse for compound.

2. **Compound writer can start in parallel** with step 1, on a
   separate branch, because:
   - It produces a NEW companion file (`.po.presence`).
   - It does not modify any reader path.
   - It does not touch existing single-column `.presence` files or
     their writers/readers.
   - Result-set semantics are unaffected when nobody reads the new
     file.

   Specifically: the writer commit can land before any compound reader
   is wired up. The companion file just sits unused on disk. Cost is
   one extra column-pair walk at boot (mergeable with Tet3's existing
   per-rg walk at no additional pass).

3. **Compound F\* module + reader redirects come AFTER step 1.**
   Reasons:
   - The redirect-call-site patch shape mirrors the Tet3 shape; trying
     to skip ahead to compound integration before Tet3 redirect is
     stable risks two patches racing on the same anchor lines.
   - The compound module's correctness story builds on Psi3 (compound
     is `Psi3.rg_passes_all && CompoundPresenceBitmap.compound_pass`).
     With Psi3 already in production through the Tet3 redirect, the
     compound add is a strictly additive lemma.

4. **Phase ordering gates:**
   - **GATE 1:** Tet3-redirect-search lands → 4.2s Q03 unchanged
     (the gate is per-column, doesn't see compound absence — same as
     today, just routed through F\*).
   - **GATE 2:** Compound writer ships, file present → still no
     reader → still 4.2s. Confirms write path benign.
   - **GATE 3:** Compound F\* module + reader redirect ships → Q03
     drops to <50ms.

Each gate is one commit-sized step (rule #23). Total: ~3 commits
post-Tet3-redirect-search.

### Parallelisation

Steps 1, 2, and the F\* module body of step 3 can all be developed
simultaneously by separate agents:
- Agent A: Tet3 redirect search (in flight)
- Agent B: Compound writer (parallel, independent)
- Agent C: F\* `CompoundPresenceBitmap.fst` module (parallel,
  doesn't depend on either A or B until reader-redirect patch ships)

The reader-redirect patch (final commit) requires A + B + C all done.

## 6. Risks / open questions

### 6a. Sparse-roaring degeneracy on dense rgs

If a future corpus has a row group where `(p, o)` distinct pairs
approach `pred_dict_size × obj_dict_size`, sparse-roaring's per-rg
size approaches the flat-2D size we ruled out. Mitigation: when
writing, if `npairs > pred_dict_size * obj_dict_size / 16`, switch
that rg's encoding to a per-rg flat bitmap and tag with
`enc_per_rg_flat = 3`. The header carries a per-rg encoding hint as
the high bit of `npairs`. This adds one branch in the reader's
sparse-or-flat dispatch. **Open:** is this worth doing now, or defer
until we see a corpus that triggers it? Recommend: document the
header reservation but ship a single encoding (sparse_roaring) for
parliament-class corpora.

### 6b. Token-id namespace contract with Vav3

The compound bitmap's `(p_id, o_id)` MUST live in the same token-id
namespace as the existing `.p.presence` and `.o.presence` companions.
That namespace is defined by Vav3's bulk-load step (sorted-dictionary
position is the token id, see `OnDiskIndex.fst:33-37`). The contract
to document:
- Compound writer reads token ids through the SAME
  `dict_encode_token` path the per-column writer uses.
- Header invariants (Section 1b) cross-check `pred_dict_size` and
  `obj_dict_size` against the per-column presence files. If either
  mismatches, the compound bitmap is treated as absent.

If Vav3 ever rebuilds the dictionary (e.g. a corpus reload), the
compound file MUST be rebuilt too. The `--cottas-rebuild-compound`
flag (Section 3) is the manual escape hatch; the boot-path detection
of "dict size disagrees with compound header" is the automatic one.

### 6c. Bloom false-positive rate vs space (fallback path)

If sparse-roaring is rejected and Bloom is the chosen encoding:
- m=256 KB, k=4, with ~100 K distinct pairs/rg: false-positive rate
  ≈ (1 - e^{-k n / m})^k ≈ (1 - e^{-4·100K / 2M})^4 ≈ 0.04^4 ≈ 2.6e-6.
- For Q03 specifically: rg=22 has ~120 K distinct pairs; the
  `(rdf:type, geo:wktLiteral)` query has 1-in-2.6e-6 chance of
  false-positive. Acceptable, but exact is strictly better.
- **Open:** if compound goes Bloom in deployment for any reason, do
  we trade off `m_bits` for known-corpus calibration?

### 6d. Producer-side proof — `compound_built_correctly`

Section 2a's lemma is statement-only; the producer-side proof
that the on-disk file actually satisfies the predicate is delegated
to the writer. With the writer in OCaml (Section 3), the proof is
informal ("enumerate all `(p_id, o_id)` for every row in rg"). A
future writer-side F\* port closes this rigorously. **Open:** is the
informal argument enough for the rule-#11 rationale, or do we need
a runtime self-check at first open ("decode 100 rows, verify their
`(p, o)` is in the bitmap")? Recommend: lightweight self-check at
debug log level only.

### 6e. Memory cost on hot path

Per-rg sparse-roaring lookups: binary search ~log2(100 K) = 17 reads
each, each a u64 read of a `(u32, u32)` cell. mmap'd, no allocations.
For a typical query touching 26 rgs, lookups = 26 × 17 = 442 reads,
all sequential-ish in mmap'd page. Well within budget. No risk.

### 6f. Interaction with offset index (Lamed3)

Compound bitmap and Lamed3's per-rg predicate-row-offset index
overlap conceptually: both prune at `(rg, predicate)` granularity
(Lamed3 per-pred, compound per-(p,o)). Compound is strictly more
selective. **Open:** does landing compound make Lamed3 redundant?
Probably not — Lamed3 also delivers row-position offsets for fast
column slicing, not just presence. Document explicitly that compound
is for prune-decisions only; Lamed3 (per Phase 2.6 plan) remains the
row-position-locator. The two compose: compound says "this rg
matters" → Lamed3 says "rows N..M in this rg are the ones to decode".

## Acceptance test

When implemented, this design's success is measured by:

1. F\* `RDF.CottasStore.CompoundPresenceBitmap.fst` verifies clean (no
   `--lax`).
2. `compound_built_correctly` lemma verifies (statement-level; producer
   gap explicitly documented).
3. Writer produces deterministic `.po.presence` byte-identical for
   identical input corpus (Vav3-style discipline).
4. Q03 wall-time drops from 4.2s to <50ms on parliament demo.
5. W3C suite unchanged (1657/1/0/4).
6. RSS does not regress (compound is read via mmap; no new heap
   allocations on hot path).

## References

- Issue #104: `https://github.com/danbri/factoidal/issues/104`
- Psi3 module: `formal/fstar/RDF.CottasStore.PresenceBitmap.fst`
- Vav3 / OnDiskIndex: `formal/fstar/RDF.CottasStore.OnDiskIndex.fst`
- Tet3 OCaml-side per-column writer:
  `formal/fstar/experimental_ocaml_glue/cottas_ondisk_zzzz_tet3_subj_obj_prune.sh`
- Tet3 redirect (estimate_fast_inner) scratch:
  `docs/designissues/2026-04-26-tet3-redirect-estimate-fast-inner.md`
- Phase 2.6 plan: `docs/designissues/fstar-purity-unwind.md`
