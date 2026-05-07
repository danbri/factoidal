# Pure F\* Roaring implementation — phased plan

Status: **plan + first cut**. This document accompanies the
work-in-progress at `formal/roaring/src/`. Companion to
[`roaring_parquet_notes.md`](roaring_parquet_notes.md) (broader
design space) and [`virtual_ngs.md`](virtual_ngs.md) (one of the
target consumers).

Date: 2026-05-06.

> The point of this plan is to slice the work into commit-sized
> goals, each producing a concrete deliverable that can be verified
> and tested independently. Per the project's anti-pattern #23
> (one subagent = one commit = one deliverable), each phase below
> is a candidate single-PR scope.

---

## 1. Goals

A pure F\* Roaring bitmap implementation, designed for use with the
existing RDF/SPARQL + COTTAS/Parquet stack, that:

- Specifies the data structure formally (denotation = `Set u32`).
- Implements the three container types (array, bitmap, run) with
  invariants pinned in refinement types.
- Implements set algebra (AND, OR, XOR, ANDNOT) with correctness
  lemmas against the denotation.
- Implements the portable on-disk format so files round-trip with
  Java/Rust/C reference implementations.
- Extracts to OCaml (the project's primary target) via
  `--codegen OCaml` without `--lax`, per iron rule #1.
- Treats SIMD / `popcount` / file I/O as `assume val`s realised in
  glue per iron rule #3.

Non-goals for the first cut:

- Roaring64 (any flavour). The `roaring_parquet_notes.md` §7
  decision is deliberately deferred; we build 32-bit first.
- KaRaMeL / C extraction. OCaml only initially. (The `noeq` choice
  on container types affects this; flagged in §6.)
- SIMD vectorisation. Pure F\* implementations of AND/OR/popcount
  for now. The vectorised path is a follow-up that lives in glue.
- Wiring into `RDF.CottasStore.PresenceBitmap.fst` to replace the
  dense companion. That's a separate design conversation; this
  module just exists alongside as a candidate.

---

## 2. Scope of the first cut (this PR series)

Implement `formal/roaring/src/`:

```
Spec.fst                  abstract set + helpers
Container.Array.fst       sorted u16[] container
Container.Bitmap.fst      fixed-size u64[1024] container
Container.Run.fst         sorted (start, length-1) pairs
Container.fst             sum type, per-container ops
Roaring.fst               top-level (sorted assoc list of containers)
Test.fst                  F* assertions + lemmas as unit tests
```

This is *just* the in-memory data structure with insert/remove/
contains/cardinality/union/intersection. Serialization, range ops,
rank/select, and the wire format come later.

---

## 3. Why this layout

Mirrors the existing project structure. `RDF.Graph.Executable.fst`
and `SPARQL11.Algebra.fst` are flat single files; a multi-file
layout is justified here because:

- Each container type has independent invariants and proofs.
- The three container types have separate per-pair op routines
  (six pairs × four ops = ~24 routines).
- Test cases naturally split per-container.
- Splitting reduces rebuild churn during iteration.

---

## 4. Phased deliverables

### Phase A — types and denotation (this PR)

- `Spec.fst`:
  - `type roaring_set = nat -> bool` (abstract Set u32 denoted as a
    boolean predicate over `nat` values bounded by 2^32). Avoids
    pulling in any runtime data structure for the spec.
  - `valid_u32 : nat -> bool`.
  - `subset`, `equiv`, `intersection_set`, `union_set` (pure spec
    operations on the abstract sets).
  - `singleton_set`, `empty_set`.

- `Container.Array.fst`:
  - `array_container` refinement type: `Seq` or `list` of `nat`
    representing low-16 values, sorted strict, length ≤ 4096, all
    values < 65536.
  - `denote_array : array_container -> u16 -> bool`.
  - `array_empty`, `array_singleton`, `array_contains`,
    `array_insert`, `array_remove`, `array_cardinality`.
  - Lemmas: `denote_after_insert`, `denote_after_remove`,
    `cardinality_correct`.

- `Test.fst`:
  - `assert_norm` checks for empty/singleton/insert/remove on
    array container.
  - A few lemma tests demonstrating denotation equivalence.

**Definition of done:** `make verify` passes for the Phase A
modules; `Test.fst` compiles and the assertions hold under the
F\* normalizer.

### Phase B — bitmap container (next PR)

- `Container.Bitmap.fst`:
  - `bitmap_container` refinement type: `seq u64` of length 1024
    plus cardinality field, with invariant
    `cardinality = sum of popcounts`.
  - `denote_bitmap`, `bitmap_contains`, `bitmap_insert`,
    `bitmap_remove`, `bitmap_cardinality`.
  - `assume val popcount_u64 : u64 -> n:nat{n <= 64}` realised in
    glue.
  - Lemmas tying popcount to denotation.

### Phase C — run container (next PR)

- `Container.Run.fst`:
  - `run_container`: `list (start, length-1)`, runs sorted and
    non-adjacent.
  - Standard ops + cardinality computed on-the-fly (paper §4 says
    run containers don't cache it at runtime).
  - The "single-run-spans-whole-chunk" optimisation as a separate
    predicate.

### Phase D — container sum type (next PR)

- `Container.fst`:
  - `type container = | A of array | B of bitmap | R of run`.
  - Promotion / demotion functions with correctness:
    - `array_to_bitmap`, `bitmap_to_array` (when card ≤ 4096),
    - `array_to_run`, `bitmap_to_run`, `run_to_array`,
      `run_to_bitmap`, with the canonical-form predicates from
      paper §4.
  - `denote_container : container -> u16 -> bool`.

### Phase E — top-level Roaring (next PR)

- `Roaring.fst`:
  - `roaring`: sorted assoc `list (u16 * container)`.
  - `roaring_contains`, `roaring_insert`, `roaring_remove`,
    `roaring_cardinality`.
  - `denote_roaring : roaring -> u32 -> bool`.
  - High-16/low-16 splitting helpers.
  - Top-level lemmas tying the high-16 split to the abstract set.

### Phase F — set algebra (multiple PRs likely)

- `Container.Ops.fst` (or per-pair files):
  - 6 × 4 = 24 per-pair routines. Practically these split as:
    - AND, OR, XOR, ANDNOT for each of 6 unordered pairs.
  - Each gets a correctness lemma: `denote (op a b) = op_set
    (denote a) (denote b)`.
- `Roaring.Ops.fst`:
  - Top-level `union`, `intersect`, `xor`, `andnot` walking the
    sorted directory.
  - Lazy-union pattern (paper §5.1): defer cardinality
    computation, repair at end. Equivalence lemma vs strict.

### Phase G — algorithms (separate PR each)

The three named algorithms from paper §4:

- **Algorithm 1: count runs in a bitmap.** With short-circuit at
  2047. Used to decide bitmap → run conversion.
- **Algorithm 2: extract runs from a bitmap.** Uses `tzcnt` (as an
  `assume val`).
- **Algorithm 3: set/clear a range of bits in a bitmap.** Mask
  construction + inner loop.

Each gets its own correctness lemma against the abstract set.

### Phase H — portable serialization (later)

- `Roaring.Serialize.fst`:
  - Cookie 0x3BC0 (no-run variant) and 0x3BF0 (with-run variant).
  - Directory layout per `RoaringFormatSpec`.
  - Round-trip lemma: `decode (encode r) == Some r` for canonical
    `r`.
  - Cross-impl conformance test corpus (golden files from Java
    upstream).

### Phase I — extraction and OCaml wiring (later)

- Add `RoaringBitmap` to `MODULES` in `formal/fstar/Makefile`.
- Patches to OCaml output for `assume val`s
  (`popcount_u64`, `tzcnt_u64`, file I/O) — same shape as existing
  `ocaml-patches.sh` work, listed in
  `minimal_regrettable_glue_code_each_with_an_open_issue/` with an
  issue number per iron rule #3.

### Phase J — SPARQL / COTTAS integration (later, separate plan)

- `RDF.CottasStore.PresenceBitmap` swap to Roaring (smallest
  blast radius — see `roaring_parquet_notes.md` §6.1).
- New row-level posting layer (§6.2 of that doc).
- The four `term-id → roaring(rowID)` indexes, with the
  correctness lemmas sketched in `roaring_parquet_notes.md` §10.

---

## 5. Test strategy

Three test layers, in order of cost:

### 5.1 F\* `assert_norm` checks

Cheapest. Compile-time evaluation of small concrete cases. Catches
misencoded literals and obvious off-by-ones. Examples:

```fstar
let _ = assert_norm (array_contains array_empty 42 = false)
let _ = assert_norm (array_contains (array_insert array_empty 42) 42 = true)
let _ = assert_norm (array_cardinality (array_insert array_empty 42) = 1)
```

### 5.2 F\* lemmas (proofs, not tests)

The bulk of correctness. Examples:

```fstar
val insert_correct (c : array_container) (x : u16) :
  Lemma (forall y. denote_array (array_insert c x) y =
                   (y = x || denote_array c y))

val union_correct (a b : roaring) :
  Lemma (forall x. denote_roaring (roaring_union a b) x =
                   (denote_roaring a x || denote_roaring b x))
```

These run during `make verify`. They *are* the spec; they aren't
runnable tests in the dynamic sense, but they're enforced by F\*.

### 5.3 Extracted-OCaml runtime tests (later)

Once Phase I lands, run the extracted code against:

- A corpus of randomly-generated bitmaps (fuzz-style).
- Round-trip property: `decode (encode r) = r`.
- Cross-impl conformance: read files written by the Java reference
  implementation.

Lives in `tests/roaring/` as a separate harness, similar to the
existing `tests/` patterns in this repo.

---

## 6. Known F\* gotchas to watch for

From CLAUDE.md and project experience:

- **`(*` and `*)` inside comments.** Reserve `//` line comments
  for any text containing parens-stars.
- **Reserved-word identifiers.** `total`, `in_mem`, anything
  beginning with `in` in a let-body context. Use domain-prefix
  names: `runs_total` not `total`.
- **`noeq` blocks KaRaMeL.** OCaml extraction works fine. If we
  ever target C, we'll need to re-engineer the container types.
- **`--lax` is banned.** Every module must verify cleanly.
- **z3 must be 4.13.3.** Missing-or-wrong-version z3 silently
  burns time.
- **Patch discipline.** `assume val`s extract to `failwith "Not
  yet implemented"` and need a sibling stub in
  `minimal_regrettable_glue_code_each_with_an_open_issue/` per
  iron rule #3.

---

## 7. Verification environment

The project assumes `eval $(opam env --switch=fstar)` is active
before any F\* invocation. The first PR (Phase A) verifies in
isolation given that env; subsequent phases have no additional
dependencies until Phase H (which needs file I/O glue) and Phase I
(which needs the existing OCaml extraction pipeline).

This file's author may not have a working F\* env locally; the F\*
modules are written *to verify* against the project's standard
toolchain, not necessarily to be verified at write time. Each PR
should be checked by running `make verify` in `formal/fstar/` (once
the modules are wired in) before merge.

---

## 8. Sequencing — what to do first

1. Phase A as one PR. Land it small. Verify it.
2. Phase B as one PR. Land it.
3. Phase C as one PR. Land it.
4. Phase D and E together — they're tightly coupled.
5. Phase F as a series of small PRs (one or two pairs at a time).
6. Phase G as three small PRs.
7. Phase H as one PR. Big but self-contained.
8. Phase I as one PR. Touches the build.
9. Phase J — separate design conversation, not part of this plan.

A — D should be doable in ~1 person-week of focused work each.
F — H are bigger; F especially is repetitive (24 routines, 24
lemmas).

---

## 9. What this PR (the one starting now) lands

- This plan document.
- `formal/roaring/src/Spec.fst` — Phase A spec layer.
- `formal/roaring/src/Container.Array.fst` — Phase A
  array container.
- `formal/roaring/src/Test.fst` — Phase A unit tests
  as `assert_norm` checks plus a couple of lemmas.
- `formal/roaring/Makefile` — verify/clean targets,
  not yet wired into the main `formal/fstar/` build.
- A README in the source directory pointing at this plan.

Defer:
- Bitmap container (Phase B).
- Run container (Phase C).
- Set algebra (Phase F).
- Anything past Phase A.

---

## 10. Open questions for this PR series

- **`Seq` vs `list` for container backing.** `Seq` has better
  refinement-type ergonomics for "sorted strict" predicates; `list`
  is what `RDF.Graph.Executable.fst` uses. House style suggests
  `list`; we'll start with `list` and revisit if proofs get hairy.
- **`u16` representation.** Use `nat` with refinement
  (`x:nat{x < 65536}`) for spec; switch to `FStar.UInt16.t` only
  if/when extraction needs the unboxed representation. Same for
  `u32`, `u64`.
- **Where to put the implementation long-term.** `experimental/`
  for now, `formal/fstar/RoaringBitmap.*.fst` once it stabilises.
  Probably move at Phase E.
- **Patches discipline.** No `assume val` in Phase A — it's pure
  data structures. Phase B introduces the first one
  (`popcount_u64`); from then on we follow the issue-numbered
  patch convention.

---

## 11. Revision history

- **2026-05-06**: First version. Phase A scope drafted; later
  phases sketched.
