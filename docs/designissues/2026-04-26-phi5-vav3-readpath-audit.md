# Phi5 audit: Vav3 mmap'd companion-file READ path verification

**Status:** complete (audit only; no code changes).
**Phase:** 2.3 of `docs/designissues/fstar-purity-unwind.md`.
**Base commit:** 48cdf53.
**Author:** Phi5 (subagent), 2026-04-26.

## Goal

Verify that Vav3's mmap'd companion-file READ path actually goes through
F\* `RDF.CottasStore.OnDiskIndex.fst` and not through duplicate OCaml
glue. Identify duplicates as candidates for Phase 2.6 (do NOT fix yet).

## Method

For each function in the patch `cottas_ondisk_zzzzz_ondisk_index.sh`
(885 LoC including pyembed scaffolding) and the resulting two appended
modules in extracted `RDF_CottasStore.ml`, classify as:

- **WRITER** — builds `.dict`/`.presence` companion files at boot. Pure
  byte-emit + Buffer/Bytes/Sys.rename I/O. Acceptable per rule #15.
- **F\*-DELEGATING READER** — thin wrapper that calls F\*
  `RDF_CottasStore_OnDiskIndex.{dict_decode_token, dict_encode_token,
  presence_test_bit, companion_encode, companion_decode,
  companion_rg_could_contain, read_dict_header, read_presence_header,
  dict_header_ok, presence_header_ok}`.
- **DUPLICATE READER** — parallel implementation in OCaml that doesn't
  call F\*. Rule-#11 violation candidate.
- **I/O PRIMITIVE GLUE** — `Vav3_mmap` byte-range readers backing
  `assume val` declarations. Acceptable per rule #15 ("never decides
  what bytes mean — only how to read them").

## Files audited

| File | LoC | Role |
|---|---:|---|
| `cottas_ondisk_zzzzz_ondisk_index.sh` (the patch script) | 885 | Combined writer + reader + boot patch |
| `RDF_CottasStore_OnDiskIndex.ml` (post-extract + Vav3 patch) | 463 | F\* OnDiskIndex extracted + Vav3_mmap I/O glue |
| `RDF_CottasStore.ml` (post-extract + Vav3 patch) | 3387 | Has `Cottas_ondisk_lazy`, `Cottas_offset_idx`, `Cottas_ondisk_runtime`, `Cottas_companion_writer`, `Cottas_companion_boot` |

The patch adds three things: (a) impls for the 6 `assume val` mmap I/O
primitives in OnDiskIndex.ml; (b) `Cottas_companion_writer` (writer);
(c) `Cottas_companion_boot` (orchestrator + bulk-load).

## Per-function classification table

### `Vav3_mmap` module in `RDF_CottasStore_OnDiskIndex.ml` (~125 LoC)

| Function | Lines | Class | Notes |
|---|---:|---|---|
| `Vav3_mmap.try_open_mmap` | ~20 | I/O PRIMITIVE GLUE | Backs `assume val mmap_companion_open`. Pure byte-mapping; no semantics. |
| `Vav3_mmap.close_mmap` | ~5 | I/O PRIMITIVE GLUE | Backs `assume val mmap_companion_close`. |
| `Vav3_mmap.view_for` | ~7 | I/O PRIMITIVE GLUE | Lazy mmap helper. |
| `Vav3_mmap.read_byte_int` | ~6 | I/O PRIMITIVE GLUE | Backs `assume val read_companion_byte`. |
| `Vav3_mmap.read_u32_le_int` | ~10 | I/O PRIMITIVE GLUE | Backs `assume val read_companion_u32_le`. Pure little-endian byte assembly. |
| `Vav3_mmap.read_u64_le_int` | ~18 | I/O PRIMITIVE GLUE | Backs `assume val read_companion_u64_le`. Same. |
| `Vav3_mmap.read_string` | ~12 | I/O PRIMITIVE GLUE | Backs `assume val read_companion_string`. Byte-range copy. |
| `Vav3_mmap.file_size` | ~6 | I/O PRIMITIVE GLUE | Backs `assume val companion_file_size`. |
| Wrapper `let mmap_companion_open = ...` (etc, 6 of them) | ~30 | I/O PRIMITIVE GLUE | Boxes `option pint` to `FStar_Pervasives_Native.option Z.t`. |

**Verdict:** `Vav3_mmap` is fully rule-#15 conformant. Pure byte-range I/O backing the F\* `assume val` layer.

### `Cottas_companion_writer` module in `RDF_CottasStore.ml` (lines 2946–3128, 183 LoC)

| Function | Lines | Class | Notes |
|---|---:|---|---|
| `column_suffix`, `dict_path`, `presence_path` | ~10 | WRITER | Path string builders. |
| `write_u32_le`, `write_u64_le` | ~10 | WRITER | Byte-emit helpers. |
| `collect_distinct_per_rg` | ~30 | WRITER | Walks parquet via `Parquet_Footer.probe_parquet_column_decode_in_row_group`. Builds Hashtbl sets. Pure I/O accumulation. |
| `atomic_write` | ~7 | WRITER | open/write/fsync/rename. |
| `write_dict_file` | ~37 | WRITER | Layout-defined byte emit. Format spec is in F\* (`RDF.CottasStore.OnDiskIndex.fst`); writer just respects it. Acceptable. |
| `write_presence_file` | ~31 | WRITER | Same. Bit-packing matches F\* `presence_test_bit`'s convention (LSB-first within byte). |
| `build_companion_pair` | ~18 | WRITER | Orchestrator: collect → write_dict → write_presence. |

**Verdict:** entire module is WRITER — acceptable I/O glue per rule #15. Per rule #15 the file FORMAT is fully F\*-defined; writer just emits per spec.

**Caveat:** `write_dict_file` hard-codes `dict_magic = 0x44544f43` and `layout_version = 1` as plain OCaml constants rather than reusing F\* `cotd_magic_u32`. Cosmetic; not a logic violation. Two-source-of-truth risk if F\* layout version bumps (the writer would silently lag).

### `Cottas_companion_boot` module in `RDF_CottasStore.ml` (lines 3135–3387, 253 LoC)

| Function | Lines | Class | Notes |
|---|---:|---|---|
| `companions_present_and_valid` | ~25 | F\*-DELEGATING READER | Calls `RDF_CottasStore_OnDiskIndex.read_dict_header` / `read_presence_header` / `dict_header_ok` / `presence_header_ok`. Header-validation path goes through F\*. |
| `build_all_companions` | ~10 | WRITER | Loops `build_companion_pair` 4 times. |
| `bulk_load_column_into_tables` (step 1: dict walk) | ~50 | **DUPLICATE READER** | Calls `RDF_CottasStore_OnDiskIndex.read_dict_header` for header (delegates), then INLINES a u64 LE reader and a `read_token` (id → string) function via `Bigarray.Array1.unsafe_get` directly. **Reimplements `dict_decode_token` byte-for-byte in OCaml**, with the comment "this is a perf shim". (Lines 3214–3254.) |
| `bulk_load_column_into_tables` (step 2: presence walk) | ~35 | **DUPLICATE READER** | Walks the presence bitmap with direct `Bigarray.Array1.unsafe_get` byte-and-bit-test. **Reimplements `presence_test_bit`** with a whole-byte zero-skip optimisation. Comment admits it: "The F\* spec `presence_test_bit` is byte-identical to this walk; we skip the per-bit F\* dispatch for boot speed." (Lines 3315–3348.) |
| `bulk_load_column_into_tables` (parse step) | ~40 | **F\*-OUT-OF-SCOPE-LOGIC** | After bulk-load, calls `Cottas_ondisk_runtime.parse_iri_token` for predicates+graphs (eager) but skips subjects+objects for lazy parse (Vav3's optimization). The "lazy decode-fast cache miss" patch (Step C of the patch script) inlines additional fallback logic in `decode_subject_fast` / `decode_object_fast`. The decision of when to eager-parse vs lazy-parse is a policy choice that lives in OCaml, not F\*. Borderline — leans WRITER-side because it only populates Hashtbls — but the eager/lazy split is semantic. |
| `prewarm_via_companions` | ~30 | WRITER + DUPLICATE-READER orchestrator | Top-level boot entry. Calls `companions_present_and_valid`; on miss, builds companions; then calls `bulk_load_column_into_tables` (the duplicate-reader); then calls `Cottas_ondisk_lazy.mark_*_loaded` and `Cottas_offset_idx.ensure_offsets_built`. |

**Plus the in-file decode-fast cache-miss patches (Step C of the patch
script), applied to `Cottas_ondisk_runtime.decode_subject_fast` and
`decode_object_fast` (~15 LoC each):** these add a fallback path "on
cache miss, look up raw token via `ft_id_to_subj_tok` and parse via
`parse_subject_str`". The token mapping source is the bulk-loaded
Hashtbl; the parse helper is `Cottas_ondisk_runtime.parse_subject_str`
(which lives in `Cottas_ondisk_runtime`, not OnDiskIndex). Not strictly
a duplicate of an OnDiskIndex function, but is policy that defers
decode work — a semantic decision in OCaml.

### `Cottas_ondisk_lazy` module (lines 252–374, 123 LoC) — pre-existing, populated by Vav3

This module pre-dated Vav3 (it's Yod6/Tet3) but Vav3's bulk-load
**populates** its Hashtbls. Critically, the runtime query path
(`pred_rg_could_contain`, `subj_rg_could_contain`, `obj_rg_could_contain`)
still consults THESE Hashtbls — NOT the F\*-extracted
`presence_test_bit` / `companion_rg_could_contain`. Confirmed by grep:

```
$ grep -n 'pred_rg_could_contain\|subj_rg_could_contain\|obj_rg_could_contain' RDF_CottasStore.ml
1380, 1472, 1559, 1692, 1771, 1903 — all call Cottas_ondisk_lazy.*
```

| Function | Lines | Class | Notes |
|---|---:|---|---|
| `pred_rg_could_contain` | ~12 | **DUPLICATE READER** | OCaml-pure Hashtbl-based; does the same job as F\* `companion_rg_could_contain` / `presence_test_bit`. |
| `subj_rg_could_contain` | ~12 | **DUPLICATE READER** | Same. |
| `obj_rg_could_contain` | ~12 | **DUPLICATE READER** | Same. |
| `pred_presence_by_path`, `subj_presence_by_path`, `obj_presence_by_path` (Hashtbls) | ~30 | DATA STRUCTURE | The duplicated state. |
| `presence_for_path`, `subj_presence_for_path`, `obj_presence_for_path` | ~30 | DATA STRUCTURE | Per-path lazy-init helpers. |
| `mark_*_loaded` family (called from boot) | ~20 | DATA STRUCTURE | Marks columns loaded so legacy lazy-populator (Bet7) skips. |

**Verdict:** the module is technically Yod6/Tet3 turf (and is on the
Phase 2.6 list per the unwind doc), but Vav3 leans on it: bulk-load
writes here. Once Phase 2.6 lifts presence-test to F\*-pure
`companion_rg_could_contain`, this entire module disappears.

## Concrete LoC counts

| Class | LoC | Notes |
|---|---:|---|
| WRITER | ~190 | `Cottas_companion_writer` (183) + `build_all_companions` (10) — acceptable per rule #15. |
| F\*-DELEGATING READER | ~25 | `companions_present_and_valid` (header-validation only) + `Cottas_offset_idx.ensure_offsets_built` lines 635/642/655 (3 call sites of F\* readers). |
| I/O PRIMITIVE GLUE | ~125 | `Vav3_mmap` module backing the 6 `assume val` declarations. Acceptable per rule #15. |
| **DUPLICATE READER (Vav3-introduced)** | **~85** | `bulk_load_column_into_tables` step 1 dict-walk (~50) + step 2 presence-walk (~35), each explicitly re-implementing F\* logic for "boot speed". |
| **DUPLICATE READER (pre-existing, Yod6/Tet3)** | **~60** | `Cottas_ondisk_lazy.{pred,subj,obj}_rg_could_contain` (~36) + presence Hashtbl wiring (~24). |
| Decode-fast cache-miss policy (Step C patch) | ~30 | Lazy-parse fallback in `decode_subject_fast` / `decode_object_fast`. |

**Total Vav3-attributable duplicate-reader LoC: ~85.**
**Total pre-existing duplicate-reader LoC consumed by Vav3 bulk-load population: ~60.**

## F\* OnDiskIndex callers vs dead code

I grep'd every `RDF_CottasStore_OnDiskIndex.<symbol>` call site in
`ocaml-output/`. Result:

| F\* symbol | Production callers | Status |
|---|---|---|
| `read_dict_header` | 4 sites (lines 635, 3152, 3199 in RDF_CottasStore.ml; plus internal use by other F\* fns) | LIVE — header-validation path. |
| `read_presence_header` | 3 sites (lines 642, 3153, 3200) | LIVE — same. |
| `dict_header_ok`, `presence_header_ok` | 1 site (line 3156–3157) | LIVE — header-validation only. |
| `dict_decode_token` | 1 site (line 655 in `Cottas_offset_idx.ensure_offsets_built`) | LIVE but only at offsets-build time; bulk-load inlines its own. |
| `dict_encode_token` | **0 sites** | **DEAD**. Runtime path uses `ft_*_tok_to_id` Hashtbls. |
| `read_id_at`, `bsearch_loop` | only via `dict_encode_token` | **DEAD**. |
| `presence_test_bit` | **0 sites** | **DEAD**. Runtime path uses `Cottas_ondisk_lazy.{pred,subj,obj}_rg_could_contain` Hashtbls. |
| `companion_encode` | **0 sites** | **DEAD**. |
| `companion_decode` | **0 sites** | **DEAD**. |
| `companion_rg_could_contain` | **0 sites** | **DEAD**. |
| `companion_status_ok`, `load_companion_status` | **0 sites** | **DEAD**. |

The high-level `companion_*` API (the layer the F\* module designs as
the runtime entry point) has **zero production callers**. The mid-level
`{dict,presence}_{encode,test}` functions are dead. Only the
header-validation reader and `dict_decode_token` (at offsets-build
time) escape death.

**This is the central finding of this audit.** The F\* OnDiskIndex
module is well-structured, fully verified, and almost entirely unused
at runtime — the OCaml glue duplicates its semantic readers.

## Recommendations for Phase 2.6 (in priority order)

### Top 3 duplicate-reader candidates by LoC

1. **`Cottas_companion_boot.bulk_load_column_into_tables`** (~85 LoC of
   duplicate). Rip out the inlined `read_u64`/`read_token` and the
   inlined byte-walk presence loop; replace with calls to F\*
   `dict_decode_token` and `presence_test_bit`. Simplest unwind.

2. **`Cottas_ondisk_lazy.{pred,subj,obj}_rg_could_contain`** (~36 LoC
   of duplicate). The runtime query path is the high-leverage win:
   redirect to `RDF_CottasStore_OnDiskIndex.companion_rg_could_contain`
   instead of consulting `pred_presence_by_path` Hashtbls. Once this
   lands, the entire `Cottas_ondisk_lazy` presence-Hashtbl machinery
   (~123 LoC) can be deleted, AND the Vav3 bulk-load step 2 (~35 LoC)
   becomes obsolete (no Hashtbl to populate).

3. **`Cottas_ondisk_runtime.ft_*_tok_to_id` lookups in
   `cottas_ondisk_search` / `_estimate`** (call sites at lines
   1068–1071, 1115, 1163, 1211, ~5 LoC per site × N sites). Redirect
   to `RDF_CottasStore_OnDiskIndex.companion_encode`. This is the
   biggest win for surface area: it makes `dict_encode_token` /
   `bsearch_loop` / `read_id_at` LIVE rather than dead F\* code.

### Sequencing

- **Recommendation 2 first** (presence). Smallest surface, widest
  collapse: consolidates Yod6/Tet3 + the Vav3 bulk-load step 2
  in one stroke.
- **Recommendation 3 second** (encode). Touches the runtime hot
  loop (`cottas_ondisk_search`); per the unwind doc Phase 2.5a
  warns this may surface a perf cliff. Profile before+after.
- **Recommendation 1 last** (bulk-load decode). Once 2 and 3 land,
  the `bulk_load_column_into_tables` function may not need to
  populate `ft_*_tok_to_id` at all — query path reads the dict via
  F\* `companion_encode` directly. The function shrinks to nothing
  or becomes a no-op.

### What stays as glue

- All of `Vav3_mmap` (I/O primitives backing `assume val`).
- All of `Cottas_companion_writer` (writer per rule #15 / #3).
- `companions_present_and_valid` (already a thin F\*-delegating wrapper).
- Most of `prewarm_via_companions` minus the bulk-load call.

## Honest gaps + surprises

1. **The F\* `companion_*` API is dead code at runtime.** This was
   not previously called out in the unwind doc Phase 2.3 description,
   which estimated "no LoC change expected". In fact: ~85 LoC of
   Vav3-introduced duplicates plus ~60 LoC of pre-existing Yod6/Tet3
   duplicates that Vav3 leans on. Phase 2.3's "verify the read path"
   action item should be re-scoped to "design Phase 2.6's redirect
   path before deleting any code."

2. **Comments admit the duplication explicitly.** The boot module
   has comments like "this is a perf shim" and "we skip the per-bit
   F\* dispatch for boot speed". The author knew it was a duplicate
   and labelled the future fix ("in a follow-on phase the _fast
   functions will consult the mmap'd companions directly via
   companion_encode/companion_decode/companion_rg_could_contain").
   **That follow-on phase IS Phase 2.6.** Useful provenance.

3. **`dict_encode_token` (binary search) is the most-buried dead
   code.** It's the only nontrivial algorithmic content in the F\*
   module (recursive `bsearch_loop` with explicit fuel/decreases). It
   has zero callers. The OCaml Hashtbl-based lookup is constant-time
   vs O(log n), so a naive port would regress perf — Phase 2.5a /
   2.6 will need a perf-conscious approach (perhaps mmap-direct
   binary search with whole-string comparator).

4. **`dict_decode_token` is the only borderline-live F\* function.**
   It's called once at offsets-build time (Cottas_offset_idx, line
   655). Its other "duplicate" (the inlined `read_token` in bulk-load)
   exists for performance, not necessity — the F\* version is correct.

5. **Step C of the patch is not really "Vav3 read-path" but
   "lazy-parse policy".** It edits `decode_subject_fast` /
   `decode_object_fast` to add a cache-miss fallback. This is OCaml
   policy that doesn't have an F\* equivalent today and probably
   shouldn't (the eager-vs-lazy decision is a perf concern, not a
   semantic one). Out of scope for Phase 2.6.

6. **Hard-coded magic constants in the writer.** `Cottas_companion_writer`
   hard-codes `dict_magic = 0x44544f43` and `layout_version = 1` rather
   than referencing `RDF_CottasStore_OnDiskIndex.cotd_magic_u32`. Two
   sources of truth → silent skew risk if F\* layout bumps. Cosmetic
   fix candidate during Phase 2.6 cleanup.

## Conclusion

Vav3's mmap'd companion-file READ path **partially** goes through F\*
`RDF.CottasStore.OnDiskIndex.fst`:

- **Header validation:** YES, F\*-delegating (`read_dict_header`,
  `read_presence_header`, `*_header_ok`).
- **Boot-time dict scan + presence scan:** NO, ~85 LoC of duplicate
  OCaml in `bulk_load_column_into_tables` (commented-acknowledged).
- **Runtime query path (encode + presence-test):** NO, fully
  duplicated in OCaml — `Cottas_ondisk_lazy.*_rg_could_contain` and
  `Cottas_ondisk_runtime.ft_*_tok_to_id` Hashtbls are the runtime
  reality; the F\* `companion_*` API has zero callers.

Phase 2.6 should be re-scoped from "verify reader path" to "redirect
runtime callers to F\* `companion_*` API; delete the duplicate Hashtbls
and the bulk-load inline reads; profile for Phase 2.5a-style perf
regressions." Estimated LoC retired: **~145** (85 Vav3 + 60 Yod6/Tet3
direct, with the supporting Hashtbl scaffolding in `Cottas_ondisk_lazy`
becoming unreachable, another ~60 LoC).

**No source code was modified by this audit.**
