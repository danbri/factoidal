# F\*-purity unwind — retiring the OCaml semantic shims

**Status:** active plan, written 2026-04-26 after the user observed that
`experimental_ocaml_glue/` had accumulated ~3000 LoC of semantic logic
overriding F\* runtime functions.

**Cause attribution (honest):** I (top-level Claude) wrote agent prompts
between 2026-04-25 and 2026-04-26 that contained "Shape A vs Shape B"
clauses giving each agent permission to add OCaml-side logic when the
F\*-side fix was inconvenient. Each individual decision was justifiable
("the F\* path is bypassed anyway"); the cumulative effect was that the
verified-extraction story for the COTTAS backend collapsed. CLAUDE.md
rule #11 (added 2026-04-26) closes off the prompt loophole. This doc
addresses the existing debt.

## Inventory of overrides

In rough size order (largest first), with current F\* equivalent state:

| # | Patch | LoC | Overrides F\* function | F\* equivalent today |
|---|---|---:|---|---|
| 1 | `cottas_ondisk_runtime.sh` | 688 | `cottas_ondisk_search`, `_estimate`, `_decode_*`, `_encode_*` | Exists (Resh3/Mim2 work); replaced at runtime |
| 2 | `factoidal_explain.ml` | 580 | (no override; reimplements `choose_best_tp_backend` for explain) | F\* planner exists; explain reimpl bypasses it |
| 3 | `cottas_ondisk_zzz_yod6_pred_presence_prune.sh` | 412 | Mirrors `populate_dict_cache_for_column` / `compute_candidate_rgs_loop` | F\* prune logic exists at `RDF.CottasStore.fst:480-525`; OCaml duplicates and replaces |
| 4 | `cottas_ondisk_z_lazy_open.sh` (Bet7) | 324 | Lazy populate of in-RAM Hashtbls | Largely OBSOLETE post-Vav3 (mmap'd dicts replace Hashtbls); see action below |
| 5 | `cottas_ondisk_zzzz_tet3_subj_obj_prune.sh` | 310 | Subject + object presence prune | No F\* equivalent (would be analogous to Yod6 in F\*) |
| 6 | `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` | 300 | Per-rg predicate row-offset index reader/use | No F\* equivalent (writer can stay; reader/use must lift) |
| 7 | `cottas_ondisk_zzzzz_ondisk_index.sh` (Vav3) | ~250 | Companion-file mmap'd readers | F\* `RDF.CottasStore.OnDiskIndex.fst` exists; verify reader path actually uses it |
| 8 | `cottas_ondisk_zz_aleph6_count_limit.sh` | ~150 | Streaming COUNT(*) + LIMIT pushdown | F\* implementations exist; OCaml mostly perf-shim routing |
| 9 | `cottas_ondisk_zzzzzzz_mem5_estimate_presence.sh` | ~80 | Estimate via presence bitmap | F\* `cottas_ondisk_estimate` exists with Mem5's structural change in F\* source; OCaml duplicates |

**Total: ~3094 LoC** of OCaml-side semantic logic to retire.

## Order of operations (smallest → largest, easiest → hardest)

The smaller patches are usually simpler refactors. Doing them first
proves the unwind methodology before tackling the big domino
(`cottas_ondisk_runtime.sh`).

### Phase 2.1 — Mem5 estimate-presence fast path (#9, ~80 LoC)

**Goal:** retire `cottas_ondisk_zzzzzzz_mem5_estimate_presence.sh`. The
F\* `cottas_ondisk_estimate`'s bound branch already calls
`plan_candidate_rgs` (Mem5's F\*-side commit `04f7c64`'s F\* edits). The
OCaml glue just needs to NOT override that.

**Steps:**
1. Read the F\*-side `cottas_ondisk_estimate` body. Confirm bound branch returns `length(candidates) * (total_rows / rg_count)`.
2. Delete the OCaml override patch from `experimental_ocaml_glue/`.
3. Re-extract; observe that `Cottas_ondisk_runtime.estimate_fast_inner`
   is no longer overridden — but it still runs because rule #1
   (`cottas_ondisk_runtime.sh`) replaces `cottas_ondisk_estimate`
   wholesale. Need to fix #1 first OR scope this to "F\*-side
   estimate body is correct; OCaml shadow becomes redundant when #1
   is retired." → Skip Phase 2.1 in isolation; bundle with Phase 2.5.

**Reality check:** Phase 2.1 cannot be done independently because
`cottas_ondisk_runtime.sh` (#1) replaces the entire `cottas_ondisk_estimate`
body. So the "smallest first" ordering is misleading. The first useful
unwind is Phase 2.2 below.

### Phase 2.2 — Pe5 `factoidal_explain.ml` calls F\*'s real planner (#2, 580 LoC simplification)

**Goal:** Pe5's plan dump should call F\*'s `choose_best_tp_backend`
(now logged via Util.Log) rather than re-implementing the planner in
OCaml.

**Why first:** Pe5's reimpl has no production runtime impact (it only
runs under `--explain`). Replacing it with a thin wrapper around F\*'s
real planner is contained: doesn't break Q00-Q02, doesn't need the
runtime.sh override gone first.

**Steps:**
1. Util.Log emits log lines for every `choose_best_tp_backend` decision (DONE in pending commit).
2. Modify `factoidal_explain.ml` to enable Util.Log at LL_Debug level, run a no-execute call into a new F\* function `dry_plan_bgp` that walks the BGP via `choose_best_tp_backend` but doesn't execute, captures the log lines, returns them as the plan dump.
3. Delete Pe5's reimplemented planner code from `factoidal_explain.ml`.
4. Result: `--explain` now shows GROUND TRUTH (what F\* actually decides), not Pe5's parallel implementation.

**Acceptance:** `--explain` on Q03 shows the F\* planner's actual decisions. May reveal the Q03 regression (planner picks T1 first, despite T2 having smaller estimate — bug somewhere upstream of `choose_best_tp_backend`'s logic).

### Phase 2.3 — Vav3 read path verification (#7, no LoC change expected)

**Goal:** confirm Vav3's `RDF.CottasStore.OnDiskIndex.fst` is actually
the runtime read path, not just spec-side decoration. If the OCaml
glue duplicates the readers, retire the duplicates.

**Steps:**
1. Read `cottas_ondisk_zzzzz_ondisk_index.sh`. Identify which functions are
   writers (allowed I/O glue) vs readers (should be F\*).
2. For each reader, confirm it's calling into F\*-extracted code.
3. If duplicates exist, delete them; the F\* `companion_decode` /
   `companion_encode` etc. become the runtime path.

**Acceptance:** No reader logic in `_zzzzz_ondisk_index.sh`; it's writer-only.

### Phase 2.4 — Aleph6 count-limit (#8, ~150 LoC)

**Goal:** the streaming COUNT(*) and LIMIT pushdown F\* paths are the runtime path.

**Steps:**
1. Verify F\* `cottas_ondisk_search_limited` and the streaming COUNT detector in `SPARQL11.Store.fst` are present.
2. Delete `cottas_ondisk_zz_aleph6_count_limit.sh` if it only re-implements those.
3. Re-extract, verify smoke tests pass.

**Acceptance:** Q00 (COUNT) and Q01 (LIMIT 5) still fast.

### Phase 2.5 — `cottas_ondisk_runtime.sh` retirement (#1, 688 LoC)

**The big one.** This is the patch that started the drift: it replaces the F\*-extracted `cottas_ondisk_search` / `_estimate` / `_decode_*` / `_encode_*` with OCaml shadow implementations.

**Two sub-tasks:**

**2.5a — Make F\* fast.** The F\* implementations work but are slower than the OCaml shadows because they use `list (option string)` for decoded columns, allocate `cottas_qp_row` records, etc. Optimisation in F\*:
- Use `Seq.seq` or a refinement-typed array shape that extracts to OCaml `Array.t`.
- Inline column decode at the hot path.
- Use mmap'd companion files (Vav3) for dictionaries instead of in-memory Hashtbls.
- Profile after each change with bytecode + Spacetime.

**2.5b — Delete the patch.** Remove `cottas_ondisk_runtime.sh`. Re-extract. The F\* versions become the runtime path. Verify W3C 1657/1/0/4. Verify Q00-Q03.

**Acceptance:** No `cottas_ondisk_runtime.sh`. The F\* `cottas_ondisk_search` IS the runtime function. Performance within 2x of the previous OCaml-shim version (target — exact ratio depends on Phase 2.5a optimisation).

### Phase 2.6 — Yod6, Tet3, Lamed3 prune+offset logic to F\* (#3, #5, #6)

**Goal:** the per-rg presence bitmaps and offset indexes are consulted by F\* code, not OCaml shims.

**Steps:**
1. **F\* module `RDF.CottasStore.PresenceBitmap.fst`**: companion-file readers + bitmap-test logic + AND-of-bitmaps. Refinement-typed where useful.
2. **F\* module `RDF.CottasStore.OffsetIndex.fst`**: the row-offset reader.
3. **Modify F\* `cottas_ondisk_search` / `_estimate`** to consult these modules' readers. The runtime path consults presence and offsets via F\*-pure binary search + bitmap-test, not OCaml glue.
4. **Delete** `_zzz_yod6_*.sh`, `_zzzz_tet3_*.sh`, `_zzzzzz_lamed3_*.sh`. The companion-file WRITERS may stay in glue (writer is I/O glue per rule #3), but no reader logic in OCaml.

**Acceptance:** The presence and offset indexes are still used (queries are still fast); but the consulting logic is F\* code that extracts deterministically to OCaml/JS/WASM/C.

### Phase 2.7 — Bet7 lazy populate (#4)

**Goal:** retire `cottas_ondisk_z_lazy_open.sh`. With Vav3's mmap'd dicts as the runtime path, the lazy Hashtbl populate is obsolete.

**Steps:**
1. Confirm Vav3's `bulk-load` from companion files populates the same data Bet7's lazy populate did.
2. Delete `cottas_ondisk_z_lazy_open.sh`.
3. Re-extract. The handle's Hashtbls are no longer populated; queries route through F\* dict lookups via mmap.

**Acceptance:** boot still <5s; queries still pass W3C.

### Phase 2.8 — Layer 3 CI check

**Goal:** prevent recurrence.

**Steps:**
1. CI script: walk `experimental_ocaml_glue/*.sh`, grep for `let cottas_ondisk_*` definitions, fail if any are present (other than allow-listed I/O writers).
2. Same check for SPARQL evaluator overrides.
3. Add to `.github/workflows/ci.yml`.

**Acceptance:** PR that adds a new override patch fails CI.

## Time estimate (agent-pace, not human-pace)

Calibration: the original drift accumulated in ~24 hours of agent work
(Aleph6, Bet7, Mim3, Vav3, Yod6, Tet3, Sin7, Lamed3, Mem5, Pe5).
Unwinding it should not take dramatically longer.

| Phase | Estimate (agent-pace) |
|---|---|
| 2.2 Pe5 explain → F\* planner | 0.5 day |
| 2.3 Vav3 read-path verify | 0.25 day |
| 2.4 Aleph6 count-limit retire | 0.5 day |
| 2.5a Make F\* search fast | 1-2 days |
| 2.5b Delete runtime.sh | 0.5 day |
| 2.6 Yod6/Tet3/Lamed3 to F\* | 1-2 days |
| 2.7 Bet7 lazy populate retire | 0.25 day |
| 2.8 CI check | 0.25 day |

**Total: ~5 days agent-pace.** Human-pace would be ~3 weeks.

## Verification at each phase

After every phase, run:
1. `make verify` — all F\* modules verify clean.
2. `./bin/<platform>/w3c_runner --all` — W3C 1657/1/0/4 unchanged.
3. Smoke queries via curl: Q00 (COUNT), Q01 (rdf:type LIMIT 5), Q02 (absent predicate), Q03 (absent class).
4. Compare timings to pre-unwind baseline. Document acceptable regressions or restored wins.

## Honest gaps

- I can't yet verify that the F\* `cottas_ondisk_search` is fast enough
  to replace the OCaml shim without unacceptable regression. Phase
  2.5a is the place to confirm.
- The presence-bitmap + offset-index F\* modules don't exist yet; Phase
  2.6 may surface unexpected F\* type-system friction (e.g. byte-array
  refinement types).
- Pe5's plan dump's accuracy depends on F\*'s `choose_best_tp_backend`
  matching the actual runtime planner. Need to verify they're literally
  the same function (not two parallel implementations).

## Tracking

Each phase commit message must include `[unwind 2.N]` for greppability.
On completion, update this doc's status table:

| Phase | Started | Completed | Commit |
|---|---|---|---|
| 2.2 | — | — | — |
| 2.3 | — | — | — |
| 2.4 | — | — | — |
| 2.5a | — | — | — |
| 2.5b | — | — | — |
| 2.6 | — | — | — |
| 2.7 | — | — | — |
| 2.8 | — | — | — |
