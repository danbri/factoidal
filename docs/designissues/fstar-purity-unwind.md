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

## Scope clarification (reviewer 2026-04-26)

The drift is **not just `experimental_ocaml_glue/`**. Two OCaml-side
files in `formal/fstar/ocaml-output/` have accumulated substantial
backend semantics that should also live in F\*:

- `factoidal_http.ml` (~2500 LoC, hand-written) — query-timeout policy
  (Heth3's SIGALRM wrapper), `/backend-info.json` aggregation across
  in-memory + COTTAS state (just edited 2026-04-26), result-row cap
  enforcement (Tav5), worker-thread coordination during COTTAS load,
  serialiser dispatch. Some of this is genuinely OCaml's job
  (HTTP protocol parsing, `Unix.accept`, signal handling); some
  encodes server-correctness *decisions* that belong in F\*.

- `RDF_CottasStore.ml` (extracted, but heavily mutated by
  `experimental_ocaml_glue/` patches) — caching policy (page cache,
  byte cache), index population, prune-dispatch logic. Most of this
  is what the unwind aims to retire.

The reviewer's distinction is useful: thin glue (HTTP routing,
`Unix.read`, `printf`) belongs in OCaml. **Backend semantics,
caching policy, timeout/cancellation policy, and server correctness
decisions belong in F\*.** Phase 2.5 (retire `cottas_ondisk_runtime.sh`)
addresses RDF_CottasStore.ml. Phase 2.6+ should also address the
`factoidal_http.ml` drift specifically:

- Move query-timeout policy into F\* via a `time_budget : nat` +
  `assume val cancellation_polled : unit -> bool` discipline. The
  OCaml side becomes a timer that flips the flag.
- Move backend-info aggregation into F\* (`dataset_summary :
  rdf_dataset -> list cottas_ondisk_store -> Tot summary_info`). The
  OCaml side renders JSON.
- HTTP routing, `Unix.accept` loop, file serving stay in OCaml — that
  IS the genuinely-I/O part.

This expands Phase 2.6 from "lift Yod6/Tet3/Lamed3 to F\*" to also
include "lift factoidal_http.ml's policy/aggregation logic to F\*".
Estimate +1 day. **Documented here so the recurring "but factoidal_http.ml is hand-written, surely it's fine" reflex stops.**

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

**Status (2026-04-26, Chi3 audit):** **BLOCKED.** Three dependency
blockers prevent Phase 2.4 from landing standalone:

1. `cottas_ondisk_runtime.sh` (Phase 2.5) shadows the F\* runtime
   functions Aleph6 calls into; deleting Aleph6 first would route
   through the shadow, not F\*.
2. Bet7's lazy-populate patch (Phase 2.7) leaves `coh_*_raw` empty
   on cold open — Aleph6's F\* path needs them populated.
3. Yod6/Tet3 patches (Phase 2.6) grep for the Aleph6 marker; deleting
   it first breaks their anchor matching.

Phase 2.4 deferred until 2.5/2.6/2.7 land. Audit:
\`docs/designissues/2026-04-26-chi3-aleph6-retire.md\`.

**Goal:** the streaming COUNT(*) and LIMIT pushdown F\* paths are the runtime path.

**Steps (post-unblock):**
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

**Live diagnostic (2026-04-26, Q03 daemon trace):** The drift cost is
not theoretical — Q03 (`?o a geo:wktLiteral`, zero matching triples)
takes 4.2s on the live demo because Tet3's per-column bitmap returns
`could_o=true` for rg=22 (`wktLiteral` appears as object somewhere in
that rg, just never paired with `rdf:type`). Mem5 returns
estimate=120,900 (overcount of the surviving rg's row count) — so the
planner doesn't see the unsat-ness. Executor walks rg=22 with 4 full
DLBA column decodes (subj/pred/obj/graph) of 122,880 rows, RSS
278MB→1360MB, finds 0 matches.

Phase 2.6 should produce **either** of:

- **Compound `(p, o)` presence per rg** — companion `.po.presence`
  file. Mem5 returns 0 → planner short-circuits → 0ms execute.
  Verifiable in F\* (lemma: \"if compound bitmap says no, no row
  matches\"). Filed as **issue #104**.
- **Lazy column decode in `*_inner`** — decode predicate first
  (cheap, 232 distinct), filter, then decode object on the survivors.
  Cuts rg=22 from 4s to ms. Belongs in F\* `RDF.CottasStore`, not
  the OCaml `*_inner` glue.

Either fix completes the unwind for the prune layer and lands Q03
near-instant. Whichever lands first should also delete the Q03 fix
in `cottas_ondisk_zzzzzzzzz_q03_estimate_fix.sh` (the lamed3
dispatcher bypass becomes obsolete once `*_via_offsets` either
disappears (via 2.5/2.6 lift) or is fixed in F\*).

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
3. Wire into the existing CI: this repo has
   `.github/workflows/check-derived-files.yml`,
   `.github/workflows/check-extraction.yml`,
   `.github/workflows/deploy-pages.yml`, and
   `.github/workflows/w3c-tests.yml`. **There is NO `.github/workflows/ci.yml`** — earlier draft of this doc referenced one as if it
   existed. The recurrence check should either: (a) become a new
   workflow `.github/workflows/check-fstar-purity.yml`; or (b) be
   added as a job inside `check-extraction.yml` since that
   workflow already runs the build pipeline. Pick (a) for
   isolation; the job runs in seconds and a failure should be
   blocking for the unwind invariant, separately from the
   slower extraction-validity check.

**Acceptance:** PR that adds a new override patch fails CI.

## Companion architectural concerns (out-of-band, non-rule-violating)

Two reviewer-flagged issues that are NOT rule-#11 violations but matter
for the same correctness/quality posture:

### A. SIGALRM-based per-query timeout is process-global

Heth3's commit `afb4c1d` uses `Unix.alarm` + `SIGALRM` to interrupt a
running query. The handler raises `Query_timeout` inside whatever OCaml
stack frame happens to be running when the signal fires. The code at
`factoidal_http.ml:1184` documents the caveat: *"Unix.alarm is per-
process. Today we have a single-threaded accept loop (or one
accept-thread when COTTAS is loading), so this is effectively
per-request. A future worker pool will need a per-thread polling abort
flag instead."*

Reviewer (2026-04-26): *"The server is already running an accept loop
on a worker thread when COTTAS is loading at
factoidal_http.ml:2459. ... it is the kind of mechanism that makes
failure isolation and future concurrency much harder."*

**Verdict:** the reviewer is right. Today's deployment is single-
request-at-a-time so this works, but as soon as we add real
concurrency (worker pool, Lwt, or async COTTAS open + concurrent
queries) the global alarm becomes wrong. Replacement options:

- **Per-thread polling abort flag** — long-running loops in F\* (BGP
  walker, search_fast, estimate_fast) check a thread-local atomic
  every N iterations. Threading the flag through F\* is invasive;
  lifting it to an `assume val` is feasible.
- **Lwt-style cooperative cancellation** — would require refactoring
  the accept loop to Lwt; large change.
- **`pthread_kill`** — sends a signal to a specific thread. Less
  portable; macOS and Linux differ in subtle ways. Works in practice
  for single-threaded blocking code.

**Decision:** defer until Phase 2.5 (when the F\* `cottas_ondisk_search`
becomes the runtime path). At that point we'll add a polling abort flag
to F\*'s search loop. Until then, document the limitation in the daemon
help text and don't enable concurrency.

### B. UK Parliament benchmark is not a CI gate

Reviewer (2026-04-26): *"tools/bench_ukpar_modern.py writes the
benchmark artifacts, but my search only found it referenced in docs and
not wired into any workflow under .github/workflows. So a regression
from 'some curated queries work' to 'half the demo query set fails and
the server dies' can land without an automated gate."*

**Verdict:** the reviewer is right. We have the W3C test suite as a
correctness gate (1657/1/0/4) but no demo-query-shape gate. The Q03
regression that bit us today would have been caught by a CI step
that:

1. Builds the daemon
2. Boots it with parliament corpus
3. Issues each `tools/sample-queries/ukparliament/**/*_modern.rq`
4. Asserts pass/fail counts vs a baseline
5. Asserts wall-time within tolerance

**Decision:** add `.github/workflows/ukparliament-bench.yml` as part of
Phase 2.8 (the CI work). Independently shippable from the unwind. Could
ship before Phase 2.2 starts — this is a backstop, not a refactor.

### C. /backend-info.json under-reporting (FIXED 2026-04-26 commit 134fd93)

Reviewer (2026-04-26): *"In a --data-cottas-only server, that can
advertise 'kind':'binary' while still showing a zero or partial triple
count."*

Now fixed: `serve_backend_info_json` sums `dataset_ref` quads + open
COTTAS stores' `cas_num_quads`. JSON also splits the breakdown
(`in_memory_triples`, `cottas_triples`, `cottas_files`) so consumers
can see where the rows come from. Web component pill will now show
"binary COTTAS (3,143,406 triples · data.cottas)" on parliament
deployments.

## Time estimate — tentative planning heuristic, NOT a delivery commitment

Reviewer 2026-04-26 (gpt5.5): *"docs/designissues/fstar-purity-unwind.md
gives an unrealistically confident unwind estimate and frames it as
roughly a five-day agent task. In a repo where the core issue is that
fast fixes accumulated faster than provenance discipline, that
estimate is dangerous. ... it reads like a delivery commitment. That
encourages the same 'quickly patch through the mess' mindset that
caused the drift."*

Correction. The numbers below are **planning heuristics** for sizing
the work into independent commit-shaped chunks; they are NOT a
schedule, NOT a commitment, and NOT calibrated to actual measurement.
They were generated from a one-paragraph mental model ("the original
drift accumulated in ~24 hours of agent work, so the unwind should be
similar") — that's the wrong analogy because adding logic and
**carefully retiring it under correctness invariants** are not
symmetric activities. Retirement is harder.

Specifically, each phase below has at least one of these unknowns
that could expand it 2-5×:

- **F\* type-system friction** when porting OCaml-array-shaped logic
  to F\*'s `list`/`Seq` shape. Verifying termination, refinement
  invariants, and proof obligations may surface only when you try.
- **Performance regression** when the F\*-extracted version replaces
  the OCaml shadow. Phase 2.5a is "make F\* fast"; if F\* extraction
  produces 5× slower code than the OCaml shim, the demo workload
  regresses and we either accept the regression or do another
  optimisation pass.
- **W3C suite breakage**. Each phase must keep 1657/1/0/4. Subtle
  semantic changes in F\* equivalents may break a test we didn't
  expect; debugging the diff is unbounded.
- **Cross-phase dependencies**. Phase 2.6 (Yod6/Tet3/Lamed3 to F\*)
  may need Phase 2.5 done first. Or Phase 2.5a's optimisations may
  obviate the need for some of 2.6. We won't know until we try.

| Phase | Crude size estimate (agent-pace heuristic) | Risk multiplier |
|---|---|---|
| 2.2 Pe5 explain → F\* planner | 0.5 day | 2× if F\* planner exposure is harder than expected |
| 2.3 Vav3 read-path verify | 0.25 day | low risk, narrow |
| 2.4 Aleph6 count-limit retire | 0.5 day | 1.5× — small chance the F\* version doesn't match observable behaviour |
| 2.5a Make F\* search fast | 1-2 days | **3-5× quite plausible** — biggest unknown |
| 2.5b Delete runtime.sh | 0.5 day | 2× if perf regression triggers a re-evaluation |
| 2.6 Yod6/Tet3/Lamed3/factoidal_http policy → F\* | 2-3 days (revised up after reviewer corrected build_dataset_backend mis-classification) | 2× |
| 2.7 Bet7 lazy populate retire | 0.25 day | low |
| 2.8 CI check | 0.5 day (revised — needs new workflow file, not a one-line addition) | low |

**Take these numbers as crude order-of-magnitude only.** Realistic
bounds: best case ~5 agent-days; pessimistic case where Phase 2.5a
runs into F\*-extraction-perf cliffs and 2.6 surfaces type-system
friction is ~3 weeks of agent-pace work. The honest framing is "we
don't know until we try the first phase; budget the time-box for
that phase, learn, then re-estimate."

The drift was caused by treating the work as estimateable-and-
sequential. The unwind should not repeat that mistake.

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
