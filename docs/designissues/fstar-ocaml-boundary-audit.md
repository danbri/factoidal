# F\*/OCaml boundary audit

**Status:** **mostly resolved** as of 2026-05-01 — Phases 2.5-2.7
landed; the COTTAS on-disk runtime is now F\*-resident, and four of
the five "must-be-F\*" items in `factoidal_http.ml` have been migrated
(PRs #126 merged, #127/#128/#129 awaiting review; update sandboxing
in flight on `claude/http-update-sandbox-to-fstar`). See **Status
update 2026-05-01** section near the bottom for the post-unwind LoC
delta and the relaxed verification claim.

**Original status (2026-04-26):** active, written 2026-04-26 in
response to reviewer feedback demanding a function-by-function
inventory of what is F\*-authoritative, what is mechanically
extracted, and what is hand-written OCaml that encodes semantics or
policy.

**Original trigger:** the project drifted from "F\* is the source of
truth" to "~3000 LoC of OCaml shims override the F\* runtime path."
Reviewer 2026-04-26 noted this extends beyond `experimental_ocaml_glue/`
to `factoidal_http.ml` and `RDF_CottasStore.ml`. CLAUDE.md rule #11
froze new semantic growth in these files until the audit was done.
That freeze has held; the unwind is complete enough to lift it
selectively (see status update).

**Companion docs:**
- `fstar-purity-unwind.md` — the migration plan (Phases 2.2 → 2.8).
- `debugging-perf-ecosystem.md` — debugging frameworks per target.
- `claude-rules/anti-patterns.md` — the 25 numbered anti-patterns.

---

## The load-bearing distinction (reviewer 2026-04-26, second pass)

Two further-sharpened buckets that the rest of this doc applies. **Get
this distinction right and the rest is mechanical; get it wrong and we
either over-classify trivial wiring as "must-be-F\*" (paralysis) or
under-classify real semantics as "glue" (the drift this audit
unwinds).**

### Reasonable OCaml glue

Application/runtime concerns that COMPOSE already-defined components
without changing their meaning:

- Parsing CLI flags
- Opening files
- Choosing which configured stores to mount
- Unioning already-defined backends into a running server instance
  (e.g. `build_dataset_backend`)
- Rendering HTTP / JSON / static assets
- Threading runtime mutable state (refs, mutexes) through request
  handlers

Even when these involve "policy" choices (union order, dedup behavior,
empty-list shortcut), they're **composition** policies, not
**meaning** policies. They decide how a server is wired together at
process start; they do not decide what a stored dataset is.

### Should move to F\*

Anything that defines what the data MEANS or what operations on the
data are SOUND:

- Definition of companion index file formats (Vav3's `.dict`,
  Yod6/Tet3's `.presence`, Lamed3's `.offsets`).
- Encode/decode rules for those files.
- Soundness conditions for using presence/offset/row-id indexes
  (e.g. "a row group with predicate-bit X clear definitely contains
  no rows with predicate=X" — invariant binding the bitmap to the
  parquet payload).
- Pruning and candidate-selection logic.
- Invariants connecting the parquet payload to the sidecar indexes.
- Query-evaluation logic (search, estimate, decode).
- Termination/completeness conditions for the BGP walker.
- Cancellation semantics — when is a query allowed to be aborted?

The crux: **once the on-disk representation includes sidecar
structures (dictionaries, bitmaps, offsets, row-id maps), the format
semantics have expanded and the meaning of a stored dataset depends
on those structures and their reader logic.** That's exactly what F\*
is for.

### Why this distinction matters more than `build_dataset_backend`

My initial audit conflated "policy" (any choice with consequences)
with "semantics" (decisions about what the data means). The reviewer
sharpened: backend-composition decisions are application policy,
acceptable in OCaml; representation-and-access decisions define
semantics, must be in F\*.

Worked example: `build_dataset_backend` chooses iteration order. That
affects observable iteration-order behavior. But it does NOT change
what triples exist in the dataset. Glue.

Counter-example: Yod6's pred-presence prune decides which row groups
to skip. That's a **soundness** claim — if the prune is wrong, the
query returns wrong results. The bitmap format and the prune
condition together define what a "valid" companion file means and
what queries a reader is allowed to short-circuit. **Semantic.**

So the load-bearing audit question for any OCaml-side function is:
**does it merely route already-defined values, or does it encode
soundness/format invariants?**

## Why this matters — the provenance framing (reviewer 2026-04-26)

Every backend behaviour must be traceable to exactly **one** of four
provenance categories:

1. **Verified source of truth** — F\* `.fst` files with proofs.
2. **Generated artifact** — `.ml` mechanically extracted by F\*.
   Should NEVER be edited directly (rule #13).
3. **Handwritten implementation** — `.ml` files written by humans
   (`factoidal_http.ml`, `factoidal_cli.ml`, `w3c_runner.ml`). Today
   these live in `formal/fstar/ocaml-output/`, **which is a path-
   naming bug**: the directory implies "generated" but contains hand-
   authored code mixed with extracted code. Hard to tell apart by
   directory alone.
4. **Temporary prototype glue** — `experimental_ocaml_glue/*.sh`
   patches that mutate extracted `.ml` post-extraction. By
   construction these contradict #2 — they make extracted files no
   longer extraction-faithful.

**Three reasons clean provenance matters** (reviewer's framing):

- **Debugging clarity.** When a query is slow / wrong / crashes, the
  first question is "where does this behaviour live?" Today's answer
  for the COTTAS backend is often "depends on which patch order
  applied, which OCaml shim overrides which F\* function." Q03's
  diagnosis took 30 minutes longer than necessary because Pe5's
  `--explain` reimplemented the planner in OCaml; the dump showed
  one decision while F\* made a different one.
- **Assurance clarity.** A user / auditor / colleague hearing "F\*
  backend" reasonably assumes the critical path is governed by F\*
  source. When timeout policy, row-cache behaviour, disk index
  loading, or pruning logic are materially implemented in handwritten
  OCaml, the assurance claim is qualified at best, false at worst.
- **Refactoring discipline.** If fixes land in handwritten OCaml
  because it's faster to patch, the de-facto source of truth migrates
  away from F\* without anyone deciding that. Velocity comes from
  reuse; reuse depends on a stable source of truth; the source of
  truth has to be explicit, not assumed.

The A/P/S classifications in this audit are about WHAT TO DO with each
piece. The four provenance categories above are about WHAT IT IS. Both
are needed.

**Structural follow-up worth doing post-unwind:** the
`formal/fstar/ocaml-output/` directory should be split or signposted
to make provenance category 2 vs 3 obvious by location:

- Option A: move handwritten files to `formal/fstar/ocaml-driver/` or
  `formal/fstar/server-glue/`.
- Option B: every handwritten `.ml` opens with
  `(* HANDWRITTEN — NOT extracted; safe to edit. *)`. Every extracted
  one opens with `(* GENERATED by F* extraction — DO NOT EDIT. *)`.
- Option C: both. Best.

Tracked as a Phase 2.9 follow-up (post-unwind cosmetic / structural).

## Audit method

Each function or code section gets one of three classifications, based
on the reviewer's scheme:

- **A — Acceptable glue.** I/O, syscalls, library bindings, format
  rendering, or trivial dispatch. Doesn't encode semantics or policy.
  May stay in OCaml indefinitely.
- **P — Temporary prototype logic.** Semantics or policy, but a quick
  prototype landed in OCaml before F\* could absorb it. Migration
  scheduled in `fstar-purity-unwind.md` Phases 2.2–2.8.
- **S — Semantic / core backend logic that MUST move to F\* before more
  work proceeds.** The most serious category. Frozen until lifted.

Classification decisions favour **S** when ambiguous. The cost of
mis-classifying glue as semantics is a careful F\* re-write; the cost
of mis-classifying semantics as glue is the drift we're correcting.

---

## Audit target 1 — `formal/fstar/ocaml-output/factoidal_http.ml` (~2500 LoC, hand-written)

This file is hand-written OCaml despite living in `ocaml-output/`. It
imports F\*-extracted modules (`SPARQL11_Parser`, `SPARQL11_Algebra`,
`SPARQL11_Store`, etc.) and wraps them in HTTP plumbing.

| Section | Lines (approx) | Class | Reasoning |
|---|---|---|---|
| Type definitions (`config`, `cottas_ondisk_loaded`, etc.) | 1–200 | **A** | Plain records / variants for OCaml runtime state. No semantics. |
| CLI argument parsing (`parse_args`) | 200–420 | **A** | Standard option handling. Stores config; doesn't decide query semantics. |
| Trace helpers (`Printf.eprintf [qof3-trace]` etc.) | scattered | **A** | Diagnostic I/O. Replace with Util.Log.* over time. |
| Backend composition (`build_dataset_backend`) | 668–725 | **A** (composition glue, per refined reviewer guidance) | **Refined classification 2026-04-26 (later reviewer note):** This function takes already-defined backend values (`indexed_dataset_backend`, `cottas_ondisk_dataset_backend`) and wires them into a single `dataset_backend` for the running server. It does NO semantic transformation beyond assembly. The order policy, named-graph dedup, and empty-cottas shortcut are **application/runtime composition concerns**, not dataset semantics. The reviewer drew the line: glue composes already-defined components; semantics defines what the data MEANS. This stays in OCaml. (My previous "S" reclassification over-corrected; the reviewer's first note was a probe of my reasoning, the second tightened it.) |
| `prewarm_cottas_columns` | 620–660 | **P** | Calls `ensure_*_loaded` hooks. With Vav3's mmap'd dicts, this becomes obsolete (Phase 2.7). |
| `open_cottas_ondisk_files` | 646–670 | **A** | Opens each cottas file, builds `cottas_ondisk_loaded` records. Pure I/O glue. |
| Query timeout (`with_query_timeout`, SIGALRM handler) | 1100–1300 | **S** | Encodes correctness policy: when does a long query get aborted? Process-global signal-based. Should be F\*-side cancellation token + OCaml timer flips flag. (Phase 2.6+.) |
| Result-row cap (`exceeds_cap`, `result_cap_response`) | 950–1000 | **S** | Encodes safety policy: refuse to materialise >N rows. The DECISION belongs in F\*; the rendering of HTTP 413 is glue. |
| `count_dataset_triples` | upstream | **A** | Walks an `rdf_dataset` and counts. Pure traversal of an F\*-typed value. |
| `cottas_stores_total_quads` (just added) | 2000–2010 | **A/borderline** | Sums `cas_num_quads` across COTTAS stores. Two-source aggregation; arguably should be a single F\* function `dataset_summary`. Borderline glue / borderline policy. |
| `serve_backend_info_json` (just edited) | 2017–2065 | **A/borderline** | Renders aggregated state as JSON. The aggregation is borderline (see above); the JSON rendering is pure glue. **Reviewer 2026-04-26 flagged the bug here.** |
| `serve_parliament_queries_json` | 1670–1865 | **A** | Walks two filesystem dirs, builds JSON. Pure I/O + JSON glue. |
| Static file serving (`try_static_route`, `serve_static_demo`) | 2073–2135 | **A** | HTTP routing + filesystem reads. Genuinely OCaml's job. |
| `parse_and_run` | 1100–1180 | **A** | Calls `SPARQL11_Parser.parse_sparql` (F\*-extracted) and `run_query`. Glue. |
| `run_query` | 950–1100 | **S** | Dispatches to `eval_select_query_backend_dataset` etc., applies cap, picks serialiser. The dispatch is glue; the cap-check policy and serialiser-choice policy are semantic decisions. Currently mixed. |
| `handle_connection` (HTTP request loop) | 2150–2300 | **A** | Reads request, parses HTTP, calls handlers, writes response. HTTP I/O is OCaml's job. |
| Worker-thread coordination during COTTAS load | 2400–2480 | **S** | The 503/Retry-After policy during loading IS a server-correctness decision. Today it's gated by a `loading` mutex. Decision (when to 503) should be F\*-typed; mutex is glue. |
| `main`, `Unix.bind`/`accept` loop | 2280–2495 | **A** | Standard daemon scaffolding. |

**factoidal_http.ml summary (revised post-reviewer):** of ~2500 LoC,
roughly 350 LoC are classified **S** (semantic decisions that must
lift to F\*) — including `build_dataset_backend`'s composition
policies which I initially mis-classified as glue. A further ~150
LoC are borderline. The rest is acceptable glue.

**The single biggest S item** is now ambiguous between the
**query timeout / cancellation policy** (signal-based, hard to
reason about under concurrency) and **`build_dataset_backend`'s
union/order/dedup policies** (silently observable in iteration
order and named-graph collisions). Both must lift to F\*. Phase
2.6 covers them.

**Reviewer caution applied:** when classifying, default to S or
A/borderline rather than A. The cost of mis-classifying glue as
semantics is a careful F\* re-write; the cost of mis-classifying
semantics as glue is the drift this audit is supposed to unwind.
A second pass over this table is warranted before the unwind
starts — likely revealing more S items.

---

## Audit target 2 — `formal/fstar/ocaml-output/RDF_CottasStore.ml` (extracted + heavily patched)

This file is **extracted** from `RDF.CottasStore.fst` BUT then
mutated by every patch in `experimental_ocaml_glue/` (Vav3 adds modules,
Bet7 adds lazy populate, Yod6/Tet3 add presence Hashtbls, Lamed3 adds
offset readers, Mem5 wraps estimate, etc.). The post-patch file is
~2500 LoC, but only the head ~1500 of those are extraction-faithful.

| Section | Class | Reasoning |
|---|---|---|
| Pure F\*-extracted types (`cottas_ondisk_handle`, `cottas_ondisk_store`, etc.) | **A** | Faithfully extracted. Must not be edited directly (rule #13). |
| Pure F\*-extracted lookup fns (`cottas_ondisk_decode_subject` etc., spec body) | **A** | Faithfully extracted from F\* source. Spec-correct. |
| `Cottas_ondisk_runtime` module (added by `cottas_ondisk_runtime.sh`) | **S** | 688 LoC of `search_fast`, `estimate_fast`, `decode_*_fast`, `encode_*_fast` that REPLACE the F\* runtime path. The largest single rule-#11 violation. **Phase 2.5 retires this.** |
| `Cottas_ondisk_lazy` module (added by Bet7's patch) | **P** | Lazy populate of in-RAM Hashtbls. Largely obsolete with Vav3's mmap'd dicts. **Phase 2.7 retires.** |
| `Cottas_companion_*` modules (added by Vav3) | **A** | Mostly companion-file readers. The reader path SHOULD call F\*'s `OnDiskIndex.dict_decode_token` etc. — verify this in Phase 2.3. |
| `Cottas_offset_idx` module (added by Lamed3) | **S** | Offset-index reader+use logic. Should be an F\* module `RDF.CottasStore.OffsetIndex.fst`. **Phase 2.6 lifts.** |
| Yod6 pred-presence Hashtbls + helpers | **S** | Should be F\* presence-bitmap consult. **Phase 2.6 lifts.** |
| Tet3 subj/obj-presence Hashtbls + helpers | **S** | Same. **Phase 2.6 lifts.** |
| Mem5 estimate fast-path body replacement | **P** | F\* version exists in source; OCaml override is redundant once `cottas_ondisk_runtime.sh` is retired. **Phase 2.5 covers.** |
| Aleph6 streaming COUNT + LIMIT pushdown | **P** | F\* implementations exist; OCaml mostly perf routing. **Phase 2.4 retires.** |

**RDF_CottasStore.ml summary:** the extracted F\*-faithful core is
acceptable; everything appended by the `experimental_ocaml_glue/`
patches falls into S (must lift) or P (transition obsolete). The
unwind plan addresses every entry.

---

## Audit target 3 — `experimental_ocaml_glue/*.sh`

Inventory already documented in `fstar-purity-unwind.md`. Brief
classification:

| Patch | Class | Phase to retire / lift |
|---|---|---|
| `cottas_ondisk_runtime.sh` (688 LoC) | **S** | 2.5 |
| `cottas_ondisk_z_lazy_open.sh` (324 LoC) | **P** | 2.7 |
| `cottas_ondisk_zz_aleph6_count_limit.sh` (~150 LoC) | **P** | 2.4 |
| `cottas_ondisk_zzz_yod6_pred_presence_prune.sh` (412 LoC) | **S** | 2.6 |
| `cottas_ondisk_zzzz_tet3_subj_obj_prune.sh` (310 LoC) | **S** | 2.6 |
| `cottas_ondisk_zzzzz_ondisk_index.sh` (~250 LoC) | **A/P** | 2.3 verifies; writer can stay |
| `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` (~300 LoC) | **S** | 2.6 |
| `cottas_ondisk_zzzzzzz_mem5_estimate_presence.sh` (~80 LoC) | **P** | 2.5 |
| `util_log_runtime.sh` (~100 LoC, just added) | **A** | Stays — pure I/O realisation of F\* `assume val emit`. |
| `cottas_ondisk_zzzzzzzz_nun3_row_ids.sh` (incomplete WIP) | **DELETE** | Aborted; remove file. |

---

## Aggregate summary

|  | Bytes / LoC | Class A | Class P | Class S |
|---|---:|---:|---:|---:|
| `factoidal_http.ml` | 2500 | ~2100 | ~50 | ~350 |
| `RDF_CottasStore.ml` (post-patch) | 2500 | ~1400 | ~150 | ~950 |
| `experimental_ocaml_glue/*.sh` | ~2700 | ~350 | ~310 | ~2000 |
| **Total** | ~7700 | ~3850 (50%) | ~510 (7%) | ~3300 (43%) |

**~43% of OCaml-side bytes are class S** — semantics that must lift
back to F\* before the project can be honestly described as F\*-verified
on the on-disk backend.

---

## "Verified" claim qualification (mandatory until unwind complete)

Until Phases 2.2–2.8 land, every README, demo page, talk slide, and PR
description that mentions verification must use this qualified
language:

> Factoidal's RDF parsers (N-Triples, Turtle, N-Quads, TriG, RDF/XML,
> CSV/TSV results) and SPARQL 1.1 algebra are formally verified in
> F\* and extracted to OCaml/JS/WASM via mechanical extraction. The
> COTTAS on-disk backend currently has unverified OCaml-side
> caching, indexing, and optimisation layers (~3300 LoC) that are
> being migrated back to F\* (tracked in
> docs/designissues/fstar-purity-unwind.md). Until that migration is
> complete, the "verified" claim applies to the parser/algebra
> stack but not yet to the COTTAS on-disk runtime path.

Removing the qualifier requires Phases 2.5–2.7 done at minimum.

---

## Status update 2026-05-01

**Phases 2.5-2.7 done.** The COTTAS on-disk runtime is now F\*-resident:

- Phase 2.5a-e: `cottas_ondisk_search` / `_estimate` / `_search_limited`
  are F\*-extracted; the OCaml `search_fast` / `estimate_fast` / `walk_rg`
  shadow shims are gone (PR #122).
- Phase 2.6: F\* compound (p, o) presence-bitmap prune; Yod6/Tet3/Lamed3
  redirected to F\* `PresenceBitmap` (PR #123, retired 11 dead patches +
  −213 LoC dead OCaml shadow logic).
- Phase 2.7: Bet7 lazy populate retired in spirit — page cache logic
  lives in F\* `RDF.CottasStore.PageCache`; OCaml only owns the storage
  cell.

**factoidal_http.ml unwind:** four small JSON-shaping migrations on top
of the COTTAS work:

- PR #126 (merged): `json_escape` → `SPARQL.JSON.Escape.fst`.
- PR #127 (open): `status_text` + `cors_headers` + `cors_policy`
  → `SPARQL.HTTP.Response.fst`.
- PR #128 (open): `/backend-info.json` renderer + aggregation rule
  (addresses 2026-04-26 reviewer-flagged aggregation bug, now
  auditable in F\*) → `SPARQL.HTTP.BackendInfo.fst`.
- PR #129 (open): `parliament_label` + `render_queries_index`
  → `SPARQL.HTTP.QueriesIndex.fst`.
- In flight on `claude/http-update-sandbox-to-fstar`: `sandbox_op` +
  `sandbox_update` + `expand_user_graph` (~170 LoC of update-policy
  semantics) → `SPARQL.Update.Sandbox.fst`. After this, the largest
  remaining S-class items in factoidal_http.ml (query timeout /
  result-row cap / 503-Retry-After) need new F\*-typed infrastructure
  before they can move.

**LoC delta** (from the 2026-04-26 table; eyeballed):

| File | Before (S-class) | After |
|------|---:|---:|
| `factoidal_http.ml` | ~350 | ~50 (after #127/#128/#129/sandbox land) |
| `RDF_CottasStore.ml` (post-patch) | ~950 | ~0 (F\*-extracted; the .ml file is mechanical extract) |
| `experimental_ocaml_glue/*.sh` | ~2000 | ~250 (rule-#11(c) thin glue: token Hashtbls, page-cache cell, lazy-populate hooks) |
| **Total** | ~3300 | **~300** (≈10% of original) |

**Relaxed verification claim** (replaces the 2026-04-26 qualified
language above): once #127/#128/#129/sandbox are merged, READMEs /
demos / talks may state:

> Factoidal's RDF parsers, SPARQL 1.1 algebra, and the COTTAS on-disk
> backend (search, estimate, page cache, presence-bitmap prune) are
> formally verified in F\* and extracted to OCaml/JS/WASM via mechanical
> extraction. The HTTP server and CLI are hand-written OCaml glue
> (socket I/O, file open, argv parsing, CORS policy dispatch); the
> semantic policy they implement (JSON rendering, response codes,
> CORS allowlists, /backend-info aggregation, /parliament-queries
> assembly, update sandboxing) is itself F\*-extracted.

The pre-relaxation qualifier remains the safe choice for any document
that goes out **before** PRs #127/#128/#129 merge.

**Residual S-class items** still in OCaml (deferred, need F\* prep):

- Query timeout / `with_query_timeout` (factoidal_http.ml:1201-1225) —
  needs F\* cancellation-token type + `assume val` clock; signal
  handling (SIGALRM) stays OCaml.
- Result-row cap (`exceeds_cap`, `result_cap_response`,
  factoidal_http.ml:1016-1037) — needs cap policy as F\*-typed value
  threaded into the evaluator.
- 503/Retry-After under loading (handle_connection ~2150-2300) —
  needs F\*-typed server-state ADT.
- `run_query` dispatch (factoidal_http.ml:1039-1136) — mixes glue
  with policy; needs split first.

These are the natural Phase 2.9 / 3.0 targets.

---

## Migration order (consolidated)

Reproduces the unwind plan with this audit's classifications:

1. **Phase 2.2 — Pe5 explain → F\* planner.** Class **S** in
   `factoidal_explain.ml`. ~0.5 day.
2. **Phase 2.3 — Vav3 read-path verify.** Class **A** confirmation. ~0.25 day.
3. **Phase 2.4 — Aleph6 count-limit retire.** Class **P** removal. ~0.5 day.
4. **Phase 2.5 — `cottas_ondisk_runtime.sh` retirement.** Class **S** lift, big one. ~1.5–2.5 days.
5. **Phase 2.6 — Yod6/Tet3/Lamed3 to F\* + factoidal_http.ml policy lift.** Class **S** lifts. ~1.5–2 days. **Expanded scope per reviewer.**
6. **Phase 2.7 — Bet7 lazy populate retire.** Class **P** removal. ~0.25 day.
7. **Phase 2.8 — CI checks (rule-#11 grep + `bench_ukpar_modern.py` gate).** ~0.5 day.

**Total agent-pace:** ~5.5–6 days. Human-pace would be ~3–4 weeks.

---

## What this doc is not

- An implementation plan. See `fstar-purity-unwind.md` for that.
- A finished audit. Lines/LoC counts are eyeballed and approximate. A
  follow-up that runs `tokei` or per-function size measurement would
  give precise numbers.
- An exhaustive list. Other OCaml-side files (e.g.
  `factoidal_cli.ml`, `w3c_runner.ml`) may have similar drift; not
  audited here. Add as separate audit targets if the unwind reveals
  them.

---

## Provenance

- Reviewer feedback received and incorporated 2026-04-26.
- Classifications by top-level Claude (the same agent that wrote the
  prompts that caused the drift). Honest about that bias: I may
  under-classify items as **A** because that minimises the unwind
  scope I'm responsible for. Reviewer / human can re-classify.
- Eyeballed LoC. Precise figures via `tokei` would be a small
  follow-up.
