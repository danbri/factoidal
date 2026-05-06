# F\*/OCaml boundary audit — drift recheck 2026-05-06

**Status:** spot-check, no new violations found.
**Companion:** `fstar-ocaml-boundary-audit.md` (full audit + 2026-05-01 status).
**Code-names:** `docs/code-name-glossary.md`.

> Plain-language note: this doc is part of the F\*/OCaml boundary
> audit (making sure load-bearing logic stays in F\*, not creeping
> into OCaml). It does not introduce new code; it walks the recent
> commits looking for that drift, and tightens a CI gate.

This is a scheduled-style recheck of `claude/main` against the audit's
2026-05-01 status update, plus a small expansion of the
`check-fstar-purity` CI gate's coverage. Nothing here changes the
audit's substantive conclusions; it's a clean checkpoint with two
specific changes.

---

## 1. Recent commits to claude/main since 2026-05-01

Walked the commits from 2026-05-01 forward (`git log --since 2026-05-01
origin/claude/main`). Material changes that could affect the audit:

### PR #136 — per-stage query timing (commit `8422f69`)

Added Server-Timing header + `/admin/recent.json` + an `admin/`
landing page to `factoidal_http.ml`. New definitions in OCaml:

- `query_timing` record + `zero_timing`.
- `recent_queries` ring buffer (`Mutex.create ()` + `ref []` capped
  at 50).
- Process-global counters `total_queries_seen`, `total_query_wall_ms`,
  `queries_status_2xx/4xx/5xx`, with their own mutex.
- `parse_and_run_timed` wrapping `parse_and_run`.
- `with_query_timeout` (the SIGALRM-based per-query timeout
  wrapper — pre-existing, not new).
- JSON renderer + admin HTML serving glue.

**Audit assessment:** acceptable per rule-#11(c) "thin glue" — these
are observability and HTTP-rendering plumbing, exactly the kind of
runtime mutable state the audit explicitly classifies as *reasonable
OCaml glue* ("threading runtime mutable state (refs, mutexes) through
request handlers"). The S-class items (timeout, cap, 503 retry-after)
remain blocked on new F\*-typed infrastructure (`time_budget : nat` +
`assume val cancellation_polled : unit -> bool`) per audit §A; this
PR did not regress that — the existing `with_query_timeout` was
extended in shape but not in policy.

**Caveat:** this is a watch-this-space item. The query-timing
record carries an `eval_ms` field that, once the F\* evaluator is
itself instrumented, should be sourced from F\*-side instrumentation
rather than wrapped at the OCaml layer. Filing as deferred per audit
§A; not net-new drift.

### PR #135 — inmem-cottas Phase A.5 re-scope (commit `e2ad715`)

Phase A.5 dispatch had a "encode bytes + intercept parquet_read_*"
plan; the agent timed out and **explicitly reported back that the
plan would have required ~6 distinct parquet probes patched in OCaml,
several of which would qualify as semantic glue rather than pure I/O
routing.**

Recommended re-scope: a new `GB_InMem` graph_backend F\* variant,
~200–400 LoC, F\*-first.

**Audit assessment:** **good signal.** The dispatch process caught
the drift before any patches landed. This is exactly the
audit-by-process intent of the boundary audit — agents explicitly
classify proposed work as "semantic-must-migrate" vs "acceptable
glue" before writing code. Doc landed at
`docs/designissues/in-memory-cottas-phase-a5-block.md`.

### PR #132 — streaming-count-group ORDER BY support

Added support for ORDER BY in the streaming COUNT/GROUP BY fast path.
Implementation lives in F\* (algebra-side). No OCaml-side semantic
additions noted. Not a drift concern.

### PR #131/#133 + lessons note (commit `741a8d7`)

Q01 perf hunt 2026-05-01. The lessons note documents that the fast
path was correct on the wrong layer — the actual bottleneck is
`indexed_dataset_backend`'s `bucket_replace_acc`. No code in this
commit; just diagnosis. Not a drift concern.

### `inmem-cottas: Phase A scaffold` (commit `42af49d`)

Stub returning `None`. No semantic content. Not a drift concern.

### Background ci(linux-x86_64) shadow-build commits

CI artifact bumps. Not a drift concern.

---

## 2. State of in-flight migration PRs

Per audit's 2026-05-01 update:

- **#126 — `json_escape` → SPARQL.JSON.Escape.fst** — merged.
- **#127 — `status_text` + `cors_*` → SPARQL.HTTP.Response.fst** — open.
- **#128 — `/backend-info.json` → SPARQL.HTTP.BackendInfo.fst** — open.
- **#129 — `parliament_label` + `render_queries_index` → SPARQL.HTTP.QueriesIndex.fst** — open.
- **`claude/http-update-sandbox-to-fstar`** — in flight; ~170 LoC of
  update-policy semantics → SPARQL.Update.Sandbox.fst.

Not landed since 2026-05-01. PR statuses not re-checked in this
recheck (no GitHub access this session); the audit number 2026-05-01
remains the canonical source until those merge.

---

## 3. CI purity gate expansion (this commit)

Updated `.github/workflows/check-fstar-purity.yml` to:

### 3a. Watch additional files

Added `formal/fstar/ocaml-output/factoidal_http.ml` and
`formal/fstar/ocaml-output/factoidal_explain.ml` to the diff scope.
Previously the gate only watched
`formal/fstar/experimental_ocaml_glue/*.sh`, leaving the audit's
"factoidal_http.ml has S-class drift" surface uncovered.

### 3b. Pattern 4: re-introduction of migrated functions

If any of the following names re-appears as a top-level `let` in
`factoidal_http.ml`, the gate flags it (soft-mode warning):

```
json_escape  status_text  cors_headers  cors_policy
parliament_label  render_queries_index
sandbox_op  sandbox_update  expand_user_graph
```

These are the functions migrated to F\* (PR #126 merged) or in
flight to F\* (#127 / #129 / sandbox branch) per the 2026-05-01
status. Re-defining them in OCaml would mean a migration regressed.

### 3c. Pattern 5: SIGALRM regression

The audit's §A flagged `Sys.set_signal Sys.sigalrm` based query
timeouts as process-global (a SIGALRM in one query interrupts every
query running in the process) and therefore architecturally wrong.
The existing `with_query_timeout` is grandfathered until the F\*
`time_budget` / `cancellation_polled` infrastructure lands. **New** uses of
`Sys.set_signal Sys.sigalrm` in any watched file are flagged.

### 3d. Pattern 6: planner-shape duplication in explain

Audit #2 in unwind inventory: `factoidal_explain.ml` reimplements
`choose_best_tp_backend` rather than calling F\*'s planner. New
planner-shape `let` definitions in `factoidal_explain.ml`
(`choose_best_tp_*`, `estimate_pattern*`, `order_patterns*`,
`plan_bgp*`) are flagged so duplication doesn't compound.

### What the gate still does NOT catch (deliberately)

- Generic `let` definitions in `factoidal_http.ml` that don't match
  the migrated-function or SIGALRM patterns. Adding observability
  glue, mutable refs, mutexes, JSON renderers — all explicitly
  acceptable per audit's "thin glue" classification — does not
  trigger.
- Any change to `RDF_CottasStore.ml`. That file is extracted from
  F\*; the existing `check-extraction.yml` workflow covers
  extraction sanity. Glue patches that mutate it post-extraction
  are caught via the `experimental_ocaml_glue/*.sh` watch.
- Anything in `bin/<platform>/`, generated JS / WASM, or vendored
  third-party. Those are checked by `check-derived-files.yml`.

### Mode

Soft-mode preserved (`exit 0` even on violations; PR comment
posted). Repo variable `FSTAR_PURITY_HARD=1` flips to blocking. The
audit's 2026-05-01 update doesn't make a recommendation on
flipping; this recheck doesn't either.

---

## 4. Recommendation

Status: **clean**. No fresh drift detected since 2026-05-01. Two
positive signals:

1. PR #136 (timing) stayed within the rule-#11(c) "thin glue"
   surface; the audit's classification absorbs it cleanly.
2. PR #135 (inmem-cottas re-scope) demonstrates the audit's
   process-level review actually *prevented* drift — the agent
   recognised the proposed plan as semantic-glue and reported back
   rather than landing patches.

The expanded CI gate (this commit) tightens coverage for the next
recheck cycle.

**Next recheck**: when #127 / #128 / #129 / sandbox land, or in 2
weeks (whichever comes first). After those land, the
`render_queries_index` / `cors_*` / `parliament_label` /
`sandbox_op` patterns in the gate become guards rather than
optimistic warnings — re-introduction would be a real regression.

**No action required from the user beyond this commit.**
