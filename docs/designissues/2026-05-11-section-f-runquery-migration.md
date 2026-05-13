# Section F: `run_query` / `parse_and_run_timed` migration to F*

**Date:** 2026-05-11. Plan output by Plan-agent dispatch from the #200 closeout session.
**Closes:** the last two `MIXED` rows in the boundary audit's Section 2-F.

The F\* shell `formal/fstar/SPARQL.HTTP.RunQuery.fst` (currently 119 lines:
status-codes + error bodies + serialiser-strategy enum) absorbs the dispatch
logic. OCaml retains only host-runtime concerns: exception catching,
wall-clock reads, eprintf logs.

## 1. F\* type additions

**`response_body`** (today at `bin/factoidal-http/factoidal_http.ml:866-870`)
belongs in `formal/fstar/SPARQL.HTTP.Response.fst`. `Response.fst` already
owns the matching value constructors (`result_cap_response_body`,
`query_timeout_response_body`, `cors_headers`) and the type is reused by
every `serve_*` helper (`factoidal_http.ml:1222, 1334, 1645, 1753, 1939`).

```fstar
// SPARQL.HTTP.Response.fst
type response_body = {
  rb_status       : nat;       // HTTP status (200/400/413/500/504/...)
  rb_content_type : string;    // RFC 7231 media-type with charset
  rb_body         : string;    // serialised response payload
}
```

`rb_status : nat`; the OCaml glue uses `Z.to_int` at the boundary (same
pattern as `success_status` already in `RunQuery.fst:44`).

**`query_timing`** (today at `factoidal_http.ml:1091-1100`) belongs in a
new `formal/fstar/SPARQL.HTTP.Timing.fst` companion to
`SPARQL.HTTP.Admin.fst`. It already feeds
`SPARQL_HTTP_Admin.render_timing_log_line` /
`render_timing_response_header` / `render_recent_query_json`
(`factoidal_http.ml:1115-1129, 1209-1220`). Floats stay strings at the
boundary (F\* has no native `float` formatter — `Printf.sprintf "%.1f"`
survives in OCaml as already documented at `factoidal_http.ml:1110-1114`).

```fstar
// SPARQL.HTTP.Timing.fst
type query_timing = {
  qt_parse_ms_str  : string;   // "%.1f"-formatted by OCaml glue
  qt_eval_ms_str   : string;
  qt_format_ms_str : string;
  qt_total_ms_str  : string;
  qt_status        : nat;
  qt_rows          : int;       // -1 = unknown (ASK / parse-error)
  qt_form          : string;    // "SELECT" / "ASK" / "parse-error" / ...
  qt_body_bytes    : nat;
}
```

## 2. F\*-side `run_query` body sketch

```fstar
val run_query :
    query        : SPARQL11_Algebra.query
  -> backend     : SPARQL11_Store.dataset_backend
  -> accept      : string
  -> max_rows    : nat
  -> ask_result  : option bool          // pre-evaluated by OCaml
  -> rows_result : option (list binding_row)  // pre-evaluated by OCaml
  -> Tot response_body
```

**Why split eval from `run_query`?** `S.eval_*_backend_dataset` calls can
throw OCaml-host exceptions (HDT/COTTAS file I/O, Z3-emitted assertion
violations from extracted code with `assume val` realisations). Putting
`try/with` inside the F\* function would force `run_query` into `ML`,
losing `Tot`. Cleaner: OCaml runs the evaluator in a `try`, hands the
resulting option to F\* `run_query`, F\* stays `Tot`. (Rule #11(c) —
host-runtime exception boundary stays in OCaml.)

Body sketch:

1. Match `query.q_form`:
   - `QF_Ask` → take `ask_result`, default `false` on `None`, call
     `serialiser_strategy_for_ask`, dispatch the strategy via an inner
     `Tot` helper that calls
     `SPARQL.Protocol.serialise_response_boolean_{json,xml}`.
   - `QF_Select _` → take `rows_result`, default `[]`. Apply cap via
     `SPARQL_Eval_Limits.cap_reached` with the strict-overflow encoding
     (`mk_cap (max_rows + 1)`, see `factoidal_http.ml:944-947`); on
     overflow return `result_cap_response`. Otherwise pull `vars` via
     the F\*-pure `select_vars_from_query` (NEW — see §6), call
     `serialiser_strategy_for_select`, dispatch to
     `serialise_response_{json,xml,csv,tsv}`.
   - `QF_Construct _ | QF_Describe _` → identical to `QF_Select` but
     routes through `serialiser_strategy_for_construct_describe`.
2. Wrap in `response_body { rb_status = success_status; rb_content_type = ct; rb_body = body }`.

**F\* primitives called:** `SPARQL11_Algebra.{select_item_vars}`,
`SPARQL.Protocol.{parse_accept_header, pick_response_format,
content_type_for, serialise_response_*}`,
`SPARQL.Eval.Limits.{mk_cap, cap_reached}`,
`SPARQL.HTTP.Response.{result_cap_response_body, response_body type}`,
the existing `serialiser_strategy_for_*` from `RunQuery.fst:95-119`.

`response_format_of_accept` (today `factoidal_http.ml:872-874`) is
two-line glue around `SPARQL.Protocol.parse_accept_header` +
`pick_response_format`. Move inline into F\* `run_query`.

## 3. What stays in OCaml (rule #11 classification)

| Item | Loc | Rule | Why |
|---|---|---|---|
| `try/with` around `eval_*_backend_dataset` | `factoidal_http.ml:986-996, 1012-1022, 1050-1060` | #11(c) | Extracted F\* code calls `assume val` realisations (HDT mmap, COTTAS) that can raise OCaml exceptions per untyped FFI. F\* `Tot` cannot catch host exceptions. |
| `Printexc.{to_string, get_backtrace}` | `factoidal_http.ml:993, 1019, 1057, 1392, 1399` | #11(c) | Host-runtime introspection. F\* has no analogue. |
| `Printf.eprintf "[qof3] ..."` instrumentation | `factoidal_http.ml:980, 984, 989, …, 1393` | #11(c) | Side-effecting log output. |
| `Unix.gettimeofday ()` reads | `factoidal_http.ml:1244-1247, 1343, 1351, 1376, 1395` | #11(c) | Non-deterministic host clock. |
| `Printf.sprintf "%.1f"` float formatters | `factoidal_http.ml:1118-1129, 1211, 1217-1220` | #11(c) | F\* has no native `float` formatter. |
| Mutable ring buffer + `Mutex` | `factoidal_http.ml:1139-1163` | #11(c) | Process-global mutable state, threading. |

## 4. OCaml glue surface after migration

Today: ~190 lines (`run_query` ≈ 100, `parse_and_run_timed` ≈ 70, helpers).
After migration: ~50 lines.

```ocaml
let run_query_glue ~backend ~accept ~max_rows query =
  let try_eval thunk = try Some (thunk ()) with e ->
    let bt = Printexc.get_backtrace () in
    Printf.eprintf "[qof3] eval raised: %s\n%s%!" (Printexc.to_string e) bt;
    raise e
  in
  let ask_r, rows_r = match query.q_form with
    | QF_Ask -> (try_eval (fun () -> S.eval_ask_query_backend_dataset query backend), None)
    | _ -> (None, try_eval (fun () -> S.eval_select_query_backend_dataset query backend))
  in
  SPARQL_HTTP_RunQuery.run_query query backend accept (Z.of_int max_rows) ask_r rows_r
```

`parse_and_run_timed` shrinks similarly: parse via
`SPARQL11_Parser.parse_sparql` inside `timed`; on `ParseErr` build response
from F\* `make_parse_error_response`; on `ParseOk` invoke `run_query_glue`
inside `try/with`, then assemble the `query_timing` record by handing
pre-formatted floats to F\*. ~30 lines.

## 5. Migration order — recommended commit boundaries

**Commit 1: F\* type + `run_query` core (additive only).**
Add `response_body` to `SPARQL.HTTP.Response.fst`. Add
`make_parse_error_response`, `make_eval_error_response`,
`make_result_cap_response` constructors to `SPARQL.HTTP.RunQuery.fst`
returning `response_body`. Add `run_query` (taking pre-evaluated
`ask_result` / `rows_result` options). Verify in F\*; no OCaml callers
yet. Greenfield.

**Commit 2: switch HTTP caller to F\* `run_query`.**
Rewrite `factoidal_http.ml:977-1076` (`run_query`) into the ~15-line glue.
Delete OCaml `select_vars`, `exceeds_cap`, `result_cap_response`,
`response_format_of_accept` (now F\*-internal). The OCaml `response_body`
record shadows the F\* one for one commit (re-export
`SPARQL_HTTP_Response.response_body` as a type alias); next commit removes
the alias. Run full HTTP regression suite.

**Commit 3: timing record migration + `parse_and_run_timed` shim.**
Add `query_timing` to `SPARQL.HTTP.Timing.fst`. Rewrite
`factoidal_http.ml:1342-1412` into the ~30-line shim. Delete the OCaml
`query_timing` and `zero_timing` record/value (now F\*-typed). Confirm
`/admin/recent.json` and `X-Factoidal-Timing` byte-identical to
pre-migration.

## 6. Risk register

- **`exceeds_cap` / tav5 SIGBUS circuit breaker**
  (`factoidal_http.ml:1024-1028, 1062-1064`): policy already lives in
  `SPARQL.Eval.Limits.fst`; only the OCaml plumbing is here. Inside F\*
  `run_query` we call `cap_reached` directly on the option-rows. Preserve
  the strict-overflow encoding (`mk_cap (max_rows + 1)`) so existing
  semantics (`> cap` triggers, `= cap` passes) are bit-identical. Add an
  F\* lemma `strict_overflow_iff_gt` to lock it in.
- **`select_vars`** (`factoidal_http.ml:883-897`): the `Select_Vars items`
  branch is already pure F\* (`SPARQL11_Algebra.select_item_vars`). The
  `_` (star-projection) branch walks rows with a `Hashtbl` for first-seen
  order. Add `collect_distinct_vars_in_order : list binding_row -> list var_name`
  to `SPARQL11.Algebra.fst` (a list-`mem` fold; ~10 lines). The Hashtbl
  is a perf hint — fine without for typical row widths (< 50 vars).
- **External callers of `run_query`**: only `bin/factoidal-http/factoidal_http.ml`.
  `bin/w3c-runner/w3c_runner.ml:1579` uses
  `OWL_QueryEval.eval_select_query_owl` directly — a different code path
  (OWL-rewritten queries against in-memory `RDF_Graph_Executable`, not
  the backend-dataset evaluator). Not migrated here.
- **`OWL_QueryEval.eval_select_query_owl` differs from the backend path**
  in two ways: takes a pre-materialised `rdf_graph` not a
  `dataset_backend`; has its own OWL rewrite step
  (`OWL.QueryRewrite.rewrite_query`). Not a candidate for the same
  consolidation in this PR; flag for a future "OWL HTTP path
  unification" issue.
- **`response_body` shadowing**: the OCaml `response_body` is used by
  ~10 unrelated `serve_*` helpers (admin, parliament, static demo,
  component bundle). A type alias bridges Commit 2; Commit 3 removes the
  alias and updates the helpers in one sweep.
- **F\* extraction perf**: `run_query` is small `Tot`. No rlimit risk.
  The cap-strictness lemma is the only proof obligation that might need
  `--z3rlimit 30+`.
- **Backtrace string**: `Printexc.get_backtrace` returns "" when
  backtraces are off. F\* `eval_error_body` (`RunQuery.fst:58-60`)
  handles the empty case fine.

## 7. Effort estimate

| Sub-step | Effort | Verification risk |
|---|---|---|
| Add `response_body` type to `SPARQL.HTTP.Response.fst` | 10 min | None |
| Add `run_query` + helpers to `SPARQL.HTTP.RunQuery.fst` | 1.5 h | Low — compose-only; cap-strictness lemma may need ~30 min |
| Add `collect_distinct_vars_in_order` to `SPARQL11.Algebra.fst` | 30 min | Low — pure list fold |
| Rewrite OCaml `run_query` glue (Commit 2) | 45 min | Medium — byte-identical against test corpus |
| `query_timing` + `parse_and_run_timed` shim (Commit 3) | 1 h | Medium — `/admin/recent.json` byte-exact |
| Update `bin/factoidal-http/dune` deps for new modules | 5 min | None |
| Regression: `dune runtest`, w3c-runner full suite, manual `/admin` smoke | 45 min | Low |
| Boundary-audit doc update (Section 2-F MIXED → PURE) | 10 min | None |

**Total: ~5 hours, single PR or tight three-commit stack.**
