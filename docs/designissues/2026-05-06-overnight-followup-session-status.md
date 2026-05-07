# 2026-05-06 — F\* Purity Unwind: Late-Evening Follow-up Session

## Scope

A second migration push during 2026-05-06, picking up where the
22:35h-onwards session left off. The earlier session's status doc
lives on the `claude/migration-session-status-2026-05-06` branch and
will land on `main` only when [its PR][prior-status-pr] merges; until
then this followup doc deliberately avoids in-tree links to it (a
relative reference would be a dead link on `main` post-merge).

[prior-status-pr]: https://github.com/danbri/factoidal/blob/claude/migration-session-status-2026-05-06/docs/designissues/2026-05-06-overnight-migration-session-status.md

Goal: continue retiring rule-#11 violations (semantic logic in OCaml
glue) by lifting small, independent, byte-for-byte-equivalent helper
functions from `formal/fstar/ocaml-output/factoidal_*.ml` into pure
F\* modules. Each migration is a standalone PR against `claude/main`
so reviewers can land them in any order.

## PRs queued during this session

In addition to PR #155 (`claude/bound-status-fstar`, opened in the
prior session and re-confirmed live here):

### PR #156 — `claude/http-buffer-helpers-fstar`
Lift `find_header_terminator_pos`, `ci_substring_index`, and
`extract_content_length` from `factoidal_http.ml`'s streaming
request reader into `SPARQL.HTTP.fst`. The OCaml `read_full_request`
loop keeps the actual socket I/O; the byte-level decisions move to
F\*. Net `-30` OCaml LoC retired; `+89` F\* LoC including three
smoke tests.

### PR #157 — `claude/cli-json-delegation-fstar`
Retire `factoidal_cli.ml`'s local `json_escape` and `json_term`
duplicates; delegate to `SPARQL.JSON.Escape.json_escape` and
`SPARQL.Protocol.json_term` (both already in F\*). Mirrors the
delegation `factoidal_http.ml` already does. Net `-30` LoC.

### PR #158 — `claude/dump-nq-rdf-format-fstar`
Bring `factoidal-dump-nq` in line with the standard pattern: its
`rdf_format` / `detect_format` / `format_of_string` duplicates of
`RDF.Format.fst` collapse to a re-export typedef + delegation
shims. Adds `RDF_Format.ml` to the standalone
`build-ocaml-serializer.sh` link list. Net `-17` LoC. After this
lands, **all three CLI binaries** (`factoidal`, `factoidal-http`,
`factoidal-dump-nq`) share the same F\*-extracted RDF format
detection rules.

### PR #159 — `claude/template-prefix-fstar`
Lift `template_prefix` (split a user-graph template at the
`{authid}` placeholder) into `SPARQL.Update.Sandbox.fst` alongside
the existing `expand_user_graph` substitutor. The split rule and
the replace rule are now in the same F\* module. Adds
`find_open_brace` helper and three smoke tests. Net `-8` LoC.

### PR #160 — `claude/error-response-bodies-fstar`
Lift the JSON error-body templates `result_cap_response_body` and
`query_timeout_response_body` to `SPARQL.HTTP.Response.fst` next
to the existing `status_text` / `cors_headers` helpers. Both
templates share the same hint text matched by the `/admin` demo
page; centralising prevents drift. Net `-12` LoC.

### PR #161 — `claude/qof3-diagnostics-fstar`
Lift the qof3 instrumentation stringifiers (`qof3_graph_kind`,
`qof3_backend_kind`, `qof3_query_form_str`) into a NEW pure F\*
module `SPARQL.Diagnostics.fst`. Adds the module to the
`build-ocaml.sh` extract list and link order. Putting the
exhaustiveness checks on the F\* side means a new `graph_backend`
constructor will fail extraction with a missing-case error rather
than silently producing the literal `"<unknown>"`. Net `-16` LoC.

## Cumulative impact (this session only)

| Field | Count |
|------|------|
| PRs opened against claude/main | 6 (excluding PR #155 which was already on its branch when this session started) |
| OCaml-side semantic LoC retired | ~113 |
| New F\* helper modules created | 1 (`SPARQL.Diagnostics.fst`) |
| Existing F\* modules extended | 3 (`SPARQL.HTTP.fst`, `SPARQL.HTTP.Response.fst`, `SPARQL.Update.Sandbox.fst`) |
| `assume val` declarations introduced | 0 |
| `--lax` or `admit` introductions | 0 |

All seven PRs verify cleanly under z3 4.13.3 with no `--lax` and
no `admit`. Each compiles to `bin/linux-x86_64/factoidal`,
`factoidal-http`, and `w3c_runner` and passes the `--help` smoke
test.

## What's still pending after this session

The big-ticket items continue to be:

1. **Phase 2.9: F\* `time_budget` + `cancellation_polled` infrastructure.**
   Blocks the `with_query_timeout` migration (Tav5 / 503-Retry-After).
   This is genuinely large because it requires plumbing a
   cancellation token through the SPARQL evaluator's recursive walk.

2. **`bs_json` + `tp_explain` + `tpx_json` (rest of the Pe5
   `--explain` dump).** Stacked on PR #155; blocked until that lands
   so the `bound_status` constructors are in F\*.

3. **`print_query_algebra` + `print_ggp` text-dump renderers.** A
   substantial migration: build a pure F\* `query_algebra_to_text`
   that returns a single string, with the OCaml side becoming
   `output_string out (...)`. ~80 LoC saved if done correctly.

4. **`optimiser_order_for_bgp_from_explains`** — depends on the
   `tp_explain` type which is in factoidal_explain.ml.

5. **Test runner stringifiers** in `owl_runner.ml` and
   `rdfc10_runner.ml` (`term_nq`, `subj_nq`, `triple_nq`,
   `escape_literal_lexical`). Could go in a new
   `RDF.NTriples.Render.fst` or be merged into the existing
   `RDF.NQuads.Serialize.fst` from PR #144.

## Process notes

- **Z3 version bump**: this environment has z3 4.13.3 only;
  `build-ocaml.sh` invokes `fstar.exe` without `--z3version`, so
  individual extraction calls were patched locally to add
  `--z3version 4.13.3`. The local edit was reverted before each
  PR commit so it does not leak into the migration commits.
  CI must already be handling this somehow (perhaps via z3-4.8.5
  on the runner) since none of the prior migrations needed the
  flag. If CI starts failing on the same z3-version error, the
  fix is one line in `build-ocaml.sh`.
- **`libzstd-dev`**: this environment didn't have the dev headers,
  so `Parquet_Footer.o` couldn't link. `apt-get install libzstd-dev`
  fixed it (the build script auto-detects via header probing).
- **Branch hygiene**: each PR is on its own branch off `claude/main`.
  No PR depends on another, so reviewers can merge in any order.

## Recommendation

Review and merge any subset of #155-#161 in any order. They are
small, mechanical, and follow the established factoidal_http.ml
unwind pattern (PRs #126 onwards). Once merged, the next batch can
cover the `bs_json` / `tpx_json` stack on top of #155.
