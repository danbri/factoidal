# Overnight migration session status — 2026-05-06

**Session window:** 2026-05-06 ~22:35h → 06:00h (user's instructions:
"queue up a few clock-hours work on the F\* lifting/migration").

**Goal:** continue the F\*-purity unwind by lifting OCaml-side
semantic logic into F\* modules, scoped so the user wakes up to
self-contained PRs reviewable independently.

This document is a worklog. The PRs themselves are the deliverable;
this is so the user has a clean handoff in the morning rather than
needing to scroll back through the chat transcript.

---

## PRs opened during this session

All target `claude/main`. All carry the CLAUDE.md rule-#11
qualifier in the body. All cherry-pickable independently.

| PR | Title | Branch | Net OCaml LoC retired |
|---:|---|---|---:|
| **#140** | Lift pretty-printers to RDF.Pretty.fst | `claude/rdf-pretty-fstar-migration` | −95 |
| **#141** | Lift parse_cors_value, cors_mode_to_string, simplify select_vars | `claude/select-vars-and-cors-cleanup` | −21 |
| **#142** | audit: 2026-05-06 status update — six more migrations landed/in-flight | `claude/audit-status-2026-05-06` | (doc-only) |
| **#143** | Lift content_type_for_path + path_has_dotdot to SPARQL.HTTP.StaticFiles.fst | `claude/static-files-fstar` | −25 |
| **#144** | Lift N-Quads serializers to RDF.NQuads.Serialize.fst | `claude/nquads-serialize-fstar` | −32 |
| **#145** | Lift update_has_load to SPARQL.Update.Analysis.fst | `claude/update-has-load-fstar` | −4 |
| **#146** | Lift count_dataset_triples + backend_kind_of_cfg into SPARQL.HTTP.BackendInfo.fst | `claude/backend-info-helpers-fstar` | −16 |

**Total net OCaml semantic LoC retired across the seven PRs: ~193.**

Each PR adds the corresponding F\* source plus the extracted .ml file.
The F\* additions total ~390 LoC; the bookkeeping is +390 / −193 in
the strict sense, but the substantive change is the −193 LoC of
duplicated/diverged OCaml-side semantic table that Iron Rule #1
wanted out of OCaml.

## New F\* modules created

- `RDF.Pretty.fst` — RDF term pretty-printers (Turtle/N-Triples styles, prefix abbreviation).
- `SPARQL.HTTP.StaticFiles.fst` — Content-Type and path-traversal-guard.
- `RDF.NQuads.Serialize.fst` — byte-correct N-Quads/N-Triples wire-format serializers.
- `SPARQL.Update.Analysis.fst` — structural predicates over SPARQL UPDATE ASTs.

## Existing F\* modules extended

- `SPARQL.HTTP.Response.fst` — added `parse_cors_value`, `cors_mode_to_string`, `trim_ascii`, helpers.
- `SPARQL.HTTP.BackendInfo.fst` — added `count_dataset_triples`, `backend_kind_of_flags`, `sum_named_triples` helper.

## Audit doc state

`docs/designissues/fstar-ocaml-boundary-audit.md` got a new "Status
update 2026-05-06" section in PR #142. Updated LoC table:

| File | 2026-04-26 | 2026-05-01 | 2026-05-06 (this session) | After all 7 PRs land |
|------|---:|---:|---:|---:|
| `factoidal_http.ml` (S-class) | ~350 | ~50 | ~30 | ~5 |
| `factoidal_cli.ml` (S-class) | n/a | n/a | ~10 | 0 |
| `factoidal_explain.ml` (S-class) | ~580 | ~580 | ~510 | ~440 |
| `RDF_CottasStore.ml` | ~950 | ~0 | ~0 | ~0 |
| `experimental_ocaml_glue/*.sh` | ~2000 | ~250 | ~250 | ~250 |
| **Total** | ~3300 | ~300 | ~250 | ~700 (incl. unchanged glue) |

After all 7 PRs land, the only S-class items remaining in
`factoidal_http.ml` are the architecturally-blocked ones (query
timeout, result-row cap, 503-Retry-After) waiting on the F\*
`time_budget` + `cancellation_polled` infrastructure design.

## Remaining migration candidates I noticed but didn't take on

Listed for the next session. None blocks any PR I've opened; each
is a fresh starting point.

### Tractable in one PR each

1. **`bs_string` + `bound_status` type → `SPARQL.Explain.fst`**.
   `bs_string` is a 5-line diagnostic formatter for the
   `bound_status` variant in `factoidal_explain.ml:264-268`. The
   type is also used by `bs_json`, `tpx_json`, and the
   `tp_explain` record. The smallest version migrates just the
   type + `bs_string`; OCaml callers re-export the constructors
   the same way #139 / #140 did. Larger version pulls in
   `bs_json` + `tp_explain` + `tpx_json` (the Pe5 `--explain`
   JSON output renderer), which is the audit's #2 unwind item.

2. **`recent_query_to_json` + `serve_recent_queries_json` body
   → `SPARQL.HTTP.Admin.fst`** (factoidal_http.ml:1236-1276).
   The renderer is pure modulo a mutex-protected counter snapshot.
   Migration moves the type definitions for `recent_query` and
   `query_timing` plus the JSON template. The mutex/ref state
   stays in OCaml. This was added by PR #136 (per-stage timing);
   the audit currently classifies all of #136 as thin glue, but
   the renderer itself is a "what does the JSON shape look like"
   decision that fits Rule #1.

3. **`backend_source_string` (factoidal_http.ml:2124)**. Joins
   `Filename.basename` results with `", "`. Could split: the
   `", "` separator and overall format are F\* decisions; the
   `Filename.basename` extraction is OS-aware glue. Tiny.

4. **HTTP request-buffer parsing helpers**
   (factoidal_http.ml:758-806):
   `find_header_terminator`, `ci_find`, `extract_content_length`.
   `SPARQL.HTTP.fst` already has `find_4byte`, `header_lookup_ci`,
   `parse_nat` — the OCaml versions are partial duplicates from
   the streaming-read context (where we don't yet have a complete
   request to feed into `parse_http_request`). Could replace with
   thin OCaml wrappers calling the F\* primitives.

### Bigger; need design decision

5. **F\* `time_budget` + `cancellation_polled` infrastructure**.
   The audit's §A documents the design ("`time_budget : nat`"
   threading + an `assume val cancellation_polled : unit -> bool`
   that the OCaml-side timer flips). Once it lands, the existing
   SIGALRM-based `with_query_timeout` in factoidal_http.ml can
   be retired and `Tav5` (result-row cap) and 503 Retry-After
   become straight migrations. This is the natural Phase 2.9
   target per the unwind plan.

6. **Pe5 `--explain` planner deduplication** (factoidal_explain.ml's
   `optimiser_order_via_fstar` etc.). The audit's #2 in unwind
   inventory: `factoidal_explain.ml` reimplements the F\* planner
   (`choose_best_tp_backend`) rather than calling it. The fix is
   to invoke the F\* planner from the explain dump, deferring
   the F\*-side log/dry-plan-mode plumbing so the existing F\*
   evaluator doesn't grow new I/O surface.

### Glue files (do NOT migrate; rule-#11(c) compliant)

- `experimental_ocaml_glue/util_log_runtime.sh` — env-var-gated
  log-line emission, file I/O, mutex. Pure I/O glue. Stays.
- `experimental_ocaml_glue/cottas_pagecache_global_runtime.sh` —
  state-cell threading for the F\* page cache logic. Stays.
- `experimental_ocaml_glue/parquet_footer_runtime.sh` — file
  byte-cache + raw I/O. Stays.
- `experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzzzzzz_token_lookup_runtime.sh`
  — dispatch shim bridging F\* assume_vals to lazy-loaded
  Hashtbls. Stays.

The `experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh`
is a Vav3-style companion-file writer; per the audit, writers
stay in OCaml glue, but the reader path must be in F\*. The reader
already migrated in PR #123. Status: clean.

## Toolchain notes for the next session

- F\* opam install on this box went through twice during the session
  because an unrelated `opam install digestif lwt cohttp ...` for
  `factoidal_http.ml` link triggered an F\* downgrade rebuild
  (going from 2026.03.24 to 2025.03.25~dev). The `--z3version 4.13.3`
  flag becomes mandatory on the older F\* version — the project's
  `build-ocaml.sh` already passes it so CI is unaffected; only
  ad-hoc `fstar.exe foo.fst` invocations need the flag.
- The existing `.gitignore` in `formal/fstar/` ignores all `*.ml`,
  but the convention for the `ocaml-output/` directory is that
  extracted .ml files **are tracked** (49 of them are committed on
  `claude/main` today, including the recent #126/#127/#128/#129
  outputs). New extracted files need `git add -f` to bypass the
  ignore. All seven PRs above follow this pattern.
- The session sandbox's local checkout works against a localhost
  git proxy, so `git ls-remote` is the authoritative source for
  what's on origin. PRs created via GitHub MCP show up in the
  remote; locally-pushed branches need a fetch round-trip to
  appear in `origin/*`.

## Recommendation for the morning

1. **Review and merge #140-#146 in any order.** They're
   independent. CI on each will run the full F\* extract +
   native compile + js_of_ocaml + wasm pipeline; if any one fails
   the rest are unaffected.
2. **#142 is the audit doc update**; it's safe to merge first
   since it's documentation only.
3. **The freeze in CLAUDE.md rule #11** can be lifted to the
   migrate-to-F\* direction — the audit is substantively complete
   per #142's recommendation. The user is the right person to make
   that edit; I deliberately didn't touch CLAUDE.md autonomously.
4. **The rest of the candidates** (sections 1–6 above) are
   ranked by complexity. Tractable items 1–4 are each one
   afternoon's work; items 5–6 are real design work and benefit
   from explicit user direction.

## End-of-session ledger

Files this session created/modified:

- New F\* sources: `RDF.Pretty.fst`, `SPARQL.HTTP.StaticFiles.fst`,
  `RDF.NQuads.Serialize.fst`, `SPARQL.Update.Analysis.fst`.
- Extended F\* sources: `SPARQL.HTTP.Response.fst`,
  `SPARQL.HTTP.BackendInfo.fst`.
- Modified OCaml: `factoidal_http.ml`, `factoidal_cli.ml`,
  `factoidal_explain.ml`.
- Modified build: `build-ocaml.sh` (extract + compile lists).
- New extracted .ml files (force-added): `RDF_Pretty.ml`,
  `SPARQL_HTTP_StaticFiles.ml`, `RDF_NQuads_Serialize.ml`,
  `SPARQL_Update_Analysis.ml`, `SPARQL_HTTP_BackendInfo.ml`.
- Updated audit doc: `fstar-ocaml-boundary-audit.md` (status
  section).
- This status doc.

Each of the seven PR descriptions has a concrete CI test plan; the
existing omega3 F\*-purity gate (PR #138's expanded form) runs on
each PR's diff and should be clean (these are *retirements*, not
new growth).

Sleep well; status above.
