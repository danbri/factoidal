# 2026-05-07 — F\*/OCaml Boundary Audit

**Phase 0** of
[`2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md).
Catalogue only — no proposed code, no F\* modules. Surfaces the migration backlog
that Phases 1-9 of the recovery plan consume.

This is a fresh audit applying the **corrected taxonomy** from
[CLAUDE.md](../../CLAUDE.md) Iron Rule #11 (only `assume val` realisations
are acceptable inside the verified library boundary; companion-file writers
with byte-layout logic are violations; consumer/binding code belongs
outside `formal/fstar/ocaml-output/`). It supersedes the 2026-04-26 →
2026-05-06 status updates that previously occupied this filename, which
applied the older A/P/S taxonomy and have served their purpose.
The earlier text is preserved in `git log`.

## Status
Done (audit). Recovery Phases 1-9 unblocked.

## Method

Every hand-written `.ml` file in the audit brief and every `.sh` patch under
`formal/fstar/experimental_ocaml_glue/` and
`formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/` was
classified against the taxonomy in
[`CLAUDE.md`](../../CLAUDE.md) Iron Rule #11 augmented by the
boundary-audit-taxonomy table in
[`2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md).

Approach:
- `wc -l` + `grep -nE "^(let|and) "` to enumerate top-level defs.
- Read first 30 lines of every file (intent + context).
- Sampled bodies for any function whose role was non-obvious.
- Read every glue patch end-to-end (they are short).
- For `w3c_runner.ml`, `factoidal_cli.ml`, `rdfc10_runner.ml`, `owl_runner.ml`:
  classified at file granularity (CONSUMER, RELOCATE Phase 8) per the audit
  brief's instruction not to walk them line-by-line.

The codename glossary referenced throughout is
[`docs/code-name-glossary.md`](../code-name-glossary.md).
No new short-codes are introduced here.

## Classification taxonomy

| Code | Category | Action |
|---|---|---|
| `EXTRACTED` | F\*-extracted `.ml` (must carry GENERATED header). | Verify only. |
| `ASSUME-IO` | OCaml realisation of an `assume val` for pure I/O / OS primitive. | ALLOWED. |
| `ASSUME-HOST` | OCaml realisation of an `assume val` calling a host engine (regex, etc.). | ALLOWED. |
| `ASSUME-CRYPTO` | OCaml realisation of an `assume val` for a vendored crypto primitive. | ALLOWED. |
| `CONSUMER` | Hand-written consumer / binding (argv, file I/O, dispatch shim around F\* extract). Not part of the verified library. | RELOCATE to `bin/<consumer>/`. |
| `VIOLATION-SEM` | Carries an RDF/SPARQL semantic decision (planning, optimisation, prune, byte-layout for an on-disk format, etc.). | MIGRATE to F\*. |
| `MIXED` | Mostly consumer but with semantic decisions inline. | SPLIT — extract the semantic part to F\*; keep consumer scaffolding. |
| `UNCLEAR` | Role not yet determined; flag for follow-up. | INVESTIGATE before migrating. |

---

## 1. Per-file summary

| File | LoC | Top-level defs | EXTRACTED | ASSUME-* | CONSUMER | VIOLATION-SEM | MIXED |
|---|---:|---:|---:|---:|---:|---:|---:|
| `factoidal_http.ml` | 2598 | 108 | 0 | 0 | 95 | 8 | 5 |
| `factoidal_cli.ml` | 1135 | 34 | 0 | 0 | 33 | 0 | 1 |
| `factoidal_explain.ml` | 671 | 19 | 0 | 0 | 14 | 4 | 1 |
| `factoidal_dump_nq.ml` | 113 | 7 | 0 | 0 | 7 | 0 | 0 |
| `factoidal_serve.ml` | 20 | 1 | 0 | 0 | 1 | 0 | 0 |
| `w3c_runner.ml` | 2851 | 96 | 0 | 0 | 96 | 0 | 0 |
| `rdfc10_runner.ml` | 474 | 38 | 0 | 0 | 38 | 0 | 0 |
| `owl_runner.ml` | 516 | 42 | 0 | 0 | 42 | 0 | 0 |
| `cottas_ondisk_smoketest.ml` | 95 | 4 | 0 | 0 | 4 | 0 | 0 |
| **Totals (audited)** | **8473** | **349** | **0** | **0** | **330** | **12** | **7** |

Notes:

1. **Zero `EXTRACTED` files in this audit set.** All 9 hand-written `.ml` files
   are consumers / runners / glue. The actual extracted output (`SPARQL11_*`,
   `RDF_*`, `Parser_*`, `Parquet_*`, etc.) is *not* in this audit list because
   it is auto-generated — the audit's job is to classify the hand-written
   layer that calls into it.
2. **Zero `ASSUME-*` realisations in this audit set.** All `assume val`
   realisations live in the glue-patch directories
   (`experimental_ocaml_glue/` + `minimal_regrettable_glue_code_each_with_an_open_issue/`),
   which patch already-extracted modules in place — see Section 3.
3. The 12 `VIOLATION-SEM` + 7 `MIXED` rows are the migration backlog.
   Section 2 enumerates them.
4. The 8 codename violators (Yod6, Tet3, Lamed3, Mem5, Pe5, Bet7, Tav5, Heth3)
   are not all in this audit set's `.ml` files — most live in the glue-patch
   layer that injects post-extraction OCaml semantic logic into already-
   extracted `.ml` files (see Section 3, e.g.
   `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh`). The OCaml-side surface those
   patches expose lives mostly in `RDF_CottasStore.ml` (extracted, then
   patched) — a file the recovery plan calls out explicitly.

---

## 2. Violator inventory (the migration backlog)

The 8 codename violators (Yod6, Tet3, Lamed3, Mem5, Pe5, Bet7, Tav5, Heth3)
are all **RETIRED** as of #200 Section A — see the Codename violator
confirmation table below for per-codename target F\* modules and the #200
issue body for the merging-PR/commit references. The Phase 8 consumer
relocation (#200 Section D) moved `factoidal_http.ml` and
`factoidal_explain.ml` to `bin/factoidal-http/` and `bin/factoidal-explain/`,
so the file:line columns below are pinned to the original audit-set paths
for archaeology; the canonical residence today is under `bin/`.

The "File:line" column points to where the violator surfaces in the audit set
(`factoidal_http.ml`, `factoidal_explain.ml`); the underlying logic also lives
in `experimental_ocaml_glue/*.sh` (Section 3) which post-extraction patch the
F\*-extracted COTTAS modules. Phase 4-7 migrations replace both.

| File:line | Function | What it does (one sentence) | Target F\* module | Effort | Codename | Status |
|---|---|---|---|---|---|---|
| `factoidal_http.ml:735` | `exception Query_timeout` + `with_query_timeout` (l. 1433) | Per-query SIGALRM-based wall-clock cancellation. | `SPARQL.Eval.TimeBudget.fst` (+ `assume val now_ms`) | M | **Heth3** | DONE — `1a22822` + `07659a1` |
| `factoidal_http.ml:950` | `result_cap_response` | Result-row-cap circuit breaker (HTTP 413 when row count > cap). | `SPARQL.Eval.Limits.fst` (`take n` combinator) | XS | **Tav5** | DONE — #205 |
| `factoidal_http.ml:961` | `exceeds_cap` | Decision predicate "row count > cap". | `SPARQL.Eval.Limits.fst` | XS | **Tav5** | DONE — #205 |
| `factoidal_http.ml:1013, 1052` | inline `match exceeds_cap … with Some n -> result_cap_response` | Cap policy applied to SELECT and CONSTRUCT/DESCRIBE branches. | `SPARQL.Eval.Limits.fst` (consumer call site only post-migration) | XS | **Tav5** | DONE — #205 |
| `factoidal_http.ml:1407` | `query_timeout_response` | Heth3 504-body construction (delegates the JSON shape to `SPARQL_HTTP_Response.query_timeout_response_body`, but the OCaml `with_query_timeout` retains the SIGALRM decision logic). | `SPARQL.Eval.TimeBudget.fst` | M | **Heth3** | DONE — `7bf06a3` + `ce7d0bc` |
| `factoidal_http.ml:613` | `prewarm_cottas_columns` | Calls Vav3-companion-boot prewarm; thin wrapper, but it embeds the policy "always prewarm on open" decision. | `SPARQL.Plan.Loader.fst` (companion-file-present? + decide load mode) | S | **Bet7** (lazy-populate side) | DONE — #218 |
| `factoidal_explain.ml:205` | `cottas_estimate_quick` | "Quick" cardinality estimate via `cottas_ondisk_estimate`; OCaml-side wrapper around an F\* call but the call-site policy "use the bitmap fast path here, fall back below" lives here. | `SPARQL.Plan.Estimate.fst` | S | **Mem5** | DONE — #215 |
| `factoidal_explain.ml:246` | `explain_triple_pattern_against_store` | Per-pattern bound-status classification + estimate composition. The bound-status classification (`BS_Var/Hit/Miss/Other`) is in F\* (`SPARQL_Explain`) post-PR #170, but the *driver* that walks `tp.tp_s/tp_p/tp_o` and composes the result is still here. | `SPARQL.Plan.Explain.fst` | M | **Pe5** | DONE — #219 |
| `factoidal_explain.ml:373` | `optimiser_order_via_fstar` | Iteratively calls `S.choose_best_tp_backend` to recover join order — wraps F\* but the "iterate till empty" loop is the planner-replay logic. | `SPARQL.Plan.Explain.fst` | S | **Pe5** | DONE — #219 (now sole ground truth post-`ae1b912`) |
| `factoidal_explain.ml:385` | `optimiser_order_for_bgp_from_explains` | Parallel re-implementation of the F\* planner using pre-computed estimates ("DIVERGES from F\*" diagnostic). Explicitly a known-divergent shadow per its own comment. | `SPARQL.Plan.Explain.fst` (delete; rely on F\* ground truth alone) | S | **Pe5** | DONE — DELETED in `ae1b912` (#200 Section C 4/4) |
| `factoidal_explain.ml:473` | `print_index_use_summary` | Hard-codes which `.dict`/`.presence`/`.offsets` companion files the planner consults given the per-pattern bound-status. Pure semantic mapping (which capabilities apply for which bound shape). | `SPARQL.Plan.Explain.fst` | S | **Pe5** | DONE — #219 |
| `factoidal_explain.ml:508` | `explain_query` | Top-level driver: parse, open, walk algebra, compute estimates, render. MIXED — outer scaffolding is consumer (open files, print headers, time it); inner per-BGP loop carries the semantic plan-replay decision. | `SPARQL.Plan.Explain.fst` (semantic core) + `bin/factoidal-explain/` (consumer) | M | **Pe5** | DONE — semantic core in F\* (#219); consumer relocated in Phase 8 (`582647d`) |
| `factoidal_http.ml:467` | `load_cottas_dataset` | Walks COTTAS `quad_row` cache, rebuilds an `rdf_dataset` with default + named-graph buckets. Bucketing by `qr_g` is a semantic decision: "no `qr_g` → default graph; `Some gid` → named graph keyed by IRI." | `RDF.Store.Loader.fst` (or `Parser.BallyhooCOTTAS` extension) | S | — (drift, not codename) | DONE — `42f06bb` |
| `factoidal_http.ml:544` | `load_cottas_part` | Folds multiple `--data-cottas` files into one `rdf_dataset`. The "default-graph triples concatenate; named graphs append (first-match wins)" rule is a semantic merge decision. | `RDF.Store.Loader.fst` | S | — | DONE — `b090c4e` |
| `factoidal_http.ml:669` | `build_dataset_backend` | MIXED — combines in-memory + cottas-ondisk into one `dataset_backend` with explicit `GB_Union`. The dispatch policy (when to use `GB_Union`, how to fold per-graph backends) is a semantic decision; the `Hashtbl`-based grouping is consumer scaffolding. | `RDF.Store.Capabilities.fst` (Phase 1) + `RDF.Store.Combine.fst` | M | — | DONE — `4a72f63` |
| `factoidal_http.ml:908` | `select_vars` | MIXED — explicit-projection branch dispatches to `SPARQL11_Algebra.select_item_vars` (good); the star-projection fallback (collect-distinct-vars-in-first-seen-order) is in OCaml. SPARQL spec defines this; should be in F\*. | `SPARQL11.Algebra.fst` (`star_project_vars`) | XS | — | DONE — `select_vars` star-projection covered by `4a72f63` |
| `factoidal_http.ml:1330` | `parse_and_run_timed` | MIXED — outer scaffolding is timing instrumentation (consumer); the dispatch on `query.q_form` and the per-form timing-record construction is semantic. | `SPARQL.HTTP.RunQuery.fst` for status codes + error body templates. | M | — | DONE — parse_error_status / eval_error_status + parse_error_body / eval_error_body migrated to F\* `SPARQL.HTTP.RunQuery`. |
| `factoidal_http.ml:967` | `run_query` | MIXED — query-form dispatch + serialiser selection + cap policy + result-format selection. The serialiser dispatch logic (which serialiser per `RF_*` value) is genuine F\*-territory; the per-call eprintf trace is consumer. | `SPARQL.HTTP.RunQuery.fst` strategy enum + per-form-format dispatch. | M | — | DONE — `serialiser_strategy_for_ask` / `_select` / `_construct_describe` in F\* `SPARQL.HTTP.RunQuery`; OCaml side reduced to a tiny strategy → host-function-pointer lookup. |
| `factoidal_http.ml:2070` | `try_static_route` | MIXED — outer routing dispatch is consumer; the URL-path-to-route mapping (`/sparql`, `/admin`, `/backend-info.json`, `/parliament-queries.json`) is part of the SPARQL Protocol surface and arguably belongs in `SPARQL.HTTP.Routes.fst`. | `SPARQL.HTTP.Routes.fst` for the path table; consumer for the `Some/None` dispatch. | S | — | DONE — protocol-path classification migrated to F\* `SPARQL.HTTP.Routes.is_sparql_protocol_path`; `try_static_route` now consumer-only. |

### Codename violator confirmation

| Codename | Confirmed at | Target F\* module |
|---|---|---|
| **Yod6** | `experimental_ocaml_glue/cottas_ondisk_zzzzz_ondisk_index.sh` (`.p.presence` writer) + `factoidal_explain.ml:491` (Yod6 label in summary) | `SPARQL.Plan.Pruning.fst` over `RDF.Store.Columnar.PresenceBitmap` |
| **Tet3** | `experimental_ocaml_glue/cottas_ondisk_zzzzz_ondisk_index.sh` (`.s.presence` + `.o.presence` writers) + `factoidal_explain.ml:488,494` | `SPARQL.Plan.Pruning.fst` + `RDF.Store.Columnar.CompoundPresence.fst` |
| **Lamed3** | `experimental_ocaml_glue/cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` (writer + reader) + `factoidal_explain.ml:497` | `RDF.Store.Columnar.OffsetIndex.fst` (NEW) + `SPARQL.Plan.AccessPath.fst` |
| **Mem5** | `experimental_ocaml_glue/cottas_ondisk_runtime.sh` (estimate fast path) + `factoidal_explain.ml:205,366` | `SPARQL.Plan.Estimate.fst` |
| **Pe5** | `factoidal_explain.ml` (entire file, named for `--explain`) | `SPARQL.Plan.Explain.fst` (extends what's in `SPARQL.Explain.fst` post-PR #170) |
| **Bet7** | `experimental_ocaml_glue/cottas_ondisk_z_lazy_open.sh` (lazy-populate dictionaries) + `factoidal_http.ml:613` | `SPARQL.Plan.Loader.fst` decision + `RDF.Store.InMemory.fst` builder |
| **Tav5** | `factoidal_http.ml:950,961,1013,1052` (result-cap circuit breaker) | `SPARQL.Eval.Limits.fst` (`take n stream` combinator) |
| **Heth3** | `factoidal_http.ml:735,1407,1433` (SIGALRM, exception, with_query_timeout, query_timeout_response) | `SPARQL.Eval.TimeBudget.fst` + `assume val now_ms` realisation |

All 8 codename violators present. No additional codename violators discovered
during the audit (the `Sade3` mention in
`experimental_ocaml_glue/cottas_ondisk_runtime.sh` refers to a *completed*
Phase B migration of `cottas_ondisk_search`/`_estimate` to F\* — not an open
violator).

---

## 3. Glue-patch inventory

### `formal/fstar/experimental_ocaml_glue/` — backend / on-disk shadows

| Patch file | What it does (one sentence) | Category | Action |
|---|---|---|---|
| `ballyhoo_hdt_runtime.sh` | Adds an HDT runtime-cache module to `Parser_BallyhooHDT.ml` (Hashtbl-backed term cache populated from F\*-verified probes). | `VIOLATION-SEM` (cache shape + ID-allocation policy is a semantic decision; the original probes are F\*-pure) | MIGRATE — `RDF.Store.HDT.fst` runtime view; cache becomes `assume val open_hdt_handle`. |
| `cottas_column_seq_runtime.sh` | Realises four `assume val`s in `RDF.CottasStore.ColumnSeq.fst`: abstract `cottas_column` ≈ `string option array`, `_length`, `_get`, and `probe_parquet_column_decode_in_row_group_seq` (calls existing list-shape decoder + `Array.of_list`). | `ASSUME-IO` (rule #11(c) thin glue: `Array.length` / `Array.unsafe_get` + a list→array shim) | ALLOWED — leave in place, ensure the matching `assume val`s remain in `RDF.CottasStore.ColumnSeq.fst`. |
| `cottas_inmem_encoder_runtime.sh` | Realises the `cottas_inmem_open` `assume val`. Phase A: stub returns `None`. Phase A.5 (per the comment) will land the real encoder + buffer registry. | `MIXED` (today: `ASSUME-IO` stub; tomorrow: byte-layout writer if Phase A.5 lands here) | INVESTIGATE — when Phase A.5 lands, the byte-encoding goes into F\* (`serialize : data -> Tot (list u8)`); the OCaml realisation reduces to `write_bytes`. Currently a stub, so no immediate action. |
| `cottas_ondisk_runtime.sh` | (1) Implements `cottas_ondisk_open` (parquet decode + dict/revmap construction). (2) **Replaces** the F\*-extracted `cottas_ondisk_search` / `_estimate` / `_decode_*` with `Hashtbl`-backed equivalents. Per the patch's own header: "PERFORMANCE: replace the extracted F\* … the F\* definitions in `RDF.CottasStore.fst` remain the verification spec." | `VIOLATION-SEM` (the explicit reason `RDF.CottasStore.fst` is "decorative" per the recovery-plan disaster note) | MIGRATE — Phases 4-7. The cottas_ondisk_open piece can be split: pure-IO `read_parquet_column` `assume val` realisations + F\*-side dictionary + revmap build. The Hashtbl overlay must go away (the F\* spec already exists). |
| `cottas_ondisk_z_lazy_open.sh` | **Bet7.** Rewrites `build_handle_and_tables` to skip subject + object dictionary populate at open; adds `Cottas_ondisk_lazy` module that builds them on first call. | `VIOLATION-SEM` | MIGRATE — `SPARQL.Plan.Loader.fst` (Phase 3). |
| `cottas_ondisk_zzzzz_ondisk_index.sh` | **Vav3.** (1) Realises 6 `assume val` byte-range I/O primitives in `RDF.CottasStore.OnDiskIndex.fst` (mmap, read u32/u64/byte/string, file size). (2) Adds an OCaml `Cottas_companion_writer` that produces the `.dict` + `.presence` files. (3) Adds a boot orchestrator. | `MIXED` — (1) `ASSUME-IO` and ALLOWED. (2) byte-format spec is now in F\* (`RDF.CottasStore.DictWriter.fst` + `RDF.CottasStore.PresenceWriter.fst`); the OCaml writer is a perf-optimised realisation under Option B with hash-witness CI tests. (3) consumer `MIXED` — when-to-build is a Loader policy decision. | (2) DONE — `2b2b138` (DictWriter) + `f6d2352` (PresenceWriter); (3) policy migration still pending. |
| `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` | **Lamed3.** Builds a third companion file `<cottas>.p.offsets` with per-(row_group, predicate) row positions. Byte format defined in F\* `RDF.CottasStore.OffsetsWriter.fst`; OCaml writer is the perf-optimised realisation. | `ASSUME-IO` (Option-B perf realisation with hash-witness CI test) — was `VIOLATION-SEM` pre-`c0412b7` | DONE — #200 PR4 (`c0412b7`); F\* `serialize_offsets` + `parse_offsets` + 4-fixture roundtrip CI witness. |
| `cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh` | **Compound (predicate, object) presence-bitmap writer (`.po.presence`).** Byte format defined in F\* `RDF.CottasStore.CompoundPresenceWriter.fst`; OCaml writer is the perf-optimised realisation. | `ASSUME-IO` (Option-B perf realisation with hash-witness CI test) — was `VIOLATION-SEM` pre-`435af40` | DONE — #200 PR3 (`435af40`); F\* `serialize_compound_presence` + `parse_compound_presence` + 4-fixture roundtrip CI witness. |
| `cottas_ondisk_zzzzzzzzzzzzzzzzz_token_lookup_runtime.sh` | Realises four `ondisk_lookup_{subj,pred,obj,graph}_id_global` `assume val`s by calling Bet7's `ensure_*_loaded` + `Hashtbl.find_opt`. | `MIXED` (`ASSUME-IO` shape but the `ensure_*_loaded` semantics depend on Bet7's lazy-populate decision) | SPLIT — once Bet7 is migrated to `SPARQL.Plan.Loader.fst`, this collapses to a pure `assume val` realisation. |
| `cottas_pagecache_global_runtime.sh` | Realises `assume val pcache_decode_in_row_group_global`: a process-level mutable `ref` holding the page-cache record; thread-safe wrapper. Pure plumbing; F\* owns LRU/clock semantics. | `ASSUME-IO` (rule #11(c) thin dispatch shim) | ALLOWED — leave in place. |
| `cottas_runtime.sh` | Adds `Ballyhoo_cottas_runtime` module to `Parser_BallyhooCOTTAS.ml`: runtime caches + backend hooks materialised from F\*-verified probes. | `MIXED` — runtime caches with ID-allocation policy are semantic decisions; underlying probes are F\*-pure. | SPLIT — fold the cache-shape decisions into F\* (capability-record), keep file I/O as `assume val`s. |
| `parquet_footer_runtime.sh` | Realises `parquet_read_tail_hex` (raw file I/O over the parquet footer). | `ASSUME-IO` | ALLOWED — pure I/O. |
| `util_log_runtime.sh` | Realises `assume val emit` for `Util.Log.fst`: env-var-controlled log level, ISO-8601 timestamp, file-or-stderr, mutex. | `ASSUME-IO` (logging is the canonical "I/O sink" example) | ALLOWED. |
| `parquet_zstd_stubs.c` | C stubs for libzstd. (Not a `.sh` patch but lives in the directory.) | `ASSUME-IO` (vendored binding to libzstd, akin to HACL\* policy) | ALLOWED — document under `formal/third_party/` policy when the README is added. |

### `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/`

| Patch file | What it does (one sentence) | Category | Action |
|---|---|---|---|
| ~~`53_blank_node_variable_rewriting.sh`~~ | Rewrote `PS_BNode`/`PT_BNode` in query patterns to fresh variables for entailment regimes. | RETIRED | DONE — w3c_runner wired to F\* `rewrite_query_bnodes_pattern`; patch deleted (`03142c4`). Issue #53 closed. |
| `57_service_client_bind.sh` | Realises `assume val service_endpoint_lookup` via OCaml mutable hashtable populated by the runner from `qt:serviceData` declarations. | `ASSUME-HOST` (host-engine call-out: in real deployments this becomes an HTTP fetch — explicitly "host-defined" per SPARQL Federated Query spec) | ALLOWED — keep `assume val service_endpoint_lookup` and document it under the `ASSUME-HOST` category in `RDF.Store.Capabilities`. |
| `62_forward_ref_wiring.sh` | Wires forward-ref `assume val`s for mutual recursion in `SPARQL11_Algebra.ml` (eval_expr_ebv, eval_expr_fwd, eval_exists_fwd, eval_property_path_fwd, eval_subselect_fwd). | `MIXED` — the mutable-ref dispatch is `ASSUME-IO`-shaped (host-language plumbing for cyclic deps F\* extraction emits as failwith); the resolution is "wire to the real implementation," which means the implementation IS in F\*. | ALLOWED-with-caveat — the dispatch shim is rule-#11(c)-compliant; track issue #62 to either (a) collapse the muts in F\*'s extraction model or (b) document this as a permanent realisation pattern. |
| `63_regex_hash_uuid_stubs.sh` | Replaces failwith stubs for `regex_match`, `regex_replace`, `hash_md5`/`sha1`/…/`sha512`, UUID/STRUUID. | `MIXED` — `regex_*` are `ASSUME-HOST` (correctly host-defined per SPARQL 1.1, per IO-verification doc); `hash_*` should become `ASSUME-CRYPTO` (HACL\* binding); UUID should become an F\*-defined `mk_v4` + `assume val random_bytes` per the IO-verification doc. | SPLIT — keep regex realisations; migrate UUID byte-format to F\* (`ThirdParty.UUID`); migrate hashes to HACL\* binding (`ThirdParty.HACL`). Issue #63. |
| `64_sparql_parser_escape_stubs.sh` | Now PARTIAL post-2026-05-10. Realised in F\* `SPARQL11.Parser.fst`: `utf8_of_codepoint` (`1d2b669`) and `process_iri_escapes` (`e79c387`). Still residual in the patch: `process_string_escapes` (the hard one — uses `failwith` on surrogate codepoints; F\* migration needs `option string` signature redesign that ripples through `scan_string` and downstream). | `VIOLATION-SEM` (residual `process_string_escapes`) — half of the original 3 stubs migrated. Issue #64. |
| `65_base_iri_resolution.sh` | RETIRED 2026-05-11. The patch is now a no-op stub kept as audit trail; previously declared `current_base_iri_ref` + injected `resolve_tok_iri` at every `Tok_IRI` site + rewrote `eval_select_query` save/restore + rewrote the `E_IRI_fn` arm. F* `SPARQL11.IRI.Resolve.fst` (Step 1 / `4ff…factor`) now hosts the resolution algorithm; `eval_expr_with_base / eval_pattern / filter_solutions / having_filter / sort_solutions / aggregate_groups / …` all take `(base : option wf_iri)` (Steps 2a/2b/2c — `e1ffba4`/`8b7d9f6`/`dff3bdc`); `eval_select_query` reads `q.q_base` directly; the parser-side pre-pass `resolve_relative_iri_tokens` already covered relative IRIs (`SPARQL11.Parser.fst:2561, 3959, 4024`). | `PURE-FSTAR` — was `VIOLATION-SEM` pre-`db95b73` | DONE — #200 (`db95b73`); 631/631 SPARQL 1.1 + 1031/1031 RDF 1.1 pass. Issue #65 closed. |
| ~~`66_zero_length_property_path.sh`~~ | Augmented zero-length property-path matching to include reflexive pairs from constant IRIs/BNodes in the query pattern even on empty graphs. | RETIRED | DONE — F\* fix (`9364009`); patch deleted (`0265099`). Issue #66 closed. |
| `67_rdfxml_validation.sh` | Thin OCaml adapter glue: defines `Rdfxml_error` exception, `attrs_to_pairs` record→tuple shim, and `option string -> raise` translators. The validation logic (NCName, forbidden-name lists, mutual-exclusion rules) lives in F\* `XML.Wellformedness.fst`. | `ASSUME-IO` (Option-B style: F\* spec + thin OCaml glue) — was `VIOLATION-SEM` pre-`3ec93d5` | DONE — #200 PR5 (`3ec93d5`); 166/166 W3C rdf-xml suite still passes. Issue #67 retired. |
| `68_unicode_boundary_workarounds.sh` | NTriples-only post-2026-05-10. The (2) Turtle surrogate-validation half was deleted as dead code: `Parser.Turtle.fst` already emits the four `valid_codepoint` guards directly (lines 1020/1038/1099/1117), confirmed byte-identical extraction with vs. without the patch. (1) NTriples `0xD7FF` → `0xD800` sed remains: workaround for `FStar.Char.char_code`'s strict-`<` exclusion of U+D7FF. | `VIOLATION-SEM` (residual NTriples sed) — unblock by upstream F\* stdlib fix to `char_code` OR by a project-local codepoint type. Issue #68. |
| `69_runner_io_glue.sh` | I/O-glue patches to `w3c_runner.ml`: namespace constants, expanded entailment-regime detection (sd:entailmentRegime), `file_to_base_uri` helper, query-file-as-base, exception handling for negative syntax tests. | `CONSUMER` — `w3c_runner.ml` is itself the consumer; this glue is consumer-on-consumer. | RELOCATE — when `w3c_runner.ml` moves to `bin/w3c-runner/` (Phase 8), inline this patch into the relocated source tree. |
| `89_fast_string_primitives.sh` | Realises 6 `assume val`s in `Parser.FastString.fst` (`fs_byte_*`, `fs_cp_*`) via direct OCaml `String.length` / `String.unsafe_get` / `String.sub` + an inline UTF-8 decoder. | `ASSUME-IO` (byte-indexed primitives — host-language fast-path for what F\* already proves correct) | ALLOWED — keep; document under `assume val` realisation policy. |
| ~~`95_stack_safe_list_ops.sh`~~ | Replaced 3 non-tail-rec list ops in `SPARQL11_Algebra.ml` with tail-rec equivalents. | RETIRED | DONE — F\*-side tail-rec rewrites: `dedup_er` + `add_to_groups` (`34a2e4c`); concatMap migration (`9ce7690`); `@` migration (`97f9d44`); patch deleted (`56108f9`). Issue #95 closed. |
| `103_parquet_ascii_string_fast_path.sh` | ASCII-only fast-path for `FStar_String` ops in `Parquet_Footer.ml` (works because hex-encoded payloads are pure ASCII). | `ASSUME-IO`-ish — observationally equivalent host-language optimisation; same caveat as #95. | INVESTIGATE — same fix as #95: route through `Parser.FastString` `assume val`s instead of post-extraction `sed`. Issue #103. |
| `181_shacl_validate_stub.sh` | Realises `assume val shacl_validate` as a host-language stub (returns conformant report) until the SHACL engine lands. | `ASSUME-HOST` (placeholder for SHACL Core, sister track #181) | ALLOWED-pending — collapses to a pure F\* call once SHACL Core engine reaches Phase 2. Issue #181. |
| `202_now_ms.sh` | Realises `assume val now_ms` for `SPARQL.Eval.TimeBudget.fst` (Heth3) via `Unix.gettimeofday`. | `ASSUME-IO` (clock — canonical I/O-glue category per rule #11(c)) | ALLOWED — permanent fixture. |
| `README.md` | Documentation. | n/a | n/a |

---

## 4. Companion-file writer audit

Per Iron Rule #11 corrected taxonomy (and the IO-verification doc): byte-format
spec MUST be in F\* (`serialize : data -> Tot (list u8)`); OCaml is reduced to
`write_bytes`. The hash-based round-trip witness pattern then proves the
on-disk bytes match the F\*-computed bytes.

| Artifact | Byte-format-spec location | Writer location | Round-trip witness exists? | Action |
|---|---|---|---|---|
| `<cottas>.s.dict` (subjects) | F\* `RDF.CottasStore.DictWriter.fst` defines `serialize_dict` + `parse_dict` (round-trip) and `RDF.CottasStore.OnDiskIndex.fst` defines the reader | OCaml `Cottas_companion_writer.write_dict_file` in `cottas_ondisk_zzzzz_ondisk_index.sh` (perf-optimised realisation under Option B) | YES (`tests/unit/dict_writer_roundtrip.ml`, 4 fixtures, SHA-256 pinned) | DONE — #200 PR1 `2b2b138` (2026-05-09). |
| `<cottas>.p.dict` (predicates) | same | same | YES (same test) | DONE — same commit. |
| `<cottas>.o.dict` (objects) | same | same | YES (same test) | DONE — same commit. |
| `<cottas>.g.dict` (graphs) | same | same | YES (same test) | DONE — same commit. |
| `<cottas>.s.presence` (subject presence bitmap) | F\* `RDF.CottasStore.PresenceWriter.fst` defines `serialize_presence` + `parse_presence` (round-trip); reader in `RDF.CottasStore.PresenceBitmap.fst` | OCaml `Cottas_companion_writer.write_presence_file` (perf-optimised realisation under Option B) | YES (`tests/unit/presence_writer_roundtrip.ml`, 5 fixtures, SHA-256 pinned) | DONE — #200 PR2 `da132dd` (2026-05-10). |
| `<cottas>.p.presence` (Yod6 — predicate presence) | same | same | YES (same test) | DONE — same commit. |
| `<cottas>.o.presence` (object presence) | same | same | YES (same test) | DONE — same commit. |
| `<cottas>.g.presence` (graph presence) | same | same | YES (same test) | DONE — same commit. |
| `<cottas>.p.offsets` (Lamed3 — per-rg predicate row offsets) | F\* `RDF.CottasStore.OffsetsWriter.fst` defines `serialize_offsets` + `parse_offsets` (round-trip; `COTO` magic, header, u64 rg_offsets array, u32 subject_ids); reader in `RDF.Store.Columnar.OffsetIndex.fst` | OCaml `Cottas_offset_idx` in `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` (perf-optimised realisation under Option B; preserves the 6 s → 200 ms win) | YES (`tests/unit/offsets_writer_roundtrip.ml`, 4 fixtures, SHA-256 pinned) | DONE — #200 PR4 (2026-05-10). |
| `<cottas>.po.presence` (compound predicate-object presence) | F\* `RDF.CottasStore.CompoundPresenceWriter.fst` defines `serialize_compound_presence` + `parse_compound_presence` (round-trip; `COPO` magic, header, u64 rg_offsets, u64 pairs); abstract bitmap reader in `RDF.CottasStore.CompoundPresenceBitmap.fst` | OCaml `Cottas_compound_po_writer` in `cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh` (perf-optimised realisation under Option B) | YES (`tests/unit/compound_presence_writer_roundtrip.ml`, 4 fixtures, SHA-256 pinned) | DONE — #200 PR3 `435af40` (2026-05-10). |
| COTTAS in-memory encoder (`cottas_inmem_open` Phase A.5) | Phase A: stub returns `None`. Phase A.5 deferred. | OCaml stub today; would land in `cottas_inmem_encoder_runtime.sh` | NO (no writer yet) | INVESTIGATE — when Phase A.5 lands, keep byte assembly in F\* per rule #11. Coordinate with Phase 6 of recovery plan. |

**Summary:** 11 companion-file artifacts across 3 distinct byte formats
(`.dict`, `.presence`, `.offsets`, `.po.presence`). All 11 currently have
their **byte assembly in OCaml**; reader sides are partially in F\*
(headers + bit-tests for `.dict` / `.presence`; nothing for `.offsets` or
`.po.presence`). Zero round-trip witnesses exist today.

---

## 5. Done-criteria progress meter

Re-stated from the recovery plan; current numbers below.

| Metric | Target (Phase 9) | Current |
|---|---:|---:|
| `VIOLATION-SEM` entries (Section 2) | 0 | **0** (all retired — codename rows via #200 Section A; `load_cottas_dataset`/`load_cottas_part`/`build_dataset_backend`/`select_vars` via `42f06bb`/`b090c4e`/`4a72f63`; Pe5 divergent shadow deleted in `ae1b912`) |
| `MIXED` entries (Section 2) | 0 | **0** (all retired — `try_static_route` → `SPARQL.HTTP.Routes.fst` (`5bd0614`); `parse_and_run_timed` + `run_query` → `SPARQL.HTTP.RunQuery.fst`) |
| Hand-written `.ml` files in `formal/fstar/ocaml-output/` (excluding `EXTRACTED`) | 0 (all under `bin/<consumer>/`) | **2** (`fstar_pure_hashes.ml` for vendored crypto, `sparql_parser_stubs.ml` for SPARQL parser host-engine call-outs — both permanent rule #11(c) fixtures, on the CI gate's allowlist as of `1490711`) |
| Glue patches that aren't `ASSUME-*` (Section 3) | 0 | **~9** (`VIOLATION-SEM`: `ballyhoo_hdt_runtime.sh`, `cottas_ondisk_runtime.sh`, `cottas_ondisk_z_lazy_open.sh`, #64, #68. `MIXED`: `cottas_ondisk_zzzzz_ondisk_index.sh` (policy half — writer half done), `cottas_inmem_encoder_runtime.sh` (Phase A.5 deferred), `cottas_ondisk_zzzzzzzzzzzzzzzzz_token_lookup_runtime.sh`, `cottas_runtime.sh`, #62, #63, #103. Plus `CONSUMER` #69 which should relocate to `bin/w3c-runner/` now Phase 8 is done. — #65 retired in `db95b73`) |
| Companion-file artifacts with byte-format-spec in F\* (Section 4) | 11 / 11 | **10 / 11** (DictWriter, PresenceWriter, CompoundPresenceWriter, OffsetsWriter all migrated under Option B; only the deferred COTTAS in-mem encoder remains) |
| Hash-based round-trip witnesses in CI (Section 4) | 11 | **10** (`tests/unit/dict_writer_roundtrip.ml`, `presence_writer_roundtrip.ml`, `compound_presence_writer_roundtrip.ml`, `offsets_writer_roundtrip.ml`; pinned SHA-256s on representative fixtures) |
| Codename violators retired (Yod6, Tet3, Lamed3, Mem5, Pe5, Bet7, Tav5, Heth3) | 8 / 8 | **8 / 8** ✅ (#200 Section A) |

Notes on the hand-written-`.ml` count:

- Phase 8 is **complete**. The audit set's 9 hand-written `.ml` files
  (95 + 113 + 20 + 474 + 516 + 671 + 1135 + 2851 + 2603 LoC)
  all live under `bin/<consumer>/` now. The auxiliary files
  (`parquet_probe.ml`, `factoidal_http_client.ml`,
  `factoidal_http_main.ml`, `factoidal_serve_*.ml`, `OWL_QueryEval.ml`,
  `OWL_QueryRewrite.ml`, `test_fstar_parser.ml`) are likewise relocated
  or deleted (`1490711`). The CI gate
  (`.github/workflows/check-ocaml-output-cleanliness.yml`, `98e1205`)
  enforces that no new hand-written `.ml` lands in `ocaml-output/`.
- The two remaining files (`fstar_pure_hashes.ml`,
  `sparql_parser_stubs.ml`) are on the CI gate's permanent allowlist
  per rule #11(c) — vendored crypto bindings and SPARQL parser
  host-engine call-outs.
- The only `.ml` in `formal/fstar/ocaml-output/` going forward should be
  `EXTRACTED` files (auto-generated by F\*) plus a small fixed set of
  `assume val` realisations the build allows in.

---

## 6. Sequencing addendum

The recovery plan's default order is preserved:

1. **Phase 1 — `RDF.Store.Capabilities.fst` contract.**
   Dependency root. Blocks 2, 3, 4, 6.
2. **Phase 2 — Columnar reorg.**
   Pure namespace-level. Renames `RDF.CottasStore.PresenceBitmap.fst`,
   `CompoundPresenceBitmap.fst`, `PageCache.fst` under `RDF.Store.Columnar.*`.
   Required by 4, 6.
3. **Phase 3 — Easy violators (parallel).**
   - **Tav5** (`SPARQL.Eval.Limits.fst`, XS effort): retires Tav5 in
     `factoidal_http.ml:950,961,1013,1052`. Independent of COTTAS work.
   - **Bet7** (`SPARQL.Plan.Loader.fst`, S effort): retires
     `cottas_ondisk_z_lazy_open.sh` + `factoidal_http.ml:613`. Depends on
     Phase 2.
4. **Phase 4 — Pruning + estimate (one PR).**
   `SPARQL.Plan.Pruning.fst` + `SPARQL.Plan.Estimate.fst`. Retires
   **Yod6**, **Tet3**, **Mem5** simultaneously (they share the
   presence-bitmap reader).
5. **Phase 5 — Time budget (2 PRs: design + migration).**
   `SPARQL.Eval.TimeBudget.fst` + `assume val now_ms` realisation +
   `SPARQL.Eval.Limits.fst` interaction. Retires **Heth3**.
6. **Phase 6 — Offset index (1-2 PRs).**
   `RDF.Store.Columnar.OffsetIndex.fst` (NEW) — file format spec +
   verified reader + serialiser + roundtrip lemma + `SPARQL.Plan.AccessPath.fst`
   chooser. Retires **Lamed3**. **Performance-critical**: must preserve
   the 6 s → 200 ms win. Benchmark required.
7. **Phase 6.5 (audit-suggested, slot between Phase 6 and 7).**
   Companion-file-writer migration: per Section 4, all 11 artifacts must
   gain `serialize`/`parse`/roundtrip lemma in F\* and a hash-roundtrip CI
   test. The `.po.presence` writer (Compound) and `.p.offsets` writer
   (Lamed3) are covered by Phases 4 + 6 respectively; this sub-phase
   tackles the simpler `.dict` + `.presence` per-column writers
   (`Cottas_companion_writer` in `cottas_ondisk_zzzzz_ondisk_index.sh`).
8. **Phase 7 — Explain (1 PR).**
   `SPARQL.Plan.Explain.fst` builds on Phases 4 + 6. Retires **Pe5**,
   relocates `factoidal_explain.ml` to `bin/factoidal-explain/`.
9. **Phase 8 — Consumer relocation (1 large PR).**
   Move all hand-written `.ml` from `formal/fstar/ocaml-output/` to
   `bin/<consumer>/`. Sweeps:
   - `factoidal_http.ml` + `factoidal_http_main.ml` + `factoidal_serve.ml`
     + `factoidal_serve_debug.ml` + `factoidal_serve_jsoo.ml` →
     `bin/factoidal-http/`
   - `factoidal_cli.ml` + `factoidal_dump_nq.ml` → `bin/factoidal-cli/`
   - `factoidal_explain.ml` → `bin/factoidal-explain/` (after Phase 7
     extracts the semantic core)
   - `w3c_runner.ml` + `69_runner_io_glue.sh` → `bin/w3c-runner/`
   - `rdfc10_runner.ml` → `bin/rdfc10-runner/`
   - `owl_runner.ml` + `OWL_QueryEval.ml` + `OWL_QueryRewrite.ml` →
     `bin/owl-runner/`
   - `cottas_ondisk_smoketest.ml` → `bin/cottas-smoketest/`
   - `factoidal_http_client.ml` → `bin/factoidal-http/` (or merge if dead).
   Tighten `check-fstar-purity.yml` so `formal/fstar/ocaml-output/`
   admits only `EXTRACTED` files and a fixed-list of `assume val`
   realisations.
10. **Phase 8.5 (audit-suggested) — Migrate remaining
    minimal_regrettable `VIOLATION-SEM` patches.** Issues #53, #64, #65,
    #66, #67, #68 each become a small F\*-only PR. None block earlier
    phases (they're independent of the COTTAS planner work) but they
    must be retired before Phase 9.
11. **Phase 9 — Drop the qualifier.** Audit shows zero violators; CI gate
    enforces; rule #11 caveat removed.

### Adjustments suggested by this audit

- The audit confirms the recovery plan's default order is correct. The
  only addition is **Phase 6.5 (companion-file-writer migration for
  `.dict`/`.presence`)** which the original plan implicitly assumed
  Phase 4 covered but in fact Phase 4 only retires Yod6/Tet3/Mem5
  (the *consumers* of the bitmaps); the *writers* (byte assembly) are
  separate work.
- Tav5 (Phase 3) genuinely is XS effort and could land before any of the
  Capabilities/Columnar reorg. Suggest doing it as a kickoff PR to build
  reviewer confidence.
- Issue #95 (stack-safe list ops) and #103 (ASCII fast-path) are both
  `MIXED` because they post-extraction-rewrite F\* output. The right fix
  for both is to change the F\* source to extract correctly; this can
  happen in parallel with the planner work and isn't in the recovery
  plan's critical path.

---

## Cross-references

- [`CLAUDE.md`](../../CLAUDE.md) — Iron Rule #11 (corrected taxonomy)
- [`docs/designissues/2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md)
  — 9-phase recovery plan; this audit is Phase 0
- [`docs/designissues/2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md)
  — `assume val` taxonomy + hash-based round-trip pattern + HACL\* /
  EverParse / UUID / regex policy
- [`docs/code-name-glossary.md`](../code-name-glossary.md) — Yod6 / Tet3 /
  Lamed3 / Mem5 / Pe5 / Bet7 / Tav5 / Heth3 decoder (historical;
  **no new short-codes** per recovery plan)
