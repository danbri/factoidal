# F\*/OCaml boundary audit

**Status:** active, written 2026-04-26 in response to reviewer feedback
demanding a function-by-function inventory of what is F\*-authoritative,
what is mechanically extracted, and what is hand-written OCaml that
encodes semantics or policy.

**Trigger:** the project drifted from "F\* is the source of truth" to
"~3000 LoC of OCaml shims override the F\* runtime path." Reviewer
2026-04-26 noted this extends beyond `experimental_ocaml_glue/` to
`factoidal_http.ml` and `RDF_CottasStore.ml`. CLAUDE.md rule #11 now
freezes new semantic growth in these files until the audit is done.

**Companion docs:**
- `fstar-purity-unwind.md` — the migration plan (Phases 2.2 → 2.8).
- `debugging-perf-ecosystem.md` — debugging frameworks per target.
- `claude-rules/anti-patterns.md` — the 25 numbered anti-patterns.

---

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
| Backend dispatch (`build_dataset_backend`) | 670–710 | **A** | Constructs `dataset_backend` value from `dataset_ref` + cottas stores. Trivial. |
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

**factoidal_http.ml summary:** of ~2500 LoC, roughly 300 LoC are
classified **S** (semantic decisions that must lift to F\*) and a
further 100 LoC are borderline. The rest is acceptable glue.

The single biggest **S** item is the **query timeout / cancellation
policy**. The reviewer flagged it; the existing code documents its own
caveat. Phase 2.6 adds it to the unwind.

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
