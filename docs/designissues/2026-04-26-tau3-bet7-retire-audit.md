# Phase 2.7 — Bet7 (`cottas_ondisk_z_lazy_open.sh`) retirement audit

**Author:** tau3 (agent)
**Date:** 2026-04-26
**Status:** AUDIT COMPLETE — Classification **(3) Still load-bearing**.
**Recommendation:** DO NOT delete the patch in this phase. Retain it
as the cold-path fallback. Schedule its removal AFTER Phase 2.6 lifts
the lazy populators (or their replacement: F\*-pure mmap'd reader
consultation) into F\* code.

## TL;DR

The unwind doc claims Bet7 is "Largely OBSOLETE post-Vav3 (mmap'd
dicts replace Hashtbls)". That claim is **false in its current form**.
Vav3's `prewarm_via_companions` does NOT bypass the Hashtbls — it
*populates* them via `bulk_load_column_into_tables` and then sets the
`Cottas_ondisk_lazy.mark_*_loaded` flags so Bet7's `ensure_*_loaded`
short-circuit. The runtime read path in `*_fast` functions still
consults `tables.ft_*_tok_to_id` (i.e. the Hashtbls). If Bet7's patch
were deleted today:

1. The Hashtbl-population logic that lives inside Bet7's
   `ensure_*_loaded` (and which Yod6/Tet3 *also* enriched with per-rg
   presence-bitmap building) would vanish from the cold path.
2. Two non-HTTP entry points (`factoidal_cli`, `cottas_ondisk_smoketest`)
   that never call `prewarm_via_companions` would be broken: their
   `*_fast` functions would return `None` for every lookup against an
   empty Hashtbl.
3. The HTTP fallback at `factoidal_http.ml:654` — which wraps
   `prewarm_cottas_columns` in `try/with` and explicitly comments
   "the lazy populators will run on first query as a fallback" —
   would also break when companions are absent or `bulk_load_column_into_tables`
   raises.

## Evidence

### 1. Vav3 populates Hashtbls, doesn't replace them

`formal/fstar/ocaml-output/RDF_CottasStore.ml:3354-3387` (the
`prewarm_via_companions` body, originally from
`cottas_ondisk_zzzzz_ondisk_index.sh`):

```ocaml
for col_idx = 0 to 3 do
  let _ = bulk_load_column_into_tables cottas_path col_idx h tables in
  ()
done;
(* Mark every column as loaded so the lazy populators (Bet7) skip. *)
Cottas_ondisk_lazy.mark_subj_loaded  cottas_path;
Cottas_ondisk_lazy.mark_pred_loaded  cottas_path;
Cottas_ondisk_lazy.mark_obj_loaded   cottas_path;
Cottas_ondisk_lazy.mark_graph_loaded cottas_path;
```

`bulk_load_column_into_tables` writes into the same
`tables.ft_*_tok_to_id` Hashtbls that `ensure_*_loaded` writes into.
So the runtime structure is unchanged; what changed is *who fills
them*, and the marker prevents double-population.

### 2. The runtime read path is still Hashtbl-based

`*_fast` functions consult Hashtbls, not the F\* `OnDiskIndex.fst`
mmap'd reader API. Examples:

- `encode_subject_fast` (`RDF_CottasStore.ml`, see Bet7 patch
  step 4 anchor) does `Hashtbl.find_opt tables.ft_subj_tok_to_id key`.
- `decode_subject_fast` does `Hashtbl.find_opt tables.ft_id_to_subject (Z.to_int id)`.
- Same shape for predicates, objects, graphs.
- `search_fast` and `estimate_fast` likewise consult tables and the
  per-rg presence Hashtbls in `Cottas_ondisk_lazy` (built by Yod6/Tet3
  inside Bet7's `ensure_*_loaded`).

The earlier Phi5 audit (`docs/designissues/2026-04-26-phi5-vav3-readpath-audit.md`,
referenced in the prompt) finding that the F\* `OnDiskIndex` API has
zero production callers is consistent with this: Vav3 currently writes
companions and mmap'd-loads them into Hashtbls, but the F\*-pure
"consult mmap'd region directly" path is not yet wired. Bet7 is
upstream of that work.

### 3. Non-HTTP open paths skip prewarm

`grep` for `cottas_ondisk_open` callers (`/tmp/open_callers.txt`):

| Caller | Calls `prewarm_via_companions`? |
|---|---|
| `factoidal_http.ml:649` (`open_cottas_ondisk_files`) | yes (with `try/with` fallback) |
| `factoidal_explain.ml:619` | yes (with `try/with` fallback) |
| `factoidal_cli.ml:239` (`open_cottas_ondisk_store`) | **NO** |
| `cottas_ondisk_smoketest.ml:55` | **NO** |

`factoidal_cli` and `cottas_ondisk_smoketest` rely entirely on the
Bet7 lazy populators triggering on first `*_fast` invocation. If Bet7
is deleted, these binaries lose the ability to do any encode/decode
against the on-disk store.

### 4. Yod6/Tet3 logic now lives INSIDE Bet7's `ensure_*_loaded`

The current extracted body of `ensure_predicates_loaded` (line ~1204
of the .ml) and `ensure_subjects_loaded` (line ~1108) is much larger
than the original Bet7 patch wrote. Yod6
(`cottas_ondisk_zzz_yod6_pred_presence_prune.sh`) and Tet3
(`cottas_ondisk_zzzz_tet3_subj_obj_prune.sh`) injected per-rg
presence-Hashtbl population into these functions. Deleting Bet7
would also implicitly remove the surface where Yod6/Tet3 inject
their work.

This makes Phase 2.7 a *dependent* of Phase 2.6 in practice, not an
independent deletion. The unwind doc's order-of-operations table is
correct in flagging dependencies (see Phase 2.4's "BLOCKED" section
which already cites Bet7 as a blocker on the *other* side too).

## Classification rationale

- **Truly obsolete (1):** would require the runtime read path to
  consult `OnDiskIndex.fst` mmap'd readers directly, OR for every
  `cottas_ondisk_open` caller to invoke `prewarm_via_companions`
  unconditionally. Neither is true.
- **Partially obsolete (2):** could in principle delete the
  `ensure_*_loaded` calls from `*_fast` functions on the *daemon hot
  path* (where prewarm has already run + marked loaded). But the
  hooks are O(1) hashtbl-mem checks and the markers make them no-ops
  — there is no measurable saving and removing them weakens the cold
  fallback. Net: not worth the risk.
- **Still load-bearing (3):** confirmed. The patch is consulted by
  every CLI/smoketest invocation and by the HTTP cold-fallback path.

## Recommended next steps (NOT in this phase)

1. **Pre-Phase 2.6 cleanup:** add `prewarm_via_companions` (or an
   equivalent) to `factoidal_cli.ml` and `cottas_ondisk_smoketest.ml`'s
   open paths so all consumers exercise the fast warm path. Then
   Bet7's *runtime* role on the warm path becomes purely "no-op
   guard," and the `ensure_*_loaded` calls in `*_fast` could be
   removed in a future commit. The cold path (companions absent)
   still exercises `ensure_*_loaded` for first-time corpus open.

2. **During Phase 2.6:** when Yod6/Tet3 logic is lifted to F\*
   (`RDF.CottasStore.PresenceBitmap.fst`), the per-rg presence
   construction must move OUT of Bet7's `ensure_*_loaded` and into
   either (a) the companion-file *writer* (build .presence next to
   .dict), or (b) a thin F\*-extracted "consult companions" reader.
   Bet7's role contracts to "populate plain Hashtbls only on cold
   path."

3. **Phase 2.7 proper (post-2.6):** once Yod6/Tet3 are gone and
   companions cover all data the Hashtbls hold, evaluate whether
   `ensure_*_loaded` is reachable on any production path. If
   companions are guaranteed-built-on-first-open (writer path is
   I/O glue, allowed by rule #11) and consulted via F\* mmap'd
   readers, Bet7 can finally retire.

## Files of interest (absolute paths)

- `/Users/danbri/working/factoidal/formal/fstar/experimental_ocaml_glue/cottas_ondisk_z_lazy_open.sh`
- `/Users/danbri/working/factoidal/formal/fstar/experimental_ocaml_glue/cottas_ondisk_zzzzz_ondisk_index.sh`
- `/Users/danbri/working/factoidal/formal/fstar/RDF.CottasStore.OnDiskIndex.fst`
- `/Users/danbri/working/factoidal/formal/fstar/ocaml-output/RDF_CottasStore.ml` lines:
  - 252 — `module Cottas_ondisk_lazy`
  - 1108 — `ensure_subjects_loaded` (with Tet3 enrichment)
  - 1204 — `ensure_predicates_loaded` (with Yod6 enrichment)
  - 1252 — `ensure_graphs_loaded`
  - 3354 — `prewarm_via_companions` (Vav3)
  - 1602–1605 — `search_fast` ensures all four
  - 1739–1740, 1765 — `search_fast_limited` ensures s/o/p
  - 1868–1877 — `estimate_fast` conditional ensures
- `/Users/danbri/working/factoidal/formal/fstar/ocaml-output/factoidal_http.ml` lines 620–664 (`prewarm_cottas_columns` + `open_cottas_ondisk_files`)
- `/Users/danbri/working/factoidal/formal/fstar/ocaml-output/factoidal_explain.ml` lines 618–631 (with try/with fallback)
- `/Users/danbri/working/factoidal/formal/fstar/ocaml-output/factoidal_cli.ml` line 239 (no prewarm — pure lazy)
- `/Users/danbri/working/factoidal/formal/fstar/ocaml-output/cottas_ondisk_smoketest.ml` line 55 (no prewarm — pure lazy)

## Action taken in this phase

- Audit doc committed.
- Patch file untouched.
- Unwind tracking table to be updated only when 2.6 unblocks 2.7.
