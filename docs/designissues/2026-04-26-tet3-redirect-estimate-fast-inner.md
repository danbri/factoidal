# Tet3 retirement step 1: redirect `estimate_fast_inner` to F\* presence bitmap

**Date:** 2026-04-26 21:42Z
**Phase:** 2.6 sub-step (issue #100 family)
**Goal:** smallest commit-sized step that proves the integration shape —
have ONE OCaml call site in `RDF_CottasStore.ml` consult the F\*
`RDF.CottasStore.PresenceBitmap` module instead of Tet3's own
Hashtbls.

## Context

Psi3 just landed `formal/fstar/RDF.CottasStore.PresenceBitmap.fst`
(257 LoC, lemma `rg_contains_token_sound` proven). API:
`bitmap_handle`, `open_bitmap`, `rg_contains_token`,
`rg_could_contain`, `rg_passes_all`. Module is extracted but no
production caller yet.

Vav3's `cottas_ondisk_zzzzz_ondisk_index.sh` already provides OCaml
realisations of OnDiskIndex's `assume val` primitives (mmap-backed),
and parliament corpus has all 4 column .presence companion files on
disk. So calling `RDF_CottasStore_PresenceBitmap.rg_could_contain`
will read the same bytes Tet3's Hashtbls were derived from.

## Choice of call site

`estimate_fast_inner` (lines 1853-1930 of post-extraction
`ocaml-output/RDF_CottasStore.ml`) is the cleanest target because:
- it's a read-only path (no result rows allocated);
- Yod6/Tet3 instrumentation already isolates `bound_p`/`bound_s`/
  `bound_o` lookup at lines 1903-1906 (one block);
- equivalence test is straightforward: same estimate output for the
  same query implies the F\*-extracted reader returned the same bits.

## Shape

**(a)** Edit Tet3's `.sh` patch so that, AT this one call site, the
OCaml code goes through a thin shim that:
1. Resolves `cottas_path -> .{s,p,o}.presence` companion paths
2. Calls `RDF_CottasStore_PresenceBitmap.open_bitmap` once per column
   per (path) — cached
3. Uses `rg_could_contain oh rg bound_tok_id` from the F\* module
4. Falls through to existing Tet3 Hashtbl path if the F\* open
   returns `None` (safe fallback — same semantics as Tet3's "no
   presence info -> include" rule).

This is rule #11(c) "trivial dispatch shim that calls F\*-extracted
code" — acceptable. The Hashtbls remain populated for the OTHER call
sites (`search_fast_inner` two gates, `search_fast_limited_inner`
gate), which keeps blast radius to one site.

The token-id translation (string -> nat) is done by F\*'s
`OnDiskIndex.companion_encode` (already extracted). Tet3 currently
uses string-keyed Hashtbls; we must convert to F\*'s nat-id form for
the F\* module call. The simplest path: read the
`tables.ft_{subj,pred,obj}_tok_to_id` mapping (already populated) for
the bound token, get the int id, pass it to the F\* function.

## Plan

1. Re-extract: `./build-ocaml.sh extract` (first time including
   PresenceBitmap.ml in ocaml-output).
2. Edit `cottas_ondisk_zzzz_tet3_subj_obj_prune.sh` to add a
   substitution that wraps the `estimate_fast_inner` candidate-
   counting loop. The loop body becomes:
   ```ocaml
   let could_p =
     match estimate_could_p_via_fstar path rg bound_p tables with
     | Some b -> b
     | None -> Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p in
   (* same for could_s, could_o *)
   ```
   where `estimate_could_p_via_fstar` lives in a helper module added
   by the patch — and that helper is the only new code, calling
   `RDF_CottasStore_PresenceBitmap.rg_could_contain`.
3. Tag the trace lines `[tet3-fstar-trace]` so we can confirm the
   F\*-routed path is hit.
4. Verify build clean, run smoke test (Q03-shape query), run W3C.

## Acceptance

- F\* verifies clean (no `--lax`).
- Build compiles.
- Smoke query `?o a geo:wktLiteral` (or simpler unbound-on-parliament)
  produces SAME estimate as before.
- W3C unchanged from baseline (1657 pass per recent commits).
- New traces show `[tet3-fstar-trace]` lines emitted on
  estimate_fast_inner calls — proves the F\* path was actually hit.
- Commit: small, includes patch edit + scratch doc + rebuilt
  binaries via build-ocaml.sh.

## Out of scope (next step)

- Migrating `search_fast_inner`'s gate (the actual 4-second cost site)
  — that's a separate commit; this run is integration-shape proof.
- Removing Tet3's Hashtbl population. They stay populated for the
  other unmigrated sites.
- Lifting the call-site INTO F\* (Shape (b)) — would require a small
  F\* wrapper in `RDF.CottasStore.fst` and changes to the F\* runtime
  signature. Defer.
