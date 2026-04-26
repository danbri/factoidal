# Sin7 scratch — BGP tail-rec hunt (2026-04-26)

**Goal:** Find and fix all remaining non-tail-rec list walkers in the BGP-result
→ SPARQL-evaluator → row-list path. The HTTP-level `--max-rows 50000` cap
(Tav5 commit `4ff2321`) checks `List.length rows > cap` AFTER the BGP
evaluator returns; if the evaluator's internal list ops blow the stack on
3M-element results, we crash before the cap can fire.

**Yod6 starting point:** `formal/fstar/RDF.CottasStore.fst:903`
`cottas_ondisk_rows_to_quads` recurses BEFORE consing — non-tail-rec on
3M-row results.

**Approach:**
1. Rewrite `cottas_ondisk_rows_to_quads` with `_acc` companion + `List.Tot.rev`,
   matching Tav5's `json_rows_body_acc` pattern.
2. Grep for other non-tail-rec offenders on the path
   `cottas_ondisk_search` → `run_query`. Targets: `SPARQL11.Algebra.fst`
   (distinct/project/extend), `SPARQL11.Store.fst`, `RDF.Graph.Executable.fst`.
3. Verify each fix with `fstar.exe` on the changed file (no `make verify`,
   no `--lax`).
4. Best-effort smoke build; daemon restart left to main thread.

**Constraints:** 1.5 h wall-clock. No `--lax`. No semantic changes. Don't
touch `formal/fstar/experimental_ocaml_glue/` (Tet3's scope). Don't push.
W3C must stay 1657/1/0/4.
