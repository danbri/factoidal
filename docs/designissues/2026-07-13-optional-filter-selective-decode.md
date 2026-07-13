# OPTIONAL/FILTER: row-index-selective decode for COTTAS on-disk

Date: 2026-07-13. Status: DESIGN (measured, implementation-ready).
Target: q6 OPTIONAL/FILTER 8.83s vs Jena TDB2 2.07s (4.3x) on the gene
corpus — the top remaining query gap after the GROUP BY fast path
(f99bb64) landed.

## The premise correction (measured, committed binary, gene 888,949 quads)

The plan-of-record phrase "column-aware decode" (skip columns the query
does not need) does NOT fix q6: its live-variable set is {s, o1, o2} —
every unbound position of both patterns. Measured decomposition:

    q6 as shipped (OPTIONAL + FILTER)                 9.42s  rows=25088
    BGP1 alone (?s wdt:P1057 ?o1)                     8.93s  rows=25063
    BGP1 + FILTER, no OPTIONAL                        8.91s
    BGP1 projecting ONLY ?s                           8.46s
    BGP1 COUNT-star only (no row materialization)     1.15s
    rare predicate P682 (4 rows), materialized        2.14s

- BGP1 alone is 95% of q6; the LeftJoin hash-join + FILTER cost <0.5s
  (the join was already fixed 2026-07-06). The join is NOT the problem.
- Dropping a projected column saves ~nothing: the walkers decode ALL 4
  Parquet columns per candidate row group BEFORE any per-row filtering
  (walk_candidate_rgs_search_tok_global, RDF.CottasStore.fst:1518-1540;
  pcache_decode_global_auto 930-936).
- The count path ALREADY gates s/o decode on boundness
  (walk_row_groups_count_exact_global, 1134-1159) — 7.8x cheaper on the
  same pattern. That asymmetry is the lever.

## Mechanism: row-index-selective decode

Per candidate row group: (1) decode cheap discriminating columns only
(bound positions + g — g stays always-decoded, issue #267 correctness);
(2) compute matched row indices from those; (3) decode expensive
unbound-but-NEEDED columns ONLY at the matched indices, via a new
primitive `pcache_decode_column_at_indices_global_from_table`
(RLE_DICTIONARY: index-array + dictionary-page lookup restricted to the
requested rows; DLBA/PLAIN: fall back to full-column decode, correct but
unaccelerated — the contract cottas_ondisk_distinct_predicates already
established for missing dictionary pages). Token equality is plain
string equality, global across row groups (cottas_column extracts to
string option array, RDF.CottasStore.fst:656-661) — no per-RG dictionary
remap hazard.

## Capability + composition (the wrong-answer trap)

New `sc_solve_selective : option (triple_pattern_bound -> col_need ->
Tot (list triple))` alongside sc_solve. CRITICAL composition difference
vs sc_distinct_predicates: that one is a shortcut whose caller has a
separate always-correct fallback, so member None => whole-query
fallback is safe. sc_solve_selective STANDS IN for sc_solve — a
None-as-skip composition would silently DROP a union member's rows
(wrong answer, not missed fast path). Therefore union_caps ALWAYS
advertises Some, with a per-member fallback to that member's plain
sc_solve; the delta overlay uses merge_on_read exactly as sc_solve does
(no acceleration when a delta is live, no elision). Both wiring points
land in the SAME commit as the capability (tonight's f99bb64 postmortem
rule).

## Needed-column analysis (new, pure)

`expr_vars : expr -> Tot (list var_name)` over the full ~50-constructor
expr AST (does not exist today; own commit), `query_live_vars`
(projection ∪ FILTER/HAVING/ORDER BY/BIND free vars ∪ SELECT-* =>
everything live), `col_need_for_tp` (bound positions never need decode;
unbound positions need it iff live or a cross-pattern join var or
repeated within the BGP).

## Staged landing (each step gated)

1. expr_vars + live-var helpers (pure, unwired; new unit tests).
2. col_need + sc_solve_selective + COTTAS selective walker family + the
   indexed-decode primitive + its glue
   (experimental_ocaml_glue/cottas_pagecache_indexed_runtime.sh, rule
   #11(c); assume val needs its open issue per rule #3). Gate:
   differential — selective with col_need_all byte-equal to
   cottas_ondisk_search_tok on the gene store; varied need preserves
   every kept position exactly.
3. union_caps + overlay composition (same commit as reachability).
4. One narrow detector (single-BGP bound-predicate shapes, optionally
   under one Filter/LeftJoin wrapper), same fall-through contract as
   every existing detector.
5. Measure q6 (estimate ~1.15-2.5s from the count floor + indexed decode
   of ~35,480 matched rows — ESTIMATE, not a committed number); update
   current-state.md's OPTIONAL/FILTER sentence (obsolescence sweep).
6. Follow-ups: multi-pattern shapes; extend the _limited walker family;
   coordinate with (not duplicate) the S/O offset sidecar — ORTHOGONAL:
   sidecar = row-group selection for bound-S/O point lookups (q3);
   this = within-row-group decode for bound-P shapes (q6). q6 gains
   nothing from the sidecar and vice versa.

## Soundness notes

Blank nodes: inherits (does not add) the existing corpus-wide-stable
bnode-token assumption; flag in the landing commit. DEFAULT graph
sentinel short-circuit (RDF.CottasStore.fst:2615) stays outside
col_need. tp_match never sees partial triples (the detector-gated path
bypasses it; everything else uses full decode).

Full file:line inventory and walker sketch preserved in the 2026-07-13
overnight session transcript; files touched: SPARQL11.Algebra.fst,
RDF.Store.Capabilities{,.Cottas,.Delta}.fst, RDF.CottasStore{,.PageCache}.fst,
new glue script, SPARQL11.Store.fst detector, tests/unit.
