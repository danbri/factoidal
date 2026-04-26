# Pe5 — `--explain QUERY --data-cottas PATH`: plan dump without execution

Date: 2026-04-26
Subagent: Pe5
Status: scratch

## Problem

Q03 (`?s ?p ?o . ?o a geo:wktLiteral LIMIT 3`) on UK-Parliament regressed
from "graceful empty in 7s" to a 30s `--query-timeout` cap (Heth3). Daemon
trace shows the optimiser walks BOTH BGP triples instead of short-circuiting
on T2's empty bound-object result. We can't see WHY without running the
query for 30s and grepping ~1500 lines of trace.

## Goal — "fix the db to be usable"

Add `factoidal --explain '<SPARQL>' --data-cottas PATH` mode that:

1. Parses query (`SPARQL11_Parser.parse_sparql`).
2. Opens COTTAS store (`Parser_BallyhooCOTTAS.cottas_open_dataset_store` /
   on-disk path via `RDF.CottasStore.cottas_ondisk_open`).
3. Computes plan only:
   - algebra tree pretty-print
   - per-triple-pattern cardinality estimate (`cottas_ondisk_estimate`)
   - chosen join order
   - per-pattern index consultations (Lamed3 `.p.offsets`, Yod6 pred-presence,
     Tet3 subj/obj presence, Mem5 fast path)
4. **Does NOT execute** any BGP walk.
5. Emits human-readable text on stdout, JSON on stderr or `--explain-out=FILE`.

## Approach

Hand-written OCaml in `formal/fstar/ocaml-output/factoidal_cli.ml`. It calls
F*-extracted helpers:
- `SPARQL11_Parser.parse_sparql`
- `SPARQL11_Algebra.parse_to_algebra` (or whatever exists)
- The cottas-on-disk estimate function
- The optimiser's join-ordering primitive (if exposed)

If the optimiser primitives aren't exposed at module boundary, fall back to
walking the algebra tree from OCaml + calling per-pattern estimate. This is
glue, not RDF semantics — rule #15 satisfied as long as we don't *re-implement*
join ordering in OCaml (we just *report* it).

## Scope discipline

DO NOT FIX THE REGRESSION — surface diagnosis, then user/main thread decides.

Time-box: 2 hours wall-clock.
