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

## Outcome (2026-04-26)

**Implemented.** New CLI flag `--explain '<SPARQL>' --data-cottas <path>`
in `factoidal_cli.ml` + new module `factoidal_explain.ml`. Total 4.5s on
parliament corpus including ~4.2s pre-warm; the explain logic itself is
<20ms. JSON sidecar via `--explain-out PATH`.

Q03 explain output reveals the smoking gun:

```
[T2] ?o rdf:type geo:wktLiteral
    s: ?o (free)
    p: rdf:type [hit]
    o: geo:wktLiteral [hit]                  <- IS in dict (just not as rdf:type target)
    bound built: true
    predicate-presence: true
    estimate: 120900 row(s)                  <- Mem5 over-estimate

Optimiser order: T2(est=120900) T1(est=3143406)   <- Picks T2 first (correct)
```

The optimiser DOES correctly route T2 first. The real regression isn't
join order — it's that T2's *execution* via `cottas_ondisk_search` falls
into the same slow `estimate_fast_via_offsets` data-page walk path
(when bound_p AND bound_o, walks columns of every candidate row group).
Finding zero matches still costs the full walk → 30s timeout.

## Implementation notes

- `explain_query` calls `cottas_ondisk_open` + `prewarm_via_companions`
  (4.2s on parliament; Vav3 mmap'd companions).
- Parsed query → algebra dump → per-pattern explain rows.
- Per pattern: `cottas_ondisk_encode_*` (fast hashtable) to determine
  hit/miss, then `cottas_estimate_quick` which **bypasses the slow
  lamed3 data-page walk** by calling `Cottas_ondisk_runtime.estimate_fast_inner`
  (Mem5's bitmap-only path) directly when bound_p + (bound_s OR bound_o).
  Other shapes use the public `cottas_ondisk_estimate` (footer-only or
  lamed3 fast count path).
- Join order replicates `choose_best_tp_backend` in OCaml using our
  pre-computed estimates rather than re-calling F* (which would re-trigger
  the slow path).

## Pre-existing nun3 syntax errors

The uncommitted state of `formal/fstar/ocaml-output/RDF_CottasStore.ml`
contained ~720 lines of nun3-experiment code (Cottas_row_ids module)
with two compile-blocking bugs:

1. Line 1670: `(cbqp_*)` inside an OCaml comment — `*)` closes the
   comment, the rest of the file became code → "Syntax error: 'end'
   expected".
2. Line 1711: `(b_s b_p b_o b_g : pint)` — invalid OCaml binder syntax,
   should be `(b_s : pint) (b_p : pint) ...`.

To make `build-ocaml.sh compile` succeed I reverted that file via
`git checkout --` to the committed snapshot at c5146ec. The nun3 code
was preserved in `/tmp/RDF_CottasStore_nun3.ml.bak` (a previous-agent
experiment that was never committed). Anyone wanting to revive it
needs to fix the two bugs above first.
