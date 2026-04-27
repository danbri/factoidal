# Walkthrough — `tools/factoidal-debug-query.sh` against demo Q06

This doc shows what the debug-tool machinery reveals about a real
non-empty query, end-to-end: **parse → algebra → planning → estimation →
execution → return**. The query is the curated demo's #06,
"ArmsLengthBody overview":

```sparql
PREFIX : <https://id.parliament.uk/schema/>
SELECT ?Org ?p ?o
WHERE { ?Org a :ArmsLengthBody . ?Org ?p ?o }
ORDER BY ?p
LIMIT 50
```

The corpus is the UK Parliament 2019-07-27 snapshot (3,143,406 triples,
26 row-groups). Wall-clock: **~7.3 s**. Returns 2 rows.

## Stage 1 — `factoidal-debug-query.sh explain` (planner-only)

Run:

```
tools/factoidal-debug-query.sh explain \
  --data-cottas tmp/ukparliament/CorpusCOTTAS/.../data.cottas \
  -e 'PREFIX : <...> SELECT ?Org ?p ?o
        WHERE { ?Org a :ArmsLengthBody . ?Org ?p ?o }
        ORDER BY ?p LIMIT 50'
```

Output (annotated):

```
=== PARSE ===
PREFIX : <...> SELECT ?Org ?p ?o
WHERE { ?Org a :ArmsLengthBody . ?Org ?p ?o }
ORDER BY ?p LIMIT 50
```
Parser: `formal/fstar/SPARQL11.Parser.fst` (F\*-resident). Builds the abstract syntax tree.

```
=== ALGEBRA ===
Project [?Org, ?p, ?o]
  Slice limit=50
    OrderBy [...]
      BGP
        ?Org rdf:type :ArmsLengthBody
        ?Org ?p ?o
```
Algebra-construction: `formal/fstar/SPARQL11.Algebra.fst` (F\*-resident).
Maps surface SPARQL to the standard SPARQL 1.1 algebra tree. Note the
nested shape: `Project ⊃ Slice ⊃ OrderBy ⊃ BGP`. This means rows from
the BGP go through ORDER BY first, then SLICE LIMIT 50, then PROJECT.
For a 2-row result the LIMIT is a no-op.

```
=== BGP PLAN (2 triples) ===
[T1] ?Org rdf:type :ArmsLengthBody
    p: rdf:type [hit]            ← in predicate dict (Vav3 .p.dict)
    o: :ArmsLengthBody [hit]     ← in object dict (Vav3 .o.dict)
    bound built: true
    predicate-presence: true
    estimate: 120900 row(s)

[T2] ?Org ?p ?o
    estimate: 3143406 row(s)
```
Planner: `S.choose_best_tp_backend` in `formal/fstar/SPARQL11.Store.fst`
(F\*-resident since Phase 2.2 / Pe5). T1's two terms (predicate and
object) are encoded against the per-column dictionaries — both succeed,
so `bound built: true`. The estimate of `120900` for T1 is the
average rg-row-count after Tet3+compound pruning (1 surviving rg ×
~120K rows/rg). T2 has no bound terms, so its estimate is the corpus
total.

```
=== JOIN ORDER ===
F* planner (runtime ground truth): T1(est=120900) T2(est=3143406)
(OCaml parallel reimpl agrees with F*)
```
Smaller-estimate-first ordering. T1 picked first; whatever it binds to
`?Org` becomes a constant for T2's evaluation.

```
=== INDEX-USE SUMMARY ===
Vav3 dict.p.dict     : encode predicates for: T1
Vav3 dict.o.dict     : encode objects for: T1
Yod6 .p.presence     : consulted by plan_candidate_rgs for: T1
Tet3 .o.presence     : consulted by plan_candidate_rgs for: T1
```
Reveals which on-disk indexes the planner actually consults for each
triple. T1 is the prune-friendly one (both p and o bound). T2 has no
bound terms so no index is consulted at planning time.

```
=== ELAPSED ===
parse=0.6ms  open=4431.3ms  algebra=0.0ms  estimate=10.7ms  total=4453.4ms
                            (no execution)
```
Most of the 4.4 s here is **store open** (CLI single-shot: opens the
COTTAS handle and bulk-loads dictionary tokens for all 4 columns,
~908K subjects + ~956K objects). The HTTP daemon pays this once at
startup, not per query.

## Stage 2 — Live HTTP daemon trace (with execution)

The `explain` subcommand stops before execution. To see execution we
hit the daemon and grep the trace for our query:

```
[qof3] parse_and_run: 128 bytes of query text
[qof3] parse_and_run: parsed OK, dispatching run_query
[qof3] run_query: backend={default=GB_Union[GB_Indexed,GB_CottasOnDisk]}
[qof3] calling S.eval_select_query_backend_dataset
```
Front door: `factoidal_http.ml`'s `parse_and_run` accepts the
`application/sparql-query` POST. Backend is `GB_Union` of in-memory
(empty here) and the COTTAS on-disk handle. Calls into F\*'s
`SPARQL11.Store.eval_select_query_backend_dataset`.

### T1 — `?Org rdf:type :ArmsLengthBody`

```
[mem5-trace] estimate_fast_inner: candidates=1/26 (s=_ p=rdf:type o=:ArmsLengthBody)
[mem5-trace] estimate_fast_inner: total=3143406 avg=120900 est=120900
```
Estimator (`mem5_estimate_fast_inner`) walks all 26 RGs, asks each
**three F\* questions** via the Tet3 redirect: "could rg N contain s?",
"could rg N contain p?", "could rg N contain o?". Then it AND-composes
those with the **F\* compound (p, o) bitmap** (issue #104). For 25 of
26 RGs the compound bitmap returns false → `candidates=1/26`.

```
[qof3-trace] search_fast: rg_count=26
[tet3-trace] search_fast rg=0  skipped (could_p=true could_s=true could_o=false compound_ok=false)
[tet3-trace] search_fast rg=1  skipped (...)
... 24 more rgs skipped, 23 of them with `compound_ok=false` ...
[pe4-trace] search_fast rg=16 enter
[pe4-trace] search_fast rg=16 decoded col=0 (subject) rss=1271MB
[pe4-trace] search_fast rg=16 decoded col=1 (predicate) rss=1293MB
[pe4-trace] search_fast rg=16 decoded col=2 (object) rss=1316MB
[pe4-trace] search_fast rg=16 decoded col=3 (graph) rss=1320MB
[pe4-trace] search_fast rg=16 filter-loop start n=122880
[pe4-trace] search_fast rg=16 done matches_so_far=1
[tet3-trace] search_fast: skipped 25/26 rg(s)
[qof3-trace] search_fast: matched 1 row(s) across 26 row group(s)
```
Executor: `search_fast`. **25 of 26 RGs are pruned without ever
touching parquet bytes.** rg=16 is the survivor — full DLBA decode of
all 4 columns, then in-memory filter loop over its 122,880 rows. One
match: the only ArmsLengthBody subject (`<https://id.parliament.uk/eup4DwE5>`).

The cost concentrates in this rg=16 walk: ~3 s for decode + filter.

### T2 — `<eup4DwE5> ?p ?o` (with subject now bound)

```
[qof3-trace] search_fast: bound s=<https://id.parliament.uk/eup4DwE5> p=_ o=_
[tet3-trace] search_fast rg=0  skipped (could_p=true could_s=false could_o=true compound_ok=true)
[tet3-trace] search_fast rg=1  skipped (could_s=false ...)
...
[pe4-trace] search_fast rg=16 enter
[pe4-trace] search_fast rg=16 decoded col=0 (subject) ...
[pe4-trace] search_fast rg=16 done matches_so_far=2
[tet3-trace] search_fast: skipped 25/26 rg(s)
[qof3-trace] search_fast: matched 2 row(s) across 26 row group(s)
```
Different prune signal this time: **subject** absence drives the skip
(`could_s=false` on 25 RGs because the ArmsLengthBody subject token
isn't in their .s.presence bitmap). Compound bitmap can't help (no
bound `(p, o)` pair). Walk rg=16 again: full 4-column decode, find 2
matching rows (the ArmsLengthBody's two property triples in this
snapshot).

```
[qof3] eval_select returned Some 2 rows
[qof3] parse_and_run: run_query returned status=200 body_bytes=504
```
Algebra wraps: ORDER BY sorts the 2 rows by `?p`; SLICE LIMIT 50 is a
no-op for 2 rows; PROJECT is a no-op for the 3 vars already in scope.
Result serialised as SPARQL JSON (504 bytes) and returned.

## What the walkthrough shows

**F\*-resident** (verified spec, runtime ground truth):
- Parser, algebra, planner (`SPARQL11.Parser`, `SPARQL11.Algebra`, `SPARQL11.Store`)
- Per-column presence bitmap (`RDF.CottasStore.PresenceBitmap`, 257 LoC, lemma proven)
- Compound `(p, o)` presence bitmap (`RDF.CottasStore.CompoundPresenceBitmap`, 362 LoC, lemma proven)
- Parquet footer parsing
- Companion-file readers (`RDF.CottasStore.OnDiskIndex`)
- Decisions about WHICH rgs to skip, made at every gate

**OCaml glue** (rule-#11(c) thin dispatch shims):
- `Tet3_fstar_redirect` and `Compound_po_fstar_redirect` — translate
  OCaml types to F\* types, call the F\* presence-bitmap functions,
  return the answer.

**OCaml shadow** (still being unwound — Phase 2.5 / 2.6 pending):
- `cottas_ondisk_runtime.sh` — replaces F\*'s extracted
  `cottas_ondisk_search` / `_estimate` with an OCaml runtime. The walk
  loop (`for rg = 0 to rg_count-1 do ...`) is OCaml; the per-rg
  decisions are F\*-routed.
- `Cottas_ondisk_lazy` Hashtbl populators (Bet7/Tet3/Yod6) — populate
  fallback Hashtbls for corpora without companion files.
- The 4-column DLBA decode itself, when an rg passes prune. This is
  the dominant cost for both T1 and T2 and is the next F\*-shadow
  reduction target (lazy column decode based on row indices).

## Where the 7.3 s goes

| Stage | Cost | F\* / OCaml |
|---|---|---|
| Parse + algebra | < 1 ms | F\* |
| Estimator (78 rg-tests via F\* compound + per-column bitmap) | ~10 ms | F\* via shim |
| T1 — prune 25 rgs (each rg-test = 3 F\* bitmap reads + 1 compound search) | ~5 ms | F\* via shim |
| T1 — walk rg=16 (DLBA decode 4 cols × 122K rows + filter) | ~3 s | OCaml (the unwind target) |
| T2 — prune 25 rgs (subject absence drives skip) | ~5 ms | F\* via shim |
| T2 — walk rg=16 again (same 4-column decode) | ~3 s | OCaml (same target) |
| ORDER BY + SLICE + result serialisation | ~10 ms | F\* (algebra) + OCaml (HTTP) |
| **Total** | **~7.3 s** | |

Both 3-second walks are identical work — there's no decoded-column
cache, so the second walk regenerates everything the first walk
already had on hand. That's a known follow-up; see also issue #104's
discussion of lazy-column-decode in `*_inner`.

## Reproducing this walkthrough

```bash
# Planner-only view (CLI single-shot, pays open cost):
tools/factoidal-debug-query.sh explain \
  --data-cottas tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas \
  -e '<your query>'

# Live trace from the daemon:
LINES_BEFORE=$(wc -l < .claude-runs/factoidal-http-3032-*.log)
curl -X POST -H "Content-Type: application/sparql-query" \
  --data '<your query>' http://127.0.0.1:3032/sparql
tail -n +$((LINES_BEFORE+1)) .claude-runs/factoidal-http-3032-*.log
```

The grep markers worth knowing:
- `[qof3-trace]` — HTTP-side request lifecycle
- `[mem5-trace]` — estimator
- `[tet3-fstar-trace]` — F\* per-column bitmap consultation
- `[compound-po-fstar-trace]` — F\* compound bitmap consultation
- `[tet3-trace]` — per-rg prune outcome (with compound_ok flag)
- `[pe4-trace]` — per-rg walk + column decode + RSS pressure
- `[aleph6-trace]` — LIMIT pushdown / streaming COUNT path
