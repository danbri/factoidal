# Bet6 — User-Facing Import Documentation (reading log)

Date: 2026-04-25.
Branch: `claude/main`.
Goal: write `docs/import/{from-trig,from-nquads,from-turtle,README}.md` so a
new user can get RDF data from disk into a COTTAS artifact and serve it.

## Source material consulted

- `tools/corpus_pipeline.py` — the actual importer. Subcommand
  `materialize-nq-cottas-corpus` does the work: pyoxigraph (or rdflib
  fallback) → strict N-Quads → pycottas.rdf2cottas. Outputs:
  `<corpus-root>/<chunk-name>/<version>/data.{cottas,factbin,nq}` plus
  `source-info.ttl`, `summary.json`, and a TOC at
  `<corpus-root>/toc/data.nt`.
- `tools/cottas_bridge.py` — wrapper for benchmarking (informative; not
  primary user path).
- `tmp/factoidal_cottas_harness.py` — bench harness; shows the
  `--data-cottas` query path and the `FACTOIDAL_COTTAS_BRIDGE=/missing` /
  `PYCOTTAS_PYTHON=/missing` sanity-check trick.
- `bin/darwin-arm64/factoidal --help` (and `cottas-import --help`,
  `cottas-info --help`, `serve --help`) — confirms current CLI surface.
  `factoidal cottas-import` is a shim that execs `python3
  tools/corpus_pipeline.py`.
- `docs/cottas-import-howto.md` — pre-existing how-to. Covers venv setup,
  pycottas install, and the `materialize-nq-cottas-corpus` invocation.
  Already documents the `STRING_DICTIONARY_PAGE_SIZE_LIMIT=1` Parquet
  encoding caveat and the per-format conversion strategy.
- `docs/cottas-format-v1.md` — the v1 format contract; cross-referenced
  from each guide.
- `docs/designissues/cottas-native-backend.md` — design context for the
  query side.
- `formal/fstar/Parser.{TriG,NQuads,Turtle}.fst` — confirms factoidal does
  natively understand all three formats at parse time, which is relevant
  for the alternative path of `factoidal serve --dataset FILE.trig`
  (parse on every startup) vs the COTTAS path (parse once, serve fast).

## Importer surface, as actually shipped

The user-prompt referenced `tools/ukparliament_trig_to_cottas.py` and a
`hybrid_escape` variant. Neither exists in the working tree (only a
stale `__pycache__/ukparliament_trig_to_cottas.cpython-314.pyc` survives).
Looking at git log this file is not in any commit on `claude/main`.
The canonical importer is `tools/corpus_pipeline.py`. I'll document
that. The `factoidal cottas-import` subcommand is the supported front
door — it execs the Python pipeline.

Note: `factoidal cottas-import --help` currently fails with
`ModuleNotFoundError: No module named 'rdflib'` because the shim execs
`python3` (system) and the system Python doesn't have rdflib installed.
The how-to mitigates this by running the venv's Python directly with
`PYCOTTAS_PYTHON=...`. Documenting this gap.

## Quirks worth surfacing in user docs

1. **Pycottas is a pre-step, not a runtime.** Factoidal queries COTTAS
   files natively via the F\*-extracted Parquet/Zstd reader. Pycottas
   appears only at import time.
2. **DELTA_LENGTH_BYTE_ARRAY only.** Factoidal's reader requires
   non-dictionary string pages today; pycottas's defaults work, but
   custom DuckDB pipelines must set
   `STRING_DICTIONARY_PAGE_SIZE_LIMIT 1`.
3. **N-Triples imports go to the default graph.** No `<g>` in the
   .nq output. To wrap a single-graph Turtle into a named graph, the
   user has to write a 4-line shell sed/awk pre-step (or use rdflib
   to load + re-serialise as TriG). The importer doesn't expose a
   `--default-graph-iri` for the `materialize-nq-cottas-corpus`
   subcommand — only `--default-graph-iri` exists on `import-line-rdf`.
   I'll document this gap.
4. **Bnode label collisions.** The importer interns terms by raw text,
   so `_:b1` from file A and `_:b1` from file B will alias. Concatenate
   on disk by relabelling first if you import multiple files.
5. **Memory.** The pyoxigraph path streams; the rdflib fallback loads
   the whole graph into memory (so a 3M-quad Parliament TriG would
   blow up rdflib but flies through pyoxigraph).
6. **The TOC writes `data.nt`.** The TOC is itself N-Triples
   describing the materialised chunk, useful when factoidal serves
   multi-graph corpora later. Today most users only need
   `<chunk>/v1/data.cottas`.
7. **Serve-time auto-detection via `--data-cottas`.** No need to
   re-parse RDF on startup.

## Suggested follow-up validation tests for the importer

- A round-trip test: TriG → cottas → SPARQL `CONSTRUCT { ?s ?p ?o }
  WHERE { GRAPH ?g { ?s ?p ?o } }` → diff against canonical N-Quads
  produced by riot.
- Quad-count parity: `wc -l data.nq` vs `factoidal cottas-info` quad
  count.
- Graph-count parity for TriG: count distinct GRAPH IRIs in source
  vs `factoidal cottas-info` graph count.
- Hybrid escape coverage: pick a TriG with IRIs containing reserved
  characters (e.g., parens, spaces percent-encoded) and confirm round
  trip. The `tmp/ukparliament-hybrid` artifact suggests hand-tuned
  escaping logic; that should be lifted into the canonical pipeline
  with a regression test.
- Default-graph injection: `--default-graph-iri` does not exist on
  `materialize-nq-cottas-corpus`. Document the gap; suggest adding
  the flag or pointing users at a sed pre-step.

## Plan

Create one file at a time, then commit. Cap doc length around
180–250 lines each. Keep cross-refs to `docs/cottas-format-v1.md` and
`docs/cottas-import-howto.md` to avoid duplicating content.
