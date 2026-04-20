# COTTAS Import And Query How-To

Date: 2026-04-20

This page documents the current practical workflow for making a COTTAS/Parquet
artifact and querying it with Factoidal.

Important distinction:

- `pycottas` is currently used to produce COTTAS/Parquet artifacts from
  N-Quads.
- `factoidal --data-cottas` queries those artifacts natively through the
  extracted Factoidal runtime. It does not need `pycottas` or
  `tools/cottas_bridge.py` at query time.

## Install The Producer Toolkit

Create a repo-local venv:

```bash
python3 -m venv tmp/pycottas-venv
tmp/pycottas-venv/bin/pip install --upgrade pip setuptools wheel pycottas rdflib duckdb
```

Verify imports:

```bash
tmp/pycottas-venv/bin/python -c 'import pycottas, rdflib, duckdb; print(pycottas.__file__); print(rdflib.__version__); print(duckdb.__version__)'
```

## Preferred Input

Use N-Quads for large data. Do not feed large Turtle directly to Factoidal's
Turtle parser for benchmarking. If source data is Turtle, TriG, or RDF/XML,
convert it first with a mature parser such as `riot`, `rapper`, or `rdflib`.

The KGX local corpus is currently in:

```bash
tmp/wikidata-lifesci-kgx/
```

It is about 243 MB of Turtle. Convert those files to line-oriented RDF before
trying COTTAS materialization.

## Make A COTTAS Artifact

For a N-Quads file:

```bash
PYCOTTAS_PYTHON=tmp/pycottas-venv/bin/python \
tmp/pycottas-venv/bin/python tools/corpus_pipeline.py materialize-nq-cottas-corpus \
  --input docs/fstar-extracted/cottas-examples/sample.nq \
  --corpus-root tmp/cottas-demo/CorpusCOTTAS \
  --dataset-name sample \
  --chunk-name sample
```

Expected output includes:

```text
artifact=tmp/cottas-demo/CorpusCOTTAS/sample/v1/data.cottas
verified=True
```

The artifact is a Parquet file with four string columns: subject, predicate,
object, graph.

## Query Natively With Factoidal

After materialization, query the artifact:

```bash
FACTOIDAL_COTTAS_BRIDGE=/definitely/missing \
PYCOTTAS_PYTHON=/definitely/missing \
./bin/darwin-arm64/factoidal \
  --data-cottas tmp/cottas-demo/CorpusCOTTAS/sample/v1/data.cottas \
  --query tmp/cottas-sample-query.rq
```

Setting `FACTOIDAL_COTTAS_BRIDGE` and `PYCOTTAS_PYTHON` to missing paths is a
useful sanity check: if the query still works, the query path is native
Factoidal over the COTTAS/Parquet artifact.

Example query:

```sparql
SELECT ?s ?p ?o ?g WHERE {
  GRAPH ?g { ?s ?p ?o }
}
ORDER BY ?g ?s ?p ?o
```

## Minimal End-To-End Check

Create a query file:

```bash
cat > tmp/cottas-sample-query.rq <<'EOF'
SELECT ?s ?p ?o ?g WHERE {
  GRAPH ?g { ?s ?p ?o }
}
ORDER BY ?g ?s ?p ?o
EOF
```

Materialize a sample artifact:

```bash
PYCOTTAS_PYTHON=tmp/pycottas-venv/bin/python \
tmp/pycottas-venv/bin/python tools/corpus_pipeline.py materialize-nq-cottas-corpus \
  --input docs/fstar-extracted/cottas-examples/sample.nq \
  --corpus-root tmp/cottas-demo/CorpusCOTTAS \
  --dataset-name sample \
  --chunk-name sample
```

Run the native query:

```bash
FACTOIDAL_COTTAS_BRIDGE=/definitely/missing \
PYCOTTAS_PYTHON=/definitely/missing \
./bin/darwin-arm64/factoidal \
  --data-cottas tmp/cottas-demo/CorpusCOTTAS/sample/v1/data.cottas \
  --query tmp/cottas-sample-query.rq
```

## Regression Checks

Backend parity currently passes with the installed producer toolkit:

```bash
PYCOTTAS_PYTHON=tmp/pycottas-venv/bin/python \
bash tests/local/backend_parity_regressions.sh
```

This compares plain N-Quads and COTTAS outputs for the same queries.

The older `tests/local/cottas_corpus_regressions.sh` currently has a brittle
ASK-output expectation in this checkout: the binary prints `Yes` where the test
expects bare `true`. Treat backend parity as the stronger signal until that
test expectation is updated.

## Current Performance Caveat

The current COTTAS path is native but not yet fast. On the 5-row sample, local
timing was around nine seconds for a `--data-cottas` query. This reflects the
current direct-Parquet probing and value reconstruction path.

The next performance work is to make the COTTAS query path page-aware and
index-aware rather than reconstructing the artifact into an in-memory scan.

## KGX Workflow Sketch

For `tmp/wikidata-lifesci-kgx`, use this staged workflow:

1. Convert source Turtle files to N-Quads with named graphs, one graph per
   source file.
2. Materialize the N-Quads into COTTAS/Parquet with
   `materialize-nq-cottas-corpus`.
3. Run result-parity queries against both plain N-Quads and `--data-cottas`.
4. Only then collect timings.

Avoid using the 134 MB `taxon (timesout).ttl` file as the first import test.
Start with small files such as `therapeutic_use.ttl`, `chemical_compound.ttl`,
or `active_site.ttl`.
