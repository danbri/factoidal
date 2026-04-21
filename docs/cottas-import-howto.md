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
- For large Turtle files, use a mature external RDF parser before the Factoidal
  query step. In the KGX trial, `pyoxigraph` parsed Turtle and DuckDB wrote the
  COTTAS/Parquet file. Those tools are importer/test-harness dependencies, not
  Factoidal query-runtime dependencies.

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

Use N-Quads or a direct Turtle-to-COTTAS importer for large data. Do not feed
large Turtle directly to Factoidal's Turtle parser for benchmarking. If source
data is Turtle, TriG, or RDF/XML, convert it first with a mature parser such as
`riot`, `rapper`, `rdflib`, or `pyoxigraph`.

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

### Parquet Encoding Caveat

Factoidal's current native COTTAS reader only handles `DELTA_LENGTH_BYTE_ARRAY`
string pages. DuckDB/pycottas will use dictionary pages for repeated columns on
normal RDF data, and those currently fail in Factoidal with errors such as:

```text
Failure("Missing Parquet value col=1 idx=0")
```

For scratch imports that must be readable by the current Factoidal binary, write
Parquet with:

```text
STRING_DICTIONARY_PAGE_SIZE_LIMIT 1
```

This keeps the string columns in `DELTA_LENGTH_BYTE_ARRAY`. Longer term,
Factoidal should support dictionary-encoded Parquet pages instead of requiring
this producer-side constraint.

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

`tests/local/cottas_corpus_regressions.sh` also passes in this checkout after
the ASK result output fix, with COTTAS query-time sanity checks forcing
`FACTOIDAL_COTTAS_BRIDGE` and `PYCOTTAS_PYTHON` to missing paths.

## Current Performance Caveat

The current COTTAS path is native but not yet fast. On the 5-row sample, local
timing was around 13 seconds for a `--data-cottas` named-graph query. On a
5-row KGX slice, local timing was about 17 seconds; 8 rows took about 39
seconds; 9 rows took about 47 seconds. This reflects the current direct-Parquet
probing and value reconstruction path, not Turtle parsing.

The next performance work is to make the COTTAS query path page-aware and
index-aware rather than reconstructing the artifact into an in-memory scan.
The current extracted OCaml runtime repeatedly probes
`DELTA_LENGTH_BYTE_ARRAY` values while loading the COTTAS cache, which is
structurally unsuitable for million-row artifacts.

## KGX Trial Results

Using `tmp/kgx_cottas_trial.py` as a scratch importer with `pyoxigraph` for
Turtle parsing and DuckDB for COTTAS/Parquet writing:

| Source | Turtle bytes | Triples | COTTAS bytes | Import time |
| --- | ---: | ---: | ---: | ---: |
| `therapeutic_use.ttl` | 5,388 | 92 | 2,011 | 0.038s |
| `chemical_compound.ttl` | 6,620 | 130 | 2,020 | 0.011s |
| `active_site.ttl` | 17,317 | 486 | 3,387 | 0.047s |
| `gene.ttl` | 17,363,312 | 888,949 | 632,446 | 7.018s |
| `Protein__protein1.ttl` | 34,468,325 | 1,043,923 | 1,203,782 | 5.124s |
| `Protein__protein3.ttl` | 50,417,919 | 1,512,879 | 2,904,617 | 24.328s |
| `taxon (timesout).ttl` | 140,525,751 | 4,121,433 | 5,025,564 | 20.807s |

DuckDB can count or preview the resulting COTTAS files in milliseconds:

```text
gene/data.cottas: 888,949 rows, count 0.009s, limit 0.011s
taxon-timesout/data.cottas: 4,121,433 rows, count 0.001s, limit 0.007s
```

So the external dataset-to-COTTAS indexing task is working for millions of
triples. The remaining blocker is efficient native querying from Factoidal over
those COTTAS artifacts.

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
