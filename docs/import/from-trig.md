# Importing TriG data into factoidal

[TriG](https://www.w3.org/TR/trig/) is the multi-graph form of Turtle.
A `.trig` file lets you mark up several **named graphs** in one file:

```trig
@prefix ex: <https://example.org/> .

ex:graph-a {
  ex:s1 ex:p ex:o1 .
  ex:s2 ex:p ex:o2 .
}

ex:graph-b {
  ex:s3 ex:p ex:o3 .
}

ex:s4 ex:p ex:o4 .   # default graph triple, outside any graph block
```

This guide turns a `.trig` file into a `.cottas` artifact and serves it
over SPARQL 1.1 Protocol.

## Prerequisites

- Python 3.10+ with `pycottas`, `pyoxigraph`, and `rdflib`. See
  [`README.md`](README.md#prerequisites-shared) for the venv recipe.
- The importer script
  [`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py).
- The factoidal binary at `bin/<platform>/factoidal` (already committed
  in this repo).
- A `.trig` file on disk. For testing, a tiny one is at
  [`tmp/test-small.trig`](../../tmp/test-small.trig).

## Quick path

Set up the env:

```bash
export PYCOTTAS_PY=tmp/pycottas-venv/bin/python
export PYCOTTAS_PYTHON="$PYCOTTAS_PY"   # consumed by the corpus_pipeline shell-out
```

Run the importer:

```bash
"$PYCOTTAS_PY" tools/corpus_pipeline.py materialize-nq-cottas-corpus \
  --input my-data.trig \
  --input-format trig \
  --corpus-root /path/to/output/CorpusCOTTAS \
  --dataset-name mycorpus \
  --chunk-name mycorpus
```

That produces:

```
/path/to/output/CorpusCOTTAS/
└── mycorpus/
    └── v1/
        ├── data.cottas        ← the artifact factoidal serves
        ├── data.nq            ← canonical N-Quads (intermediate)
        ├── data.factbin       ← internal term-id dictionary
        ├── source-info.ttl    ← provenance
        └── summary.json       ← quad/graph counts, verify result
```

`data.cottas` is the only file you need at query/serve time.

## Serving it

```bash
./bin/darwin-arm64/factoidal serve \
  --port 3032 \
  --data-cottas /path/to/output/CorpusCOTTAS/mycorpus/v1/data.cottas
```

That starts a SPARQL 1.1 Protocol endpoint at `http://127.0.0.1:3032/`.
Test with:

```bash
curl -G \
  --data-urlencode 'query=SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }' \
  http://127.0.0.1:3032/sparql
```

The named-graph structure from your `.trig` file is preserved: each
inner block becomes an addressable named graph and the loose triples
land in the default graph.

## What the importer does, step-by-step

1. **Detect format** by extension (`.trig` → format `trig`) or honour
   `--input-format trig` if you pass it.
2. **Stream-parse with pyoxigraph** (preferred) into strict N-Quads
   on disk at `<chunk>/v1/data.nq`. The importer re-emits each quad in
   N-Quads syntax, including the named-graph term as the 4th column.
   Default-graph triples land with no 4th column. See
   [`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py) lines
   141–188 (`convert_rdf_to_nquads_pyoxigraph`).
3. **Fall back to rdflib** if pyoxigraph is missing (lines 191–247).
   rdflib is **not streaming** — for files larger than a few hundred
   megabytes it will exhaust memory; install pyoxigraph instead.
4. **Re-parse the N-Quads** through a small in-process parser
   (`parse_nt_or_nq_line`) to populate the term/graph dictionaries
   for `data.factbin`.
5. **Call `pycottas.rdf2cottas(data_nq, data_cottas, index="spog")`**
   to write the binary COTTAS/Parquet artifact (line 1097).
6. **Verify** with `pycottas.verify(data_cottas)` and write
   `summary.json`.
7. **Update the corpus TOC** at `<corpus-root>/toc/data.nt` with one
   `fct:CorpusGraphChunk` entry pointing at the new artifact.

## Validation

Confirm the artifact looks right before deploying it:

```bash
./bin/darwin-arm64/factoidal cottas-info \
  /path/to/output/CorpusCOTTAS/mycorpus/v1/data.cottas
```

Output is `total_quads`, `subjects`, `predicates`, `objects`,
`named_graphs`. Compare:

- `total_quads` against `wc -l data.nq`.
- `named_graphs` against `grep -E '} *(\.|\\Z)' data.nq | sort -u | wc -l`
  or against the named-graph count produced by `riot --count`:

  ```bash
  riot --count my-data.trig
  ```

  riot reports total triples; for graph counts use:

  ```bash
  riot --output=NQUADS my-data.trig | awk '{print $NF}' | sort -u | wc -l
  ```

For a richer SPARQL-level check, run a count query against the served
endpoint and compare:

```bash
curl -G \
  --data-urlencode 'query=SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }' \
  http://127.0.0.1:3032/sparql
```

## Troubleshooting

### `ModuleNotFoundError: No module named 'pyoxigraph'`
Install pyoxigraph in the venv (`pip install pyoxigraph`). Without it
the importer falls back to rdflib, which loads the entire graph into
memory and will OOM on large parliaments-of-the-world files.

### `ModuleNotFoundError: No module named 'rdflib'`
The importer needs rdflib for the TOC writer. Install it in the same
venv. Note: `factoidal cottas-import` execs the system `python3` by
default; if your system Python lacks rdflib, run the venv's Python
directly as shown in the Quick path.

### IRI escaping issues
Factoidal's reader expects strict N-Quads escaping (only `\\`, `\"`,
`\n`, `\r`, `\t` and `\uXXXX`/`\UXXXXXXXX`). The pyoxigraph path emits
these correctly. The rdflib path uses
`tools/corpus_pipeline.py:_nt_escape_literal_lex` to coerce control
characters into `\uXXXX` before writing — if you see strict-mode
parser errors at query time, check `data.nq` for stray multiline
literals that snuck through a third-party converter.

### Bnode label collisions across files
Blank nodes are scoped to one document. If you concatenate multiple
TriG files before import, `_:b1` from file A and `_:b1` from file B
will collapse into one node. Either:

- Import each file as its own corpus chunk (run `materialize-nq-cottas-corpus`
  per file with distinct `--chunk-name`).
- Use `riot --formatted=TRIG --rename-bnodes` to give each input file
  unique blank-node labels first.

### Memory pressure on huge files
Use pyoxigraph (streaming). Confirm it's actually being used by
watching for `Pre-converting trig → N-Quads via parser pipeline` on
stderr. If you see the rdflib code path being taken, `pip install
pyoxigraph` and rerun.

### Parquet `Failure("Missing Parquet value col=1 idx=0")` at query time
Factoidal currently expects `DELTA_LENGTH_BYTE_ARRAY` string pages.
The default `pycottas.rdf2cottas` settings produce these; if you write
COTTAS files with a custom DuckDB pipeline, set
`STRING_DICTIONARY_PAGE_SIZE_LIMIT 1` to disable dictionary pages.
See [`docs/cottas-import-howto.md`](../cottas-import-howto.md#parquet-encoding-caveat).

### Slow query times after import
Import is fast, but query times on multi-million-row artifacts are not
yet optimised; see the perf notes in
[`docs/designissues/cottas-native-backend.md`](../designissues/cottas-native-backend.md).
This is a query-side issue, not an import issue.

## Known gaps

- The `materialize-nq-cottas-corpus` subcommand has no `--dry-run`.
  Run it on a small slice first if you want to validate the pipeline
  without writing a full COTTAS file.
- The subcommand has no `--default-graph-iri` flag (unlike its
  sibling `import-line-rdf`). For TriG this is fine — the file
  carries graph IRIs — but if your TriG has loose default-graph
  triples that you'd rather wrap in a named graph, edit the
  `.trig` file or the intermediate `.nq` first.

## See also

- [`docs/cottas-format-v1.md`](../cottas-format-v1.md) — what's actually
  inside `data.cottas`.
- [`docs/import/from-nquads.md`](from-nquads.md) — same pipeline,
  faster pre-step, when you've already canonicalised to N-Quads.
- [`docs/cottas-import-howto.md`](../cottas-import-howto.md) — older
  how-to with timing tables and Parquet caveats.
