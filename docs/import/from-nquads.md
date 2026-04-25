# Importing N-Quads data into factoidal

[N-Quads](https://www.w3.org/TR/n-quads/) is a line-oriented multi-graph
RDF format: one quad per line, terminated by ` .`, with an optional
fourth term naming the graph:

```
<https://example.org/s1> <https://example.org/p> <https://example.org/o1> <https://example.org/graph-a> .
<https://example.org/s2> <https://example.org/p> <https://example.org/o2> <https://example.org/graph-a> .
<https://example.org/s4> <https://example.org/p> <https://example.org/o4> .
```

This is the **fastest path into factoidal**: the importer doesn't need
to parse Turtle nesting, prefix declarations, or escapes — it walks
each line directly. If your data is in TriG, Turtle, or RDF/XML,
converting to N-Quads first with a streaming tool (`riot`, `pyoxigraph`)
and then following this guide is often faster than letting the importer
do the conversion.

## Prerequisites

- Python 3.10+ with `pycottas` and `rdflib`. `pyoxigraph` is *optional*
  for N-Quads input (the importer's line parser handles `.nq` natively),
  but installing it doesn't hurt. See
  [`README.md`](README.md#prerequisites-shared) for the venv recipe.
- The importer script
  [`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py).
- The factoidal binary at `bin/<platform>/factoidal`.
- A `.nq` (or `.nquads`) file on disk, UTF-8, one quad per line.

## Quick path

```bash
export PYCOTTAS_PY=tmp/pycottas-venv/bin/python
export PYCOTTAS_PYTHON="$PYCOTTAS_PY"

"$PYCOTTAS_PY" tools/corpus_pipeline.py materialize-nq-cottas-corpus \
  --input my-data.nq \
  --input-format nq \
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
        ├── data.nq            ← canonical copy of the input
        ├── data.factbin       ← internal term-id dictionary
        ├── source-info.ttl    ← provenance
        └── summary.json       ← quad/graph counts, verify result
```

## Serving it

```bash
./bin/darwin-arm64/factoidal serve \
  --port 3032 \
  --data-cottas /path/to/output/CorpusCOTTAS/mycorpus/v1/data.cottas
```

A SPARQL 1.1 Protocol endpoint listens at `http://127.0.0.1:3032/sparql`.
A quick smoke test:

```bash
curl -G \
  --data-urlencode 'query=SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' \
  http://127.0.0.1:3032/sparql
```

(`?s ?p ?o` without a `GRAPH` block queries the **default graph only**.
For a count of every quad including named graphs, wrap in
`{ { ?s ?p ?o } UNION { GRAPH ?g { ?s ?p ?o } } }` or use
`SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }` for the
named-graph total.)

## What the importer does, step-by-step

For `--input-format nq` the path is short:

1. **Open the input file as a stream**, line by line.
2. **Parse each line** with `parse_nt_or_nq_line` (in
   [`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py),
   line 342). Comments and blank lines are skipped. Malformed lines
   raise immediately with a `<file>:<lineno>` error.
3. **Copy the cleaned quads** to `<chunk>/v1/data.nq`. Comments and
   blank lines are stripped; literal lexical content is preserved
   verbatim, so escaped Unicode (`\uXXXX`) stays as written.
4. **Build the term-id dictionary** in `data.factbin` (binary, used
   by some internal tools — safe to ignore).
5. **Call `pycottas.rdf2cottas(data_nq, data_cottas, index="spog")`**
   to write the binary COTTAS/Parquet artifact (line 1097).
6. **Verify** with `pycottas.verify(data_cottas)` and write
   `summary.json`.
7. **Update the corpus TOC** at `<corpus-root>/toc/data.nt`.

The N-Quads path **does not invoke pyoxigraph or rdflib** for parsing.
That keeps memory flat regardless of input size.

## Validation

```bash
./bin/darwin-arm64/factoidal cottas-info \
  /path/to/output/CorpusCOTTAS/mycorpus/v1/data.cottas
```

Compare:

- `total_quads` against `wc -l < my-data.nq`. (Subtract any blank/
  comment lines: `grep -cv '^[[:space:]]*\(#\|$\)' my-data.nq`.)
- `named_graphs` against:

  ```bash
  awk '
    # crude 4th-term IRI extractor; handles the common case of
    # quads ending "<graph> ."
    {
      n = split($0, a, " ")
      if (n >= 5 && substr(a[n-1], 1, 1) == "<") print a[n-1]
    }
  ' my-data.nq | sort -u | wc -l
  ```

  For exact accounting use a SPARQL query against the served endpoint:

  ```bash
  curl -G \
    --data-urlencode 'query=SELECT (COUNT(DISTINCT ?g) AS ?graphs) WHERE { GRAPH ?g { ?s ?p ?o } }' \
    http://127.0.0.1:3032/sparql
  ```

## Troubleshooting

### `RuntimeError: <file>:<lineno>: expected terminating dot`
The importer's line parser is strict. Each line must end in ` .`
followed by a newline. Common causes:

- A literal containing an unescaped newline. Use the strict N-Quads
  escapes (`\n`, `\r`); triple-quoted Turtle-style literals are not
  valid N-Quads.
- A bnode graph term with whitespace in the label. Bnode labels in
  N-Quads run from `_:` until the next whitespace.

If the source data came from rdflib, re-serialise it with `riot
--formatted=NQUADS` or run it through pyoxigraph; both produce strict
N-Quads.

### `ModuleNotFoundError: No module named 'pycottas'`
Install in the venv:

```bash
tmp/pycottas-venv/bin/pip install pycottas
```

Then rerun the importer **with the venv's Python**, not the system
`python3`. The shim form `factoidal cottas-import` execs `python3`
which may not be the venv.

### Bnode graph terms (`_:b ` as the 4th column)
The importer rewrites these to `urn:factoidal:bnode-graph:<label>`
(see line 372). If your downstream tooling expects the original bnode
identity, normalise upstream — for example with `rdf-canon` or by
substituting deterministic IRIs of your own choosing before import.

### Bnode label collisions across files
If you `cat a.nq b.nq > combined.nq`, blank nodes labelled `_:b1` in
both files will alias. Re-label first:

```bash
awk -F' ' 'BEGIN{OFS=" "} { gsub(/_:/, "_:fileA-") } 1' a.nq > a.relabel.nq
awk -F' ' 'BEGIN{OFS=" "} { gsub(/_:/, "_:fileB-") } 1' b.nq > b.relabel.nq
cat a.relabel.nq b.relabel.nq > combined.nq
```

(That's a sledgehammer — it relabels every `_:` even inside literals.
For literals containing `_:` use `riot --formatted=NQUADS
--rename-bnodes` instead.)

### Memory pressure on huge files
The N-Quads importer streams to disk (`data.nq`) but keeps the
`parsed_rows` list in memory to build `data.factbin` (see
[`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py) line
1061). For files exceeding several hundred million quads on a small
machine, this can run out of RAM. Workarounds:

- Skip `data.factbin`: not currently a CLI flag — the file is always
  written. Track issue if you need it.
- Run the importer on a host with more RAM; `data.factbin` is roughly
  `(distinct_terms * avg_term_bytes) + (quads * 16 bytes)`.
- Pass `--disk` to use a disk-backed DuckDB during the pycottas
  conversion phase (does not eliminate the in-memory term dictionary
  but reduces peak DuckDB memory).

### Parquet `Failure("Missing Parquet value col=1 idx=0")` at query time
See the same note in [`from-trig.md`](from-trig.md#parquet-failuremissing-parquet-value-col1-idx0-at-query-time)
— factoidal's reader requires `DELTA_LENGTH_BYTE_ARRAY` string pages,
which the default `pycottas.rdf2cottas` settings produce.

## Known gaps

- No `--dry-run` flag. To preview, slice the input first:
  `head -n 1000 my-data.nq > sample.nq` and import that.
- No `--input-graph-iri` flag to force a single graph (or to override
  per-line graphs). If you need to coerce a multi-graph file into one
  graph, sed the 4th column first.
- The importer never deletes intermediate `data.nq`. For datasets
  larger than a few GB you may want to remove it after `data.cottas`
  is verified.

## See also

- [`docs/cottas-format-v1.md`](../cottas-format-v1.md) — wire format.
- [`docs/import/from-trig.md`](from-trig.md) — when source is `.trig`
  and conversion happens inside the importer.
- [`docs/import/from-turtle.md`](from-turtle.md) — when source is a
  single-graph Turtle file.
- [`docs/cottas-import-howto.md`](../cottas-import-howto.md) — older
  how-to with KGX timing tables.
