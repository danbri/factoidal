# Importing Turtle data into factoidal

[Turtle](https://www.w3.org/TR/turtle/) is the human-friendly
single-graph RDF format. It supports prefixes, nested predicate-object
lists, and abbreviated typed literals:

```turtle
@prefix ex:   <https://example.org/> .
@prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .

ex:alice
  a ex:Person ;
  ex:name "Alice" ;
  ex:age "30"^^xsd:integer ;
  ex:knows ex:bob .

ex:bob a ex:Person ; ex:name "Bob" .
```

Unlike TriG, a Turtle file describes **one graph**. By default the
importer treats that graph as the **default graph** in the resulting
COTTAS artifact. If you'd rather wrap the triples in a chosen named
graph, see "Wrapping into a named graph" below.

This guide also covers N-Triples (`.nt`), which is the line-oriented
single-graph cousin of Turtle.

## Prerequisites

- Python 3.10+ with `pycottas`, `pyoxigraph`, and `rdflib`. See
  [`README.md`](README.md#prerequisites-shared) for the venv recipe.
- The importer script
  [`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py).
- The factoidal binary at `bin/<platform>/factoidal`.
- A `.ttl` (or `.turtle` / `.nt`) file on disk.

## Quick path: Turtle → default graph

```bash
export PYCOTTAS_PY=tmp/pycottas-venv/bin/python
export PYCOTTAS_PYTHON="$PYCOTTAS_PY"

"$PYCOTTAS_PY" tools/corpus_pipeline.py materialize-nq-cottas-corpus \
  --input my-data.ttl \
  --input-format turtle \
  --corpus-root /path/to/output/CorpusCOTTAS \
  --dataset-name mycorpus \
  --chunk-name mycorpus
```

Output:

```
/path/to/output/CorpusCOTTAS/
└── mycorpus/
    └── v1/
        ├── data.cottas        ← the artifact factoidal serves
        ├── data.nq            ← canonical N-Quads (no 4th column)
        ├── data.factbin
        ├── source-info.ttl
        └── summary.json
```

Every triple lives in the default graph. Querying with a `GRAPH ?g`
block returns nothing; querying with `?s ?p ?o` (no graph) returns
everything.

## Quick path: N-Triples

```bash
"$PYCOTTAS_PY" tools/corpus_pipeline.py materialize-nq-cottas-corpus \
  --input my-data.nt \
  --input-format nt \
  --corpus-root /path/to/output/CorpusCOTTAS \
  --dataset-name mycorpus \
  --chunk-name mycorpus
```

For N-Triples the importer streams the file directly (no
pyoxigraph/rdflib involvement at parse time) — see
[`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py) line 1046.
The intermediate `data.nq` is a strict copy of the input; no graph
column is added.

## Wrapping into a named graph

The `materialize-nq-cottas-corpus` subcommand does **not** have a
`--default-graph-iri` flag (see "Known gaps" below). To put your
Turtle/N-Triples into a chosen named graph, pre-convert to TriG or
N-Quads first:

### Option A: convert via riot (Apache Jena)

```bash
riot --output=NQUADS \
     --syntax=TURTLE \
     --base=https://example.org/ \
     my-data.ttl |
  awk '{ sub(/\.$/, "<https://example.org/graph/mycorpus> ."); print }' \
  > my-data.nq
```

Then follow [`from-nquads.md`](from-nquads.md).

### Option B: convert via pyoxigraph (Python one-liner)

```bash
"$PYCOTTAS_PY" -c '
import sys
from pyoxigraph import parse, serialize, NamedNode
graph = NamedNode("https://example.org/graph/mycorpus")
quads = []
for triple in parse(open(sys.argv[1], "rb"), "text/turtle"):
    quads.append((triple.subject, triple.predicate, triple.object, graph))
with open(sys.argv[2], "wb") as out:
    for s, p, o, g in quads:
        out.write(serialize([(s,p,o,g)], None, "application/n-quads"))
' my-data.ttl my-data.nq
```

(Adjust to your pyoxigraph version's API as needed.)

### Option C: convert via rdflib

```python
from rdflib import ConjunctiveGraph, URIRef
ds = ConjunctiveGraph()
ds.parse("my-data.ttl", format="turtle", publicID="https://example.org/graph/mycorpus")
ds.serialize("my-data.nq", format="nquads")
```

In all three cases, follow up with [`from-nquads.md`](from-nquads.md)
to materialise the `.cottas`.

## Serving it

```bash
./bin/darwin-arm64/factoidal serve \
  --port 3032 \
  --data-cottas /path/to/output/CorpusCOTTAS/mycorpus/v1/data.cottas
```

A SPARQL 1.1 Protocol endpoint is at `http://127.0.0.1:3032/sparql`.

```bash
curl -G \
  --data-urlencode 'query=SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' \
  http://127.0.0.1:3032/sparql
```

## What the importer does, step-by-step

For `--input-format turtle`:

1. **Stream-parse with pyoxigraph** into strict N-Quads on disk
   ([`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py)
   line 160). Triples have no 4th term, so the resulting `.nq` lines
   are really N-Triples (factoidal accepts these as default-graph
   quads).
2. **Fall back to rdflib** if pyoxigraph is missing (line 225). Not
   streaming — beware of large files.
3. **Re-parse the N-Quads** through `parse_nt_or_nq_line` to fill
   `data.factbin`.
4. **Call `pycottas.rdf2cottas(data_nq, data_cottas, index="spog")`**
   to write the artifact.
5. **Verify and write `summary.json`**, update the corpus TOC.

For `--input-format nt`: skip step 1 — the file is `cp`'d into
`data.nq` directly (line 1051).

## Validation

```bash
./bin/darwin-arm64/factoidal cottas-info \
  /path/to/output/CorpusCOTTAS/mycorpus/v1/data.cottas
```

Compare:

- `total_quads` against `riot --count my-data.ttl`. They should match
  exactly (modulo blank-node label changes).
- `named_graphs` should be **0** for a Turtle/N-Triples import, **1**
  if you wrapped into a named graph using one of the options above.

A SPARQL-level check:

```bash
curl -G \
  --data-urlencode 'query=SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' \
  http://127.0.0.1:3032/sparql

curl -G \
  --data-urlencode 'query=SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }' \
  http://127.0.0.1:3032/sparql
```

The default-graph count should equal `riot --count`. The named-graph
count should be 0 (default-graph import) or equal `riot --count`
(named-graph wrap).

## Troubleshooting

### `pyoxigraph.ParseError: ...`
The Turtle parser pyoxigraph uses is strict (it implements W3C
Turtle 1.1). Common gotchas in non-spec-compliant files:

- Missing `@prefix` for a CURIE used in the body.
- Missing `@base` for a relative IRI: pass `--base` if the importer
  exposed one (it currently doesn't pass `--base` through to
  pyoxigraph; convert externally with `riot --base` first).
- Unicode escapes in IRIs that aren't valid: `\u` escapes only allow
  `[a-zA-Z0-9 _ - .]` after IRI-component normalisation.

### `ModuleNotFoundError: No module named 'pyoxigraph'` (or `rdflib`)
Install in the venv. Without pyoxigraph, the rdflib fallback loads
the entire graph in memory before writing the intermediate `.nq`,
which is OK for files under a few hundred MB and untenable above that.

### Blank nodes lose their identity
Blank-node labels in Turtle are scoped to the document. After import,
the label becomes a fresh internal identity in the COTTAS file. If
your application relies on a particular bnode label, mint a real IRI
upstream (the `URI` rdflib namespace functions can do this
deterministically) before import.

### Memory pressure on huge Turtle files
Use pyoxigraph (streaming) and watch for
`Pre-converting turtle → N-Quads via parser pipeline` on stderr.
For files > ~1 GB, prefer pre-converting with `riot --output=NQUADS`
and following [`from-nquads.md`](from-nquads.md) — that bypasses
all in-process Python parsing.

### Parquet `Failure("Missing Parquet value col=1 idx=0")` at query time
See the note in [`from-trig.md`](from-trig.md#parquet-failuremissing-parquet-value-col1-idx0-at-query-time)
— factoidal expects `DELTA_LENGTH_BYTE_ARRAY` string pages.

## Known gaps

- No `--default-graph-iri` flag on `materialize-nq-cottas-corpus`. The
  sibling subcommand `import-line-rdf` has one for N-Triples imports
  but doesn't write COTTAS. Workaround: pre-convert as in "Wrapping
  into a named graph" above.
- No `--base` flag plumbed to the pyoxigraph parser. Files using
  relative IRIs without an `@base` declaration must be repaired or
  pre-converted.
- No `--dry-run`. Use `head -n 100 my-data.ttl > sample.ttl` to
  preview.

## See also

- [`docs/cottas-format-v1.md`](../cottas-format-v1.md) — wire format.
- [`docs/import/from-trig.md`](from-trig.md) — multi-graph Turtle.
- [`docs/import/from-nquads.md`](from-nquads.md) — when you've already
  canonicalised to N-Quads (recommended for large files).
- [`docs/cottas-import-howto.md`](../cottas-import-howto.md) — older
  how-to with KGX timing tables (the KGX corpus is Turtle).
