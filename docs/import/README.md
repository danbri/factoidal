# Importing RDF data into factoidal

Factoidal queries large RDF datasets through a binary container called
**COTTAS** (a small Parquet schema; see
[`docs/cottas-format-v1.md`](../cottas-format-v1.md) for the wire spec).
Importing means: take your source RDF on disk, convert it to a `.cottas`
file, then point `factoidal serve` (or `factoidal query`) at that file.

This directory is the user-facing import guide. Pick the page that
matches the format your source data is in.

## Pick your input format

| Source format | Guide |
| --- | --- |
| TriG (`.trig`, multi-graph Turtle) | [`from-trig.md`](from-trig.md) |
| N-Quads (`.nq`, `.nquads`, line-oriented multi-graph) | [`from-nquads.md`](from-nquads.md) |
| Turtle (`.ttl`, single graph) or N-Triples (`.nt`) | [`from-turtle.md`](from-turtle.md) |

If your data is in another format (RDF/XML, JSON-LD, OWL/XML), the
quickest path is to convert it to N-Quads first with
[Apache Jena `riot`](https://jena.apache.org/documentation/io/) or
[`pyoxigraph`](https://pyoxigraph.readthedocs.io/), then follow
[`from-nquads.md`](from-nquads.md).

## What you get out

Every guide ends with a `data.cottas` file under
`<corpus-root>/<dataset-name>/v1/data.cottas`, plus three sidecars:

- `data.nq` — the canonical N-Quads the cottas was built from.
- `data.factbin` — a small binary term-id dictionary used by some
  internal tools. Safe to ignore for normal serving.
- `source-info.ttl` — provenance for the corpus TOC.
- `summary.json` — quad/graph counts and `pycottas` `verify()` result.

## Prerequisites (shared)

All three guides assume:

1. A **factoidal binary** under `bin/<platform>/factoidal` — already
   committed in this repo for `darwin-arm64` and `linux-x86_64`.
2. **Python 3.10+** with `pycottas`, `pyoxigraph`, and `rdflib`.
   The how-to in [`docs/cottas-import-howto.md`](../cottas-import-howto.md)
   recommends a repo-local venv:

   ```bash
   python3 -m venv tmp/pycottas-venv
   tmp/pycottas-venv/bin/pip install --upgrade pip setuptools wheel
   tmp/pycottas-venv/bin/pip install pycottas pyoxigraph rdflib duckdb
   ```

3. The importer script
   [`tools/corpus_pipeline.py`](../../tools/corpus_pipeline.py)
   (in the repo). All three guides invoke its
   `materialize-nq-cottas-corpus` subcommand.

## How factoidal natively reads these formats

Factoidal also has F\*-extracted parsers for Turtle, N-Triples,
N-Quads, TriG, and RDF/XML and can serve them directly without an
import step:

```bash
./bin/darwin-arm64/factoidal serve --port 3030 --dataset my-data.trig
```

That re-parses the file on every restart. For files larger than a few
megabytes, prefer the COTTAS path: parse once with the importer, then
restart instantly via `--data-cottas`.

The relevant F\* parsers are:

- [`formal/fstar/Parser.NQuads.fst`](../../formal/fstar/Parser.NQuads.fst)
- [`formal/fstar/Parser.TriG.fst`](../../formal/fstar/Parser.TriG.fst)
- [`formal/fstar/Parser.Turtle.fst`](../../formal/fstar/Parser.Turtle.fst)

These are what factoidal uses at *query* time on `--dataset`. The
*import* path uses pyoxigraph (Python) for speed; an F\*-native cottas
writer is future work.

## Honesty notes

- **Today the import path is Python.** `pycottas` is the writer;
  factoidal does not yet have an F\*-extracted COTTAS writer. See
  [`docs/cottas-format-v1.md`](../cottas-format-v1.md) §1 for the
  contract a future writer will satisfy.
- **The `factoidal cottas-import` subcommand is a shim.** It exec()s
  `python3 tools/corpus_pipeline.py materialize-nq-cottas-corpus
  ...`. Calling it from a Python that lacks `rdflib`/`pycottas` will
  surface a Python `ModuleNotFoundError`; run the venv's Python
  directly and pass `PYCOTTAS_PYTHON` if your shim's `python3` is
  not the venv one (see each guide).
- **Querying speed.** As of 2026-04-25, COTTAS query times are
  not yet fast on multi-million-row artifacts; see the caveats in
  [`docs/cottas-import-howto.md`](../cottas-import-howto.md) and
  [`docs/designissues/cottas-native-backend.md`](../designissues/cottas-native-backend.md).
  Import times are healthy (millions of quads per minute through
  pyoxigraph + DuckDB).

## See also

- [`docs/cottas-format-v1.md`](../cottas-format-v1.md) — wire format
  spec for the `.cottas` file.
- [`docs/cottas-import-howto.md`](../cottas-import-howto.md) — older,
  technical how-to with timings and Parquet-encoding caveats.
- [`docs/designissues/cottas-native-backend.md`](../designissues/cottas-native-backend.md)
  — design context for the read path.
