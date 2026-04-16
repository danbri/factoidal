# RDF Format Conversion

Use this when a parser benchmark or compliance task needs the same RDF content
in a different serialization, especially when converting Turtle/TriG into
line-oriented formats such as N-Triples or N-Quads for ingestion tests.

## Tool

Use:

```bash
python3 tools/rdf_convert.py INPUT OUTPUT
```

The script uses `rdflib`, which is available in this environment, and infers
formats from file extensions:

- `.ttl` -> Turtle
- `.trig` -> TriG
- `.nt` -> N-Triples
- `.nq` -> N-Quads
- `.rdf` / `.xml` -> RDF/XML

You can also force formats explicitly:

```bash
python3 tools/rdf_convert.py --input-format turtle --output-format nt in.ttl out.nt
```

## Recommended uses

- Convert Turtle fixtures to N-Triples for line-oriented parser experiments.
- Convert TriG to N-Quads for dataset-ingestion tests.
- Normalize external RDF/XML or Turtle examples into `.nt` / `.nq` for faster iteration.

## Notes

- This is a utility for testing and benchmarking, not the project's source of truth.
- Parser logic still belongs in F*.
- Prefer writing converted artifacts into `/tmp` unless they are intended to be committed.

## Example

```bash
python3 tools/rdf_convert.py \
  examples/data/third_party/Berlin.ttl \
  /tmp/Berlin.nt
```
