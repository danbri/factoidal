# Jena ARQ Graph Probe

Positive execution probe against Apache Jena ARQ's `DAWG-Final/graph` suite.

Script:

```bash
tools/jena_arq_graph_probe.sh
```

This probe loads:

- `qt:data` as the default graph
- each `qt:graphData` entry as an explicit named graph using a `file://...`
  IRI matching the test data file location

It currently compares result-row counts from the expected Turtle result-set
files, which is narrower than full result-set comparison but is good enough to
flush out dataset/default-graph and named-graph execution bugs quickly.

Current approved-suite status:

- pass: `11`
- fail: `0`

Important fixes behind this:

- separate loaded files now get distinct blank-node namespaces at the RDF
  dataset boundary, so independently parsed files no longer collide on raw
  labels like `_:x`
- withdrawn test `graph-10` is skipped, while approved replacement `graph-10b`
  is included

Interpretation:

- default graph vs named graph handling is now much closer to ordinary SPARQL
  expectations
- graph joins involving blank nodes across separately loaded files are no
  longer spuriously matching
