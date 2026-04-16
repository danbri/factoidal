# W3C SPARQL 1.1 Subquery Probe

Positive execution probe against the repo's bundled
`tests/w3c/sparql/sparql11/subquery` suite.

Script:

```bash
tools/w3c_sparql11_subquery_probe.sh
```

Current `.srx`-backed status:

- pass: `11`
- fail: `1`

Passing examples include:

- `sq01`
- `sq03`
- `sq04`
- `sq05`
- `sq06`
- `sq07`
- `sq08`
- `sq09`
- `sq10`
- `sq11`
- `sq13`

Current remaining miss:

- `sq02 - Subquery within graph pattern, graph variable is bound`

Interpretation:

- ordinary subquery execution is mostly working on the current engine
- the remaining miss is not random breakage; it is a scope/visibility issue
  involving a graph variable that is bound by `GRAPH ?g { ... }` and then
  referenced inside a nested subquery
- this looks like semantics work rather than a small parser bug

Out of scope for this probe:

- `sq12`
- `sq14`

Those have graph/Turtle expected outputs rather than `.srx` result sets, so
they need a different comparison harness.
