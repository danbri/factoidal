# HDT-Backed SPARQL Subset

Experimental `--data-hdt` / `--named-hdt` support currently covers a useful but
partial subset of SPARQL.

Implemented on the HDT-backed path:

- `SELECT`
- `ASK`
- basic BGPs
- `JOIN`
- `UNION`
- `FILTER`
- `MINUS`
- `LEFT JOIN` / `OPTIONAL`
- `BIND`
- `VALUES`
- `GRAPH <iri> { ... }`
- `GRAPH ?g { ... }`
- grouping / aggregates for `SELECT`
- subselects returning `SELECT` solution sequences

Still not implemented on the HDT-backed path:

- property paths
- `SERVICE`
- `CONSTRUCT`
- `DESCRIBE`

Repo-local checks:

```bash
tests/local/sparql_parser_regressions.sh
```

Current local HDT-backed checks cover:

- shorthand query with prefixed names, `a`, and `;`
- named graph query
- `BIND` + `VALUES`
- named-graph `ASK`
- named-graph `GROUP BY` / aggregate
- named-graph subselect
