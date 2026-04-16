# Jena ARQ Basic Probe

Positive execution probe against Apache Jena ARQ's `DAWG-Final/basic` suite.

Script:

```bash
tools/jena_arq_basic_probe.sh
```

This probe currently compares result-row counts using the suite manifest and
`.srx` expected results. It is deliberately narrower than full result-set
isomorphism, but it gives a fast signal about ordinary `SELECT` evaluation.

Current early slice (`LIMIT=20`) after the latest parser/base and
blank-node-query fixes:

- pass: `20`
- fail: `0`

Passing examples now include:

- `base-prefix-1`
- `base-prefix-2`
- `base-prefix-3`
- `base-prefix-4`
- `base-prefix-5`
- `bgp-no-match`
- `list-1` through `list-4`
- `prefix-name-1`
- `quotes-1` through `quotes-4`
- `spoo-1`
- `term-1` through `term-4`

Interpretation:

- the recent `BASE` / relative-IRI fixes improved ordinary positive query
  handling
- query-side blank nodes are now rewritten in F* as existential pattern
  variables during evaluation, which fixed the collection/list matching cases in
  this slice
- this probe is now good enough to extend beyond the initial `LIMIT=20` sample
