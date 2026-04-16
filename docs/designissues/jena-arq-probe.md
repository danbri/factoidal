# Jena ARQ Probe

Local probe against Apache Jena ARQ tests checked out under `/tmp/jena`.

Current script:

```bash
tools/jena_arq_syntax_probe.sh
```

Current syntax results from `jena-arq/testing/DAWG-Final` after the latest
parser tightening:

- `syntax-sparql3`: positive `9/9`, negative `42/42`
- `syntax-sparql4`: positive `4/4`, negative `8/8`
- `syntax-sparql5`: positive `2/2`

Interpretation:

- current parser accepts the sampled positive legal syntax in these suites
- current parser rejects the sampled negative syntax in these suites
- this is a parser/frontend issue, separate from HDT-backed evaluation

Recent local wins from this pass:

- missing-dot and extra-dot triple separator cases are now rejected
- the `syn-bad-26.rq` longest-token case is now rejected
- `syn-bad-filter-missing-parens.rq` is now rejected
- `syn-bad-lone-list.rq` is now rejected
- `syn-bad-bnode-dot.rq` is now rejected
- all sampled `syntax-sparql4` negatives in the probe are now rejected

Next steps:

- add a second probe for positive evaluation suites, not just syntax
- keep selected Jena negatives in repo-local parser regressions
- expand beyond syntax into broader ARQ/Jena execution coverage
