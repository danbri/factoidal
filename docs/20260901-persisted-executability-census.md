# Persisted-path W3C executability census (2026-09-01)

What fraction of the official W3C SPARQL evaluation tests can the
Shardborough disk path currently ATTEMPT end to end? This census
answers that with a measured number. It is an **executability**
census, not a conformance result: answers are not compared to the
expected result files, so it must never be quoted as a "W3C suite
result" (terminology per
[the Tuesday OKRs](20260901-blockengine-tuesday-okrs.md)).

## Tool

`tools/w3c-persisted-census.sh [SUITE_DIR ...]` — defaults to the
vendored sparql10 + sparql11 trees. For every `manifest.ttl` it uses
the Lean engine itself (`l4factoidal query` with the manifest's base)
to extract `mf:QueryEvaluationTest` entries whose action is a single
default-graph `qt:data` (no `qt:graphData`), packs each distinct data
file once (`l4block-shard-pack`, ibk3), activates the generation, and
runs the original query text through `l4block-id-v3-query` via
`CURRENT`. RDF/XML data files are converted to N-Triples by the Lean
parser (`--format rdfxml --base file://…`), never by shell text
processing. Every step is capped at 60 s. Outcomes land in
`tmp/w3c-persisted-census-latest.tsv`.

## Measured result (2026-09-01, this machine, tip `b1cd0ecf1`)

📊 **535 executed, 0 refused at pack/activate, 0 refused at query
(out of 535 eligible single-default-graph QueryEvaluationTest
entries)**. The two suites contain 592 QueryEvaluationTests in total;
the 57 excluded entries use `qt:graphData` (named-graph datasets),
which the current default-graph-oriented SBM6 layout does not
represent — an explicit alpha limit, not a silent skip. Named graphs
remain core to the project vision (owner, 2026-09-01, verbatim:
"named graphs remain at the heart of our vision! Even if not in the
MVP"); the quad-aware layout is a stated beta gate, and this
exclusion is sequencing, not scope.

The 535 include all 70 entailment-regime QueryEvaluationTests. They
execute cleanly, but the persisted route evaluates under simple
entailment only — it does not yet apply the requested regime, so
most of those 70 would not match their expected results. Executed
here means the plumbing ran end to end, nothing stronger.

During development the census exposed one real seam: the pack CLI
reads Turtle only, so the four RDF/XML data files in
`sparql11/subquery/` initially refused at pack; they convert cleanly
through the Lean RDF/XML parser once a `file://` base is supplied for
their relative `rdf:resource` attributes. The census now does that
conversion; a future packer could accept `--format` directly.

## What this does and does not establish

- Established: every eligible official evaluation query — including
  aggregates, subqueries, property paths, negation, functions — gets
  through parse, physical planning (or its complete fallback),
  verified reads, and result formation against a packed, activated,
  Merkle-committed store without an error or a refusal.
- Not established: answer correctness against the suite's expected
  results. That requires the Lean-side comparator census (expected
  `.srx`/`.csv` comparison with the suite's rules, plus base-IRI
  resolution for queries with relative IRIs) — the natural next
  increment, in `l4w3c` as a backend mode.

## Reproduce

```sh
tools/w3c-persisted-census.sh
```

Prints the census line and keeps per-test outcomes in
`tmp/w3c-persisted-census-latest.tsv`. Requires the Lean CLIs
(`lake build l4block-shard-pack l4block-shard-activate
l4block-id-v3-query l4factoidal` from `formal/lean4/`).
