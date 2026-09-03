# Persisted-path W3C executability census (2026-09-01, extended 2026-09-03)

What fraction of the official W3C SPARQL evaluation tests can the
Shardborough disk path currently ATTEMPT end to end, and does it
answer what the in-memory engine answers? This census answers both
with measured numbers. It is still **not** a conformance result:
answers are compared with the REFERENCE Lean engine over the same
input file, not with the suite's expected `.srx`/`.csv`, so it must
never be quoted as a "W3C suite result" (terminology per
[the Tuesday OKRs](20260901-blockengine-tuesday-okrs.md)). The
conformance number is `lake exe l4w3c`.

## Tool

`tools/w3c-persisted-census.sh [SUITE_DIR ...]` — defaults to the
vendored sparql10 + sparql11 trees. It runs two eligibility passes,
and every step is capped at 60 s.

**Pass 1, default graph.** For every `manifest.ttl` it uses the Lean
engine itself (`l4factoidal query` with the manifest's base) to
extract `mf:QueryEvaluationTest` entries whose action is a single
default-graph `qt:data` (no `qt:graphData`), packs each distinct data
file once (`l4block-shard-pack`, ibk3), activates the generation, and
runs the original query text through `l4block-id-v3-query` via
`CURRENT`. RDF/XML data files are converted to N-Triples by the Lean
parser (`--format rdfxml --base file://…`), never by shell text
processing.

**Pass 2, named graphs (added 2026-09-03).** Entries whose action has
`qt:graphData`. The `qt:data` file, if any, and every `qt:graphData`
file are converted to N-Quads by the Lean engine and concatenated into
ONE input, with the `qt:graphData` file's own IRI as the graph name —
the rule `Harness/Manifest.lean` (`dataAndGraphData`) uses. The input
is packed as `ibk4`, activated, and queried through
`l4block-quad-query`.

**Row agreement (added 2026-09-03).** For every executed test the
persisted answer (`rows=N`, `boolean=X` or `triples=N`) is compared
with the reference in-memory engine's answer for the SAME query over
the SAME file. A SELECT is counted from the SPARQL Results JSON the
engine prints, never from its `--table` rendering: see the two
counting traps below.

Outcomes land in `tmp/w3c-persisted-census-latest.tsv`, differences
in `tmp/w3c-persisted-census-mismatches.txt`.

## Measured result (2026-09-03, this machine, tip `ce23d1936`)

📊 **Default graph (IBK3, `l4block-id-v3-query`): 535 executed, 0
refused at pack/activate, 0 refused at query (out of 535 eligible
single-default-graph QueryEvaluationTest entries). Of the 535
executed, 535 matched the reference engine, 0 differed.**

📊 **Named graphs (IBK4, `l4block-quad-query`): 29 executed, 0 refused
at convert/pack/activate, 6 refused at query (out of 35 eligible
`qt:graphData` QueryEvaluationTest entries). Of the 29 executed, 29
matched the reference engine, 0 differed.**

The two suites contain 592 QueryEvaluationTests: 535 with `qt:data`
and no `qt:graphData`, 35 with `qt:graphData`, and 22 whose action
carries neither (measured 2026-09-03). The 2026-09-01 text of this
document said "the 57 excluded entries use `qt:graphData`"; that was
`592 - 535` assumed to be one category, and it was wrong by 22.

The 6 named-graph refusals all have ONE cause, and it is not the quad
layout: the query text carries a RELATIVE IRI naming its own fixture
(`GRAPH <ng-01.ttl>`, `FROM <data.ttl>`, `VALUES ... <empty.ttl>`), and
none of `l4block-quad-query`, `l4block-id-v3-query` or `l4factoidal
query` accepts a query BASE IRI, so `parseSparql` refuses with
"invalid IRI". The reference engine refuses the same six identically,
so this caps eligibility rather than creating a false difference. The
`l4w3c` runner does not have this gap: it parses each query with its
own `file:` IRI as BASE. Giving the query CLIs a `--query-base` means
threading a base through the `query` dispatch op, which changes the
WASM ABI, so it is not done here.

The 535 include all 70 entailment-regime QueryEvaluationTests. They
execute and agree with the reference engine, but BOTH evaluate under
simple entailment only — neither applies the requested regime, so most
of those 70 would not match their expected results. Agreement here
means the disk path answers what the in-memory path answers, nothing
stronger.

## Two row-counting traps this census paid for

Both made the shell report differences the engines did not have.

1. **A zero-variable projection.** `SELECT * WHERE { :a0 (:p)* :a1 }`
   (sparql10 `pp36`) has one solution that binds nothing. The table
   renderer prints an empty header line and one empty row line, and
   `$(...)` strips both, so the count came out 0 against a correct 1.
   The reference output now goes to a FILE, never a command
   substitution.
2. **A literal containing a newline.** The sparql10 `regex-*` fixtures
   bind values such as `"a\nc"`, which the table renderer prints across
   two lines. Counting table lines made 5 of 535 tests differ for no
   engine reason. SELECT rows are now counted from the result JSON's
   `results.bindings` array.

Neither was a divergence between the disk path and the engine. A row
count taken from a human-readable rendering is a count of that
rendering.

## What this does and does not establish

- Established: every eligible official evaluation query — including
  aggregates, subqueries, property paths, negation, functions, and now
  `GRAPH <iri>`, `GRAPH ?g`, `FROM` and `FROM NAMED` over named-graph
  fixtures — gets through parse, physical planning (or its complete
  fallback), verified reads and result formation against a packed,
  activated, Merkle-committed store, and returns the SAME answer shape
  and cardinality as the in-memory engine.
- Not established: answer correctness against the suite's expected
  results, and per-row value equality. The comparison is on answer
  KIND and CARDINALITY (`rows=N`, `boolean=X`, `triples=N`), not on the
  bindings themselves. The conformance census with `.srx`/`.csv`
  comparison, blank-node isomorphism and query base-IRI resolution
  remains the next increment, in `l4w3c` as a backend mode.
- Known limitation of pass 2: the per-file N-Quads are concatenated
  without relabelling blank nodes, so two `qt:graphData` files that use
  the same blank node label are conflated. Both sides of the comparison
  read the same concatenated file, so the agreement number is exact;
  the dataset can differ from the one `l4w3c` builds, which parses each
  file into its own graph.

## Reproduce

```sh
tools/w3c-persisted-census.sh
```

Prints both census lines, the first five differences, and per-test
outcomes in `tmp/w3c-persisted-census-latest.tsv`. Requires the Lean
CLIs (`lake build l4block-shard-pack l4block-shard-activate
l4block-id-v3-query l4block-quad-query l4factoidal` from
`formal/lean4/`) and `python3` for reading the result JSON.
