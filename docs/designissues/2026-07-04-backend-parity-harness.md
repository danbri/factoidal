# Corpus-driven cross-backend SPARQL parity harness

Date: 2026-07-04.
Owner directive: "a fully compliant memory impl doesn't mean the disk
variant is" — semantic compliance is claimed PER BACKEND, and every
semantic regression test runs on all backends. The W3C suites exercise
the in-memory path only; #261 and #267 both lived in exactly that gap.
This harness generalises the pattern of
[`tests/local/graph_default_semantics_regressions.sh`](../../tests/local/graph_default_semantics_regressions.sh)
(same fixtures, same queries, every backend, results diffed) from 7
hand-rolled checks to a manifest-driven corpus.

## Files

- [`tests/parity/run_backend_parity.py`](../../tests/parity/run_backend_parity.py)
  — the harness (Python, stdlib only). Loads each fixture once per
  backend (in-memory via `--data file.nq`; COTTAS via `--data-cottas`
  on an artifact built on the fly with the pycottas venv + DuckDB and
  cached in the workdir), runs every manifest query on every backend
  through the factoidal CLI with `-o json` (SPARQL-Results JSON),
  normalises, and diffs.
- [`tests/parity/queries.json`](../../tests/parity/queries.json) — the
  corpus manifest: 36 queries over 3 fixtures.
- [`tests/parity/fixtures/`](../../tests/parity/fixtures/) —
  `graphs_empty_default.nq` (empty default graph + 2 named graphs),
  `graphs_mixed.nq` (4 default triples + the same named graphs),
  `people.nq` (default-graph-only: typed integers/decimals,
  language-tagged literals, bnodes, OPTIONAL-shaped gaps).
- [`tests/local/backend_parity_full.sh`](../../tests/local/backend_parity_full.sh)
  — house-convention wrapper: `FACTOIDAL_BIN` / `PYCOTTAS_PYTHON` /
  `PARITY_WORKDIR` overrides, non-zero exit on any new divergence,
  expect failure, or backend error.

Run it:

```bash
tests/local/backend_parity_full.sh
```

Needs the committed platform binary and the pycottas venv at
`_tmp.junk/pycottas-venv` (session bootstrap provisions it). No F\*
toolchain, no build step.

## Query statuses

- `PASS` — all backends agree (and `expect`, if present, holds on the
  in-memory reference).
- `DIVERGENT` — backends disagree: per-backend row counts, result
  digests, and row-level differences are printed. Fails the run.
- `KNOWN-DIVERGENT` — backends disagree but the manifest entry carries
  `known_divergent`. Reported, not counted as failure.
- `EXPECT-FAIL` — backends agree with each other but the in-memory
  reference violates the entry's `expect`. This is how a bug shared by
  ALL backends is caught. Fails the run.
- `ERROR` — a backend exited non-zero, timed out (600 s cap per
  command), or emitted unparseable output. Fails the run.

Result normalisation: ASK compares the boolean; SELECT compares the
row multiset (rows sorted) unless the entry sets `"ordered": true`
(use that for ORDER BY queries). Blank-node labels are
engine-internal, so they are canonically relabelled before comparison.
CONSTRUCT is not yet covered (the CLI's JSON output is
SELECT/ASK-shaped; see follow-ups).

## Adding queries

Append to `queries[]` in `queries.json`:

```json
{
  "name": "unique-name",
  "fixture": "people",
  "query": "SELECT ?s WHERE { ... }",
  "expect": { "rows": 3 },
  "ordered": false
}
```

`expect` forms: `{"rows": N}` (row count), `{"boolean": true|false}`
(ASK), `{"single_value": "42"}` (exactly one row, one bound variable,
value string match — for aggregates). Give an `expect` to any query
whose right answer you know independently; agreement alone cannot catch
a bug both backends share. New fixtures go in `tests/parity/fixtures/`
as N-Quads plus one line in the manifest's `fixtures` map.

**Policy:**

- Every new semantic regression (the kind that today lands as a
  one-off script in `tests/local/`) also gets a parity manifest entry,
  so it is checked on every backend forever.
- `known_divergent` is the only escape hatch and MUST reference an
  open issue as `#NNN` (the harness rejects the manifest otherwise —
  same rule as `tests/beyond-w3c` `known_failures`). Removing the
  entry belongs in the same PR that fixes the bug; a
  `KNOWN-DIVERGENT` entry that starts agreeing prints
  `PASS (FIXED — remove known_divergent ...)`.
- Do not mark a divergence known without an issue. New divergences
  fail the run loudly, by design.

## COTTAS artifact writer: one deviation from the sibling scripts

The writer is the DuckDB one from
`graph_default_semantics_regressions.sh` (Parquet V2, ZSTD) but with
`DICTIONARY_SIZE_LIMIT 0`, not `1`. With limit 1, a column holding
exactly ONE distinct value (the `g` column of an all-default-graph
fixture; the `p` column of a single-predicate fixture) still fits the
dictionary and DuckDB emits `RLE_DICTIONARY` pages, which the
F\*-verified reader cannot decode. Limit 0 disables dictionaries
entirely. See "What the first run found" — this is not a footnote; it
changed the diagnosis of #267.

## What the first run found (2026-07-04)

Score: 28 of 36 queries pass on both backends, 6 known-divergent
(issue #267), 0 new divergences, 2 expect failures, 0 errors.
Backends: in-memory (`--data`), COTTAS on-disk (`--data-cottas`).

1. **#267, union-default half: confirmed.** Plain BGP over
   `--data-cottas` matches all quads, not just the default graph
   (COUNT 5 vs 0 on the empty-default fixture; 9 vs 4 mixed; ASK true
   vs false). The 6 known-divergent entries cover COUNT, SELECT, ASK,
   ORDER BY, and UNION shapes of this.
2. **#267, "generic GRAPH matches nothing" half: does NOT reproduce on
   a dictionary-free artifact.** `GRAPH ?g`, `GRAPH <iri>`, and
   `SELECT DISTINCT ?g` all agree with the in-memory backend once the
   artifact is written with `DICTIONARY_SIZE_LIMIT 0`. The
   regression-script fixtures have a single-distinct-value `p` column,
   which under `DICTIONARY_SIZE_LIMIT 1` is written as
   `RLE_DICTIONARY` — the verified reader cannot decode it, and the
   GRAPH path returned empty. Issue #267 should be updated: bullet 1
   is an engine bug, bullet 2 is (at least partly) a test-artifact
   encoding effect.
3. **Undecodable columns produce inconsistent failure surfaces.** On
   an artifact with an `RLE_DICTIONARY` column, SELECT/COUNT shapes
   fail hard (`Failure("COTTAS on-disk: could not decode column N")`)
   but `ASK { ?s ?p ?o }` silently answers `false` with exit 0 — a
   wrong answer, not an error, with no diagnostic on stderr. Needs its
   own issue: decode failure must never degrade to a result.
4. **Property paths do not evaluate on the CLI path — either
   backend.** `knows+` and `knows/name` parse (exit 0) but return zero
   rows on data where matches exist; the two manifest entries are
   deliberately left as EXPECT-FAIL (they keep the suite red until an
   issue exists or the bug is fixed). Cross-checked against the real
   W3C files: `factoidal query --data third_party/testing/w3c/sparql/sparql11/property-path/pp01.ttl --query .../pp02.rq`
   returns 0 rows where `pp02.srx` expects 2 — yet `w3c_runner`
   scores property-path 33 pass, 0 fail (out of 33). The CLI
   evaluation path is skipping path evaluation that the test runner
   performs (same eval-path-divergence family as the bnode-rewrite gap
   noted in `docs/claude-rules/current-state.md`).
5. **Parser rejects `OFFSET` before `LIMIT`.** `ORDER BY DESC(?age)
   OFFSET 1 LIMIT 2` → "SPARQL parse error: unexpected tokens after
   query"; the SPARQL 1.1 grammar allows `LimitOffsetClauses` in
   either order. Both backends share the parser, so parity cannot
   flag it — recorded here from probing; the corpus uses
   `LIMIT 2 OFFSET 1`.

Findings 3–5 have no issue numbers yet; they were found by this
harness's first run and need filing.

## Follow-ups

- File issues for findings 3–5; then either fix the property-path CLI
  gap or mark the two EXPECT-FAIL entries against the new issue.
- CONSTRUCT parity (compare canonical N-Quads of the constructed
  graph) — also relevant to #103 (CONSTRUCT over `--data-cottas`
  falls back to the eager in-memory path).
- More backends as they exist: `-n IRI=FILE` named-graph loading, the
  HTTP endpoint (`factoidal serve`) as a backend via the protocol.
- Wire into CI with a `.github/test-suites/` manifest once green
  (trigger paths: `tests/parity/**`, the COTTAS store modules, the
  evaluator).
- Fold the `graph_default_semantics_regressions.sh` checks into the
  manifest entirely once #267 closes (they are a strict subset of the
  corpus already).
