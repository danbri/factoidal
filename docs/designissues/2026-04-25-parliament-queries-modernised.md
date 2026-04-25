# 2026-04-25 — Modernised UK Parliament SPARQL queries (Agent He2)

## Problem

The 24 vendored Parliament queries at
`third_party/data/ukparliament/sparql/{main,detail}/*.rq` mostly target
specific `id.parliament.uk/X` IRIs (e.g. `<id:1AFu55Hs>` for House of
Commons) that are not present in the 2019-07-27 N-Quads snapshot served
on the live endpoint. 22 of 24 queries return `rows=0` against the
current data shape, even though they are valid SPARQL.

## Goal

Land a parallel set under `tools/sample-queries/ukparliament/{main,detail}/`
that:

- Preserves the *intent* of each vendored query (count? listing?
  overview? join across incumbencies?).
- Is data-shape-aware for the 2019 dump:
  - top classes: `WebArticle` 331, `ParliamentPeriod` 73, `Person` 35,
    `Question` 34, `FormalBody` 32, `Member` 16, `House` 18, `EPetition` 24,
    `Answer` 24
  - top predicates per `docs/test-results/ukparliament-bench.csv`:
    `ePetitionHasLocatedSignatureCount`, `signatureCount`,
    `signatureCountRetrievedAt`, `locatedSignatureCountHasPlace`,
    `answerExpectationStartDate`, `parliamentaryIncumbencyHasMember`,
    `seatIncumbencyHasParliamentPeriod`, etc.
- Replaces hard-coded entity IRIs with class-driven patterns so the
  queries surface real rows (binding `?house a :House` rather than
  `<id:1AFu55Hs>`, etc.).
- Keeps the originals strictly untouched (vendored = sacred).

## Plan

1. Read all 24 .rq files; note shape + assumed entity IDs per file.
2. Write modernised versions to
   `tools/sample-queries/ukparliament/{main,detail}/<orig_name>_modern.rq`.
3. Test each against `http://100.107.116.70:3030/sparql` with the same
   POST envelope used by `tools/bench_ukpar_queries.py`.
4. Add `tools/bench_ukpar_modern.py` mirroring `bench_ukpar_queries.py`
   but rooted at the modernised tree; write a sibling CSV/JSON.
5. Commit `tools: modernised vendored Parliament queries (rows>0 against 2019 snapshot)`.

## Constraints

- 60 min budget, hard.
- Not all originals will have a meaningful equivalent in this snapshot
  (e.g. step-collections / procedures / business-items do not appear in
  the top class list). Those get a one-line note in the modernised file
  rather than a fake query.
- Don't edit `third_party/`, don't touch `.fst` files, don't run extract.
