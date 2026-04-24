# RDFC-1.0 — Phase 0 skeleton (Agent Gimel, task #40/48)

Date: 2026-04-25
Status: Phase 0 (skeleton-only) follow-up to
`2026-04-24-rdfc10-plan.md`. Wires the W3C RDFC-1.0 suite into the
test scoreboard with a placeholder canonicaliser so failures are
visible and labelled.

## Summary

Yesterday's plan (`2026-04-24-rdfc10-plan.md`) sketched the algorithm
and a 5-phase ramp. Today I land Phase 0 only: the *runner skeleton*
that reads the manifest, dispatches per test type, runs a no-op
canonicaliser, compares to expected, and reports a labelled score.
This makes RDFC-1.0 visible on the public test-results page (per the
"never write cryptic score strings" rule #25) instead of being silently
absent. Honest baseline: large FAIL count + small accidental-pass
count from trivial bnode-free tests (test001 is bnode-free → no-op
identity wins).

## What was found in the corpus

`third_party/testing/rdf-canon/tests/`:

- 89 total `mf:entries` in `manifest.ttl`.
- Counts by `rdf:type`:
    - 65 `rdfc:RDFC10EvalTest` (positive: input nq → expected nq)
    - 22 `rdfc:RDFC10MapTest` (input nq → expected JSON issued-id map)
    - 2  `rdfc:RDFC10NegativeEvalTest` (reject input)
- 60 distinct `rdfc10/testNNN-in.nq` input files.
- 60 expected `rdfc10/testNNN-rdfc10.nq` output files.
- 22 expected `rdfc10/testNNN-rdfc10map.json` map outputs.

Manifest shape per entry (already worked out yesterday):

```turtle
:test001c a rdfc:RDFC10EvalTest;
  mf:name "simple id";
  rdfc:computationalComplexity "low";
  rdft:approval rdft:Approved;
  mf:action <rdfc10/test001-in.nq>;
  mf:result <rdfc10/test001-rdfc10.nq>;
  .
```

## F\* coverage today

`grep -ril "canonicaliz\|RDFC\|bnode_canonical"
formal/fstar/` shows zero coverage. The only matches are unrelated
mentions in `Parser.RDFXML.fst` (RDF canonical syntax / lexical-form
canonicalisation, separate concept) and a stray comment in
`SPARQL11.Algebra.fst`. **No RDFC-1.0 algorithm exists in F\* yet.**
Phase 0 is therefore a runner-only skeleton; the no-op canonicaliser
is a placeholder so the score harness has something to wire to.

What we do already have, ready to call (per the 04-24 plan):

- `Parser_NQuads.parse_nquads_with_base` — reads input.nq files.
- `RDF_Graph_Executable.rdf_dataset` etc. — type representation.
- `fstar_pure_hashes.sha256_hex` — for when Phase 1 lands.
- `Parser_Turtle.parse_turtle_with_base` — for the manifest itself.

## Phase B (this commit) deliverables

1. `formal/fstar/ocaml-output/rdfc10_runner.ml` — new hand-authored
   runner. Parses manifest via Parser_Turtle, extracts entries,
   dispatches per test type, runs `canonicalize_noop` on the input
   N-Quads, compares serialised output bytewise to expected, prints
   per-test status, emits a labelled total per rule #25.
2. `formal/fstar/build-ocaml.sh` — add `rdfc10_runner` to the binary
   list (parallel to `owl_runner`).
3. CSV row in the public test-results page so the suite shows up.

Out of scope for this commit (deferred to Phase 1):

- The actual canonicalisation algorithm (first-degree hash, issuer,
  n-degree hash). These belong in F\*, not the runner.
- Map-test verification — runner reports them as `STUB` for now.
- Negative-test handling — same.

## Expected score impact

Likely **0 new passes, ~89 new visible fails** in the harness.
Possible accidental passes: tests with no blank nodes (test001 et
al. — input contains no `_:` so no-op canonicalisation is a perfect
identity transform if our N-Quads serialiser matches the spec's
canonical form byte-for-byte). Hard to predict before running; the
honest signal is "the suite is now visible in the score".

## Hard limits respected

- No `.fst` files touched (skeleton is pure I/O glue, rule #10).
- No `build-ocaml.sh extract` / `compile` run on this thread (Wave 8
  rebuild is on the main thread).
- No `--lax`.
- 60-min wall-clock cap.
