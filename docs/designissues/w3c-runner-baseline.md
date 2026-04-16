## W3C Runner Baseline

This note records the first restored conformance baseline after fixing the `w3c_runner` build path, reinitialising the `tests/w3c` submodule, and repairing stale post-extraction patches in the SPARQL OCaml output.

### Preconditions

- `tests/w3c` submodule initialised from `https://github.com/w3c/rdf-tests.git`
- `formal/fstar/build-ocaml.sh compile` completes successfully
- `formal/fstar/ocaml-output/w3c_runner --list` sees the SPARQL and RDF suites

### Current Snapshot

Initial restored baseline from the rebuilt runner:

- `bind`: `10 pass / 0 fail`
- `syntax-query`: `93 pass / 1 fail`
- `rdf-n-triples`: `41 pass / 29 fail`
- `rdf-turtle`: `284 pass / 29 fail`

Updated after the subsequent F*-side fixes in this session:

- `bind`: `10 pass / 0 fail`
- `syntax-query`: `94 pass / 0 fail`
- `rdf-n-triples`: `70 pass / 0 fail`
- `rdf-n-quads`: `87 pass / 0 fail`
- `rdf-turtle`: `290 pass / 23 fail`
- `rdf-trig`: `330 pass / 26 fail`
- `w3c_runner --all` RDF aggregate before the latest Turtle/TriG rerun: `915 pass / 116 fail`
  This aggregate is now stale on the low side because the later Turtle/TriG fixes were not folded back into a fresh `--all` run yet.

### Immediate Interpretation

The restored runner now gives meaningful overall-project progress signals again.

SPARQL:
- the parser/evaluator path is no longer blocked by missing runtime stubs
- simple query-evaluation and syntax-query are alive
- the property-path syntax miss was fixed in F* by supporting blank-node property lists in `TriplesNodePath`

RDF/Turtle:
- Turtle is substantially compliant already, but still has a concentrated tail of failures
- the failures are not random; they cluster around stricter edge cases:
  - escaped and reserved local-name handling
  - some blank-node label boundaries
  - some numeric escape rejection
  - a few IRI-resolution graph-equality mismatches
  - non-ASCII/prefix-boundary acceptance that is currently slightly over-restricted by the latest validation pass
  - some eval-bad cases that should fail but currently succeed

N-Triples:
- the strict/lenient parser split fixed the negative-syntax rejection problem

N-Quads:
- the same strict/lenient split fixed the negative-syntax path there too
- one remaining graph-label IRI permissiveness bug was fixed by requiring absolute IRIs for graph labels

### Why This Baseline Matters

This is the metric path that should guide overall project progress, not just ad hoc parser timings.

The Turtle benchmark harness is still useful for speed work, but the W3C runner is the compliance gate and the main signal for whether parser/evaluator changes are actually net positive.
