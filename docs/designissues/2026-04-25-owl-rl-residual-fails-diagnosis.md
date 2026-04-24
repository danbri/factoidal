# OWL 2 RL residual PositiveEntailment failures (Agent Omega — 2026-04-25)

Diagnose-and-fix mission: 5 OWL 2 RL PositiveEntailment tests still FAIL despite
relevant closure rules having been added in commits `c08b777` (Nu, XSD datatype
axioms) and Iota's `scm-cls` / `prp-rfl` work.

Tests under investigation:

- `WebOnt-I5.5-005` — Iota added `scm-cls` (Restriction → Class) — still FAIL.
- `WebOnt-I5.8-006` / `008` / `009` / `011` — Nu added `xsd_datatype_axioms` — still FAIL.

Plan:

1. Locate test inputs in `third_party/testing/owl/profile-RL.rdf` (catalog) and
   per-test source `.rdf` files.
2. Run `./bin/darwin-arm64/owl_runner -v` to see the precise mismatch line per
   test (missing triple? extra triple? bnode-iso failure?).
3. Compare premise + conclusion to the rule's actual firing condition.
4. Patch `RDF.Graph.Executable.fst` only if the fix is small (≤80 lines), no
   logic in OCaml patches. Otherwise, hand off with a precise next-step plan.

WIP — to be updated with findings.
