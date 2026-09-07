# RDF 1.2 Semantics — Factoidal tight cases

Not a W3C suite, and never reported together with one.

Every entry states a reading of RDF 1.2 Semantics that the vendored
`third_party/testing/w3c/rdf/rdf12/rdf-semantics` manifest either
contradicts or cannot express. The reasoning, with specification
citations and the upstream evidence, is in
[`docs/designissues/2026-09-07-rdf12-sparql12-semantics-fstar.md`](../../../docs/designissues/2026-09-07-rdf12-sparql12-semantics-fstar.md).

Run:

```
RDF12_TESTS_BASE=tests/local bin/<platform>/w3c_runner \
  --rdf12entail rdf12-semantics-tight
```

Score, 2026-09-07: **6 pass, 1 fail (out of 7)**. The one fail is
`literal-type` — the D-entailment rule "a literal denotes an instance of
its datatype" is stated here but not yet implemented in
`RDF.Entailment.Regime`. It is a fail on purpose: the vendored copy of
this test is invisible (its manifest block has an undeclared prefix), so
without this file the gap would show as a silent skip.

The vendored tree is never edited. Fixtures here are byte-identical
copies of the vendored ones where a vendored fixture exists, so a
difference in outcome can only come from the manifest entry.
