# OWL runner Phase 1 — wire owl_rl_closure through profile-RL PositiveEntailmentTests

**Date:** 2026-04-24
**Owner:** claude/main (scratch)
**Status:** implementation in flight

## Goal

Take `owl_runner` from Phase 0 skeleton (prints manifest inventory, no
reasoning) to Phase 1: actually runs the closure against every
`test:PositiveEntailmentTest` in `third_party/testing/owl/profile-RL.rdf`
and prints a labelled score per rule #25.

## Algorithm (one PositiveEntailmentTest)

1. Walk the parsed catalog graph. For each subject `s` whose `rdf:type`
   set contains `&test;PositiveEntailmentTest`, collect:
   - `test:rdfXmlPremiseOntology` — literal string (RDF/XML body).
   - `test:rdfXmlConclusionOntology` — literal string.
   - `test:identifier` — human label.
2. Pre-expand the DOCTYPE-declared catalog entities (`&rdf;` `&rdfs;`
   `&owl;` `&test;` `&xsd;`) in each string. Same function as the
   manifest-load path — this is I/O glue per rule #15.
3. Parse each via `Parser_RDFXML.parse_rdfxml_with_base` to get
   `g_premise` and `g_conclusion` triple lists.
4. Apply `RDF_Graph_Executable.owl_rl_closure_with_reflexivity
   g_premise (Z.of_int 100)` → `g_closed`.
5. Entailment check: every triple of `g_conclusion` must be matched by
   some triple of `g_closed`.
   - **Non-bnode triples** — exact match by `triple_eq`.
   - **Bnode-containing triples** — relaxed "structural" match:
     same predicate, same non-bnode positions match exactly, bnode
     positions match any bnode in `g_closed`. This is an over-
     approximation; proper bnode isomorphism is deferred.
6. Aggregate: `pass` if every conclusion triple matched, else `fail`.
   Record first failing triple for debug output on `-v`.

## Output

```
Profile-RL PositiveEntailmentTests: N pass, M fail (out of K)
  (bnode match is structural; full isomorphism deferred — see Phase 1 doc)
```

## Failure modes we expect

- Parse failures on premise/conclusion (closing `]>` inside escaped text
  confuses strip_doctype, or entity expansion miss). Count these as
  fails and print a `PARSE-FAIL` marker so they're distinguishable from
  closure gaps.
- Closure-rule gaps in `owl_rl_closure_with_reflexivity` — this is
  the *point* of scoring. The number will start low and grow as F* side
  lands more RL rules.
- Relaxed bnode matching may under-report failures (structural match
  accepts graphs that a proper isomorphism check would reject). This is
  documented in the stdout tail so we can't forget.

## Report integration

Add a single line to `generate-report.sh` (or a tiny helper) under the
existing SPARQL table:

> **OWL 2 RL (W3C conformance):** `N / K` PositiveEntailmentTests pass
> — profile-RL manifest, bnode match relaxed.

Separate denominator from the SPARQL suite's — they're different
corpora. If the report wiring runs long, defer to a follow-up commit
and keep this commit to the runner itself.

## Out of scope (defer)

- NegativeEntailmentTest (Phase 2) — need non-entailment check + at
  least one absent triple.
- ConsistencyTest / InconsistencyTest (Phase 3) — needs contradiction
  detection layer.
- ProfileIdentificationTest (Phase 4) — syntactic.
- EL, QL, direct semantics (Phases 5–6).
- Proper bnode isomorphism.
- `Parser.XML.fst` native DOCTYPE-entity support.
