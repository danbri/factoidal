# G4: SPARQL theorem-backed end-to-end (program plan)

**Owner goal (2026-08-09, verbatim):** "SPARQL theorem backed end to
end: parser, expression eval, solution modifiers, filters, results....
Push F\* theorems as far as they can go, giving us a solid basis for
improvements, optimisations, indexing and persistent storage."

**Starting point** (see theorem registry §5 and the layer accounting
that motivated this goal): BGP matching, join keys, dedup keys,
planner reordering, index access, and the corerdfs entailment chain
are theorem-backed on the shipping entry points. The unproved
semantic surfaces in a response are the two edges — parsing in,
serialization out — and the expression language + modifiers between.

## Milestones (value order)

- **M1 Parser.** The largest unproved surface: a parse bug makes every
  downstream theorem answer the wrong question. Target: round-trip
  theorem `parse (print q) == Some q` over the algebra (requires an
  F\*-side printer if none exists — scout confirms), or failing that,
  per-production soundness on a stated grammar subset. Every claim
  labelled with the subset it covers.
- **M2 Expressions/FILTER.** Per-operator lemma fan-out against an
  independent F\* transcription of the SPARQL/XPath operator tables
  (EBV, numeric promotion, comparison, the type-error lattice) — the
  proof-factory shape that carried the OWL licensing program: one row,
  one spec predicate, one lemma.
- **M3 Solution modifiers.** ORDER BY: comparator lawfulness (total
  preorder) + sort correctness (sorted permutation of input); LIMIT/
  OFFSET window lemmas; projection soundness. DISTINCT already rests
  on sp_key injectivity (#338).
- **M4 Results.** Serializer round-trips (serialize then parse = id)
  for SRJ first (parser exists in-tree for the test harness), then
  SRX/CSV/TSV as parsers allow.
- **M5 Composition.** Extend the exact-answer theorems through the
  modifier pipeline so the corerdfs regime claim covers the RESPONSE,
  not the BGP layer — the goal's "solid basis" deliverable: any
  optimisation/indexing/storage change must preserve stated theorems,
  not test suites alone.

## Method

proof-factory skill governs dispatch (closure-identity law, guard
depth ≤3, brief anatomy, spray-and-verify economics, harvest
pattern). Registry updated with every landing. No --lax, no admits.
Findings discipline: refuted statements become machine-checked
counterexample rows, as in G3.
