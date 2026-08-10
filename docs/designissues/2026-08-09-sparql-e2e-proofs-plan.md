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

## G1 fold-in (owner decision)

Owner, 2026-08-09, on folding the G1 review-kernel remainder into M5:
"Yes fold it in." M5 therefore delivers BOTH the composed
response-level theorems AND the curated review kernel (the minimal
set of spec predicates + theorem statements a W3C expert can read
end-to-end, with the guarantee nothing outside it overrides what it
states) — assembled at the same time because composition is when the
kernel's contents become final. Task #38's kernel item transfers to
task #46/M5; the G2 remainder (claims block, npm batch) stays in
task #40.

## Fast-path re-founding constraints (owner steer, 2026-08-10, verbatim)

> "Refound migration - the mention of ocaml scares me as earlier
> Claudes slipped into writing everything in ocaml, and it took weeks
> to recover. This cannot be that again.
> Also, we need practical performant parsers (memory, speed,
> streaming; error recovery from realworld data flaws"

Binding constraints on the FastString migration and all parser work:
1. ACCEPTANCE CRITERION: every semantic decision has an extracted F*
   definition as its source; anything OCaml is substitutable,
   equivalence-gated (rule 11(b) Option-B), and deletable. The
   migration REMOVES hand-written OCaml semantics (patch 89's realised
   assume vals); optimized OCaml returns only if benchmarks demand it.
2. Benchmark-gated at every step (parser throughput harness,
   perf-benchmarking discipline) — no perf regressions on faith.
3. Streaming: N-Quads chunk-fold with bounded carry; streaming==batch
   as a theorem; line-based formats first.
4. Error recovery as proof targets: strict mode = position-carrying
   errors; lenient mode = resync-point skip with recovery-soundness
   theorems (every emitted triple grammatical, every skip reported
   with position, silent drops impossible — retires the #334/#344
   bug class by construction).
