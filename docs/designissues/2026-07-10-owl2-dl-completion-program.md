# OWL 2 DL completion program: tableau to full coverage

Date: 2026-07-10. Status: PLAN (written during a network outage on a
rolled-back container; baseline numbers are from the tableau landing
report of the same day, branch `worktree-tableau-refute` commit
`4d04cc8`, pushed to origin — re-verify against
`docs/test-results/latest.json` once the landing merges).

Owner goal (2026-07-10 `/goal`): level up implementation + npm FP JS
API + hub docs for OWL2 DL/tableau to complete coverage.

**Update 2026-07-14 (obsolescence sweep):** five tableau waves landed
since the baseline below — datatype facet satisfiability, role box
(subPropertyOf/FunctionalProperty/transitive), contrapositive
unfolding of definitions + exact-cardinality-0 NNF, SHIQ ≤-rule
witness merging, and named-individual identification + stored FP
max-1 bounds. Current measured scores: type-inconsistency (DL) 110
pass, 18 fail (out of 128 scored); type-consistency (DL) 334 pass, 18
fail (out of 352). Soundness gate held throughout: exactly one
`unexpected-inconsistency` (WebOnt-miscellaneous-202, pre-existing,
tcon only). See `docs/claude-rules/current-state.md` and
`w3c-completeness-ledger.md` for the current snapshot; the wave
letters actually landed (datatype facets / role box / contrapositive /
≤-rule / named-merge) diverge from the A–E plan below — treat the plan
as the historical starting point, not the executed sequence.

## Baseline (measured, 2026-07-10)

All DL-regime numbers from the rebuilt binaries of the tableau landing:

- type-inconsistency (DL): 66 pass, 51 fail (out of 117 scored), 11
  skipped (functional-syntax-only inputs).
- type-consistency (DL): 328 pass, 18 fail (out of 346).
- semantics-direct: PE 103 pass, 101 fail (out of 204); NE 22 pass,
  1 fail (out of 23); Cons/Inc as above.
- Soundness: exactly one `unexpected-inconsistency`
  (WebOnt-miscellaneous-202, pre-existing, #236 territory).
- profile-EL Inc 9 pass, 5 fail; profile-QL Inc 6 pass, 0 fail.

`Tableau.Refute.fst` (~1050 lines, verified, zero admits/assume vals)
implements: NNF, lazy TBox unfolding, index-ordered disjunction
branching under a threaded linear budget, depth-capped existential
witnesses, and clash rules for complement/boolean, min/max cardinality
(incl. qualified), differentFrom-backed counting, self-disjoint
properties, Bottom/Top property assertions, AllDifferent, rdf:nil
structure, and hasSelf+disjointness.

## Remaining fail families (from the landing report's enumeration)

1. **Nominals / oneOf** (largest single family). Requires ABox
   individuals inside class expressions: `O`-rule (x : {a} implies
   x = a) and its interaction with counting. Plan: represent nominal
   membership as a merge constraint; reuse the existing
   differentFrom-aware counting for the clash side. No full equality
   saturation — merge classes lazily, as the RL closure already
   maintains a sameAs partition we can consult.
2. **Datatype facets**: literals asserted into facet-restricted
   datatypes (xsd:minInclusive etc. via DatatypeRestriction).
   `XSD.Datatypes.fst` already carries lexical + value-space checks
   for the base types; the missing piece is a facet-satisfiability
   checker over value-space intervals (rational endpoints, open/closed)
   + string length/pattern facets where the corpus needs them. Keep it
   interval-based and total; the corpus does not need general regex
   intersection (verify against actual fixtures before building any).
3. **Finite-model counting** (dl-909/910 class): max-cardinality on a
   property whose fillers are forced into fewer distinct individuals
   than min-cardinality demands, requiring pigeonhole reasoning across
   merges. Plan: bounded merge-search under the existing budget — when
   a max-card clash candidate has unmergeable fillers
   (differentFrom/distinct literals), report clash; when mergeable,
   branch on merges (budgeted).
4. **FP/IFP equality chains**: FunctionalProperty/
   InverseFunctionalProperty forcing y1 = y2, propagating into other
   clash rules. Plan: same lazy-merge machinery as nominals — a
   union-find threaded through the tableau state (pure, persistent;
   F* map-backed).
5. **Budget-outs** (deep propositional cases): raise
   `FACTOIDAL_OWL_REFUTE_FUEL` selectively? No — first profile which
   tests exhaust budget and whether ordering heuristics (clash-first
   branch ordering, unit propagation before split) shrink the search.
   Only then consider budget raises, measured.
6. **Consistency-side 18 fails + PE 101 fails**: PE (positive
   entailment) largely reduces to refutation of the negated conclusion
   — once the refuter is stronger, wire PE through
   refute(KB + not(conclusion)) for the class/property-assertion forms
   the corpus uses (the existing anchor-based rewrite covers the
   entailment-regime suite; this extends DL-catalog coverage). The 11
   functional-syntax-only skips need the OWL FS parser path wired into
   the DL runner (parser exists since wave 9).

## Wave structure (one agent per wave, one commit each, soundness gate every time)

- **Wave A (nominals + lazy merge)**: union-find state + O-rule +
  merge-aware counting. Target: the oneOf/nominal family + a bite of
  finite-model counting. Gate: zero new unexpected-inconsistency.
- **Wave B (datatype facets)**: interval facet checker in F*,
  clash on empty facet intersection / literal-outside-facet. Scope
  strictly to fixture-exercised facets.
- **Wave C (FP/IFP + finite-model)**: functional-property merges via
  the Wave A machinery; pigeonhole branching under budget.
- **Wave D (PE via refutation + FS parser wiring)**: negate-and-refute
  for the corpus's conclusion forms; unskip the 11 FS-only tests.
- **Wave E (budget/heuristics)**: profile budget-outs, ordering
  improvements, measured fuel policy.

Each wave: fail-set diff (names, not counts), floors (SPARQL 631/0,
RDF 1031/0, RIF 46/1/3, ShEx-neg 100/0), and the one pre-existing
WebOnt-202 soundness exception must stay exactly one.

## npm FP JS API (parallel track, after Wave A lands)

Expose reasoning to the bundle per the engines pattern (typed fn.*):

- `fn.owlIsConsistent(ontologyTtl, opts?) -> {consistent: boolean|null, reason?: string}`
  (null = budget-out, reason names the cap — never a silent false).
- `fn.owlEntails(premiseTtl, conclusionTtl, opts?) -> {entailed: boolean|null, via: "closure"|"refutation"}`.
- `fn.owlClassify(ontologyTtl)` — subsumption pairs from the closure
  (already computable via RL rules; label it RL-closure-based, not DL-complete,
  until refutation-backed classification exists).
- Unit tests mirror the corpus: one inconsistent fixture per clash
  family, one budget-out fixture asserting `null`.

## Hub docs (post 30 level-up, after the API lands)

Post 30 ("OWL reasoning by model construction: the tableau") gains
live cells: a textarea ontology cell -> `fn.owlIsConsistent` verdict
cell -> a rendered clash-trace summary (the refuter's reason string),
plus canned examples per clash family (the corpus's spirit, original
data). Live cells call fn.* only; bundle rebuild with npm-entry forced;
`tests/hub/post30*` extended. Anti-pattern #28 applies.

## Ordering + landing discipline

Waves land sequentially onto claude/main (no long-lived stack), each
via the dedicated-landing pattern if its base drifts. The npm/hub
tracks branch after Wave A and land independently. All scores labelled
per anti-pattern #25; dashboard rows via the normal generate-report
path.
