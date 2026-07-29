# Project scope — what factoidal does and does not cover

Companion to `CLAUDE.md`. Lists features that are explicitly **not planned**
so future agents (and humans) don't burn cycles attempting them.

## In scope

- RDF 1.1 abstract syntax + all core serialisations (N-Triples, Turtle,
  N-Quads, TriG, RDF/XML, JSON-LD).
- SPARQL 1.1 Query, Update, Protocol, federated `SERVICE`.
- SPARQL 1.1 result formats (XML/SRX, JSON, CSV, TSV).
- RDF model theory / RDFS entailment (forward-chaining closure in F\*).
- OWL 2 RL entailment (rule-based subset, F\* closure rules).
- OWL DL via `OWL.QueryRewrite` rewriter for queryable fragments
  (`someValuesFrom`, `allValuesFrom`, `unionOf`, `intersectionOf`,
  cardinality CEs) — best-effort, not full DL classification.
- RIF Core — the frame/BGP-shaped rule-body subset exercised by the
  4 vendored W3C RIF test cases plus the applicable subset of the
  full vendored Core dialect corpus (see below), verified in
  `RIF.Core.Syntax.fst` / `RIF.Core.Translation.fst` /
  `RIF.Core.Eval.fst` + `Parser.RIFXML.fst`, driven end-to-end by
  `bin/rif-runner/rif_runner.ml`.

## Out of scope — not planned

### RDFa and Microdata — web-platform territory (owner decision, 2026-07-05)

RDFa Core/HTML+RDFa and HTML Microdata are the only Rec-track RDF
extraction syntaxes with zero implementation here. Deliberate: they
require HTML parsing and web-platform semantics ("we don't go near
'web platform' yet" — owner, 2026-07-05). Revisit only if the project
grows a browser-ingestion story.

### RDF 1.2 / RDF-star — SUPERSEDED: un-parked and largely landed

> This entry previously said "deferred to v1 by design (owner, 2026-07-05),
> no quoted-triple term type exists in the tree." Both halves are now
> false. RDF 1.2 / SPARQL 1.2 was **un-parked (owner, 2026-07-16)** and the
> term-model + text/line syntaxes are implemented and verified. Kept here
> only as a pointer, since other docs cited this section as the authority
> for "1.2 is future work."

Current state (see
[`w3c-completeness-ledger.md`](w3c-completeness-ledger.md) for the live
scoreboard): `RDF.Term` now carries the `T_TripleTerm` constructor and
`text_direction` / `rdf:dirLangString`. Landed + verified (no `--lax`):
N-Triples, N-Quads, Turtle, TriG triple terms `<<( s p o )>>`, `~`
reifiers, `{| |}` annotation blocks, `VERSION` directive, directional
literals `"x"@lang--dir` — **RDF 1.2 syntax/eval 212 pass, 0 fail**;
**SPARQL 1.2 248 pass, 6 fail (out of 254)**.

Still genuinely open (do NOT claim these): RDF/XML 1.2, the RDF 1.2
canonicalization suite (86 tests) and entailment regime (74 tests), the
6 remaining SPARQL 1.2 eval fails, RML-star mapping generation, and
exposure through the browser/npm API + dashboard (the `parse`/`query`
JS surface still runs 1.1 mode only — a triple term handed to `fn.parse`
today is silently dropped). Tracked under epic #305.

### RIF Core (Rule Interchange Format) — supported subset only

RIF Core is a full production-rule language; factoidal implements the
fragment the W3C RIF Core test distribution exercises: `Forall` /
`Frame` / `And` / `Implies` rule bodies translated to SPARQL BGPs
(`RIF.Core.Translation.fst`, including Uniterm argument-value
satellites and n-ary >= 3 reification since 2026-07-10),
forward-chaining fixpoint saturation (`RIF.Core.Eval.fst`),
`External(...)`/`Equal` body conditions over the RIF-DTB builtin
subset in `RIF.Core.Builtins.fst` (numeric, string, rdf:PlainLiteral
families; a dateTime slice; `pred:iri-string` with binding-pattern
execution), `Exists`-quantified conclusions, per-document `rif:local`
scoping, dialect conformance checking (`RIF.Core.Conformance.fst`:
safeness, free variables, import rejection, cross-document
constant-role tracking, OWL-Direct vocabulary-separation
inconsistency), and single `<Import>` companion-graph resolution
(with OWL-Direct closure applied first when the import's own
`<profile>` declares it — see `bin/rif-runner/rif_runner.ml`'s
`apply_import_closure`). RIF **List terms**, the **full
date/time/duration builtin family** (only the EBusiness slice is
implemented), and RIF-PRD (production rules, actions, retraction)
are **not implemented**; RIF-PRD is not planned.

**Concretely:** the 4 RIF tests under
`third_party/testing/w3c/sparql/sparql11/entailment/` (manifest IRIs
`:rif01 :rif03 :rif04 :rif06`, all tagged `sd:entailmentRegime ent:RIF`)
now PASS, measured via `bin/rif-runner/rif_runner.ml` (4 pass, 0 fail
out of 4, 2026-07-04):

- `:rif01` — RIF Logical Entailment (referencing RIF XML).
- `:rif03` — RIF Core WG tests: Frames.
- `:rif04` — RIF Core WG tests: Modeling Brain Anatomy (the imported
  ontology needs OWL-Direct closure — `owl_rl_closure_with_reflexivity`
  + `Tableau.tableau_materialise` — before the rule body's
  `rdf:type MaterialAnatomicalEntity` check matches individuals the
  ontology only asserts via `rdf:type Gyrus` + `rdfs:subClassOf`).
- `:rif06` — RIF Core WG tests: RDF Combination Blank Node.

Any RIF document whose rule bodies or imports fall outside the
frame/BGP + single-`<Import>` shape above is out of scope; a runner
encountering one should report an honest FAIL/SKIP with a diagnosis,
not force a PASS.

**Full Core dialect corpus (2026-07-10):** `bin/rif-runner/rif_runner.ml`
also walks the complete official W3C RIF Core dialect test
distribution vendored at `third_party/testing/rif-core-suite/`
(46 tests — see that directory's `README.md` for source/license/
inventory, and `bin/rif-runner/README.md` for the full pipeline,
score, and per-test disposition table). Measured 2026-07-10:
**42 pass, 1 fail, 3 skip (out of 46)**; combined with the 4 tests
above, **46 pass, 1 fail, 3 skip (out of 50)** — up from 34 pass,
4 fail, 12 skip on 2026-07-05 and 11 pass, 3 fail, 36 skip at the
corpus walker's first landing. The 1 FAIL is a data defect in the
official corpus itself (`RDF_Combination_Constant_Equivalence_4`'s
malformed `xsd:string` datatype IRI — present in both the
`Core_v1.22.zip` files and the archived authoritative wiki source,
checked 2026-07-10); the 3 skips each name their gap (RIF List
terms ×2; the full date/time/duration builtin family, where only
the EBusiness_Contract slice is implemented).

### Full OWL DL tableau classifier

The `Tableau.fst` module sketches stages (a)–(e) but a complete
DL tableau (skolemisation, disjunction blocking, complementOf
contrapositive, fresh-individual witnesses) is not the project goal.
Specific DL-only entailment tests (`paper-sparqldl-Q3`, the OWL 2 RL
fp/ifp-differentFrom contrapositive cases) are tracked in #58 and the
OWL-RL triage doc but are not in the current critical path.
`WebOnt-I5.26-010` is tracked separately below (comprehension
entailment, not a tableau gap).

### OWL 1 Full comprehension-principle entailments — WebOnt-I5.5-005, WebOnt-I5.26-010 (IMPLEMENTED 2026-07-28, PE-only witness layer)

**Status change (2026-07-28).** These two were carried here as a
permanent scope exclusion from 2026-07-05 to 2026-07-28. The exclusion
reasoning was: the entailments have no premise-side antecedent to hang
a Horn rule off of (OWL 1 Full's comprehension conditions guarantee
them; OWL 2's RDF-Based Semantics demoted comprehension to the
informative Section 8 appendix), so any rule firing on them would be an
unconditional triple generator polluting EVERY closure — tableau
inputs, consistency scoring, SPARQL entailment regimes included.

That polluting-generator objection was an objection to WHERE such a
generator would run, not to its soundness — and the escape hatch this
section itself proposed ("if a future comprehension mode is ever built
as its own opt-in layer, gated so it never leaks into the OWL 2
RL/Direct closures scored by the floors") is what landed on 2026-07-28:
the comprehension-witness rules `owl_rule_comp_singleton_union`
(I5.5-005) and `owl_rule_comp_min1_restriction` (I5.26-010) live in the
**PositiveEntailmentTest-only witness layer**
(`owl_rl_closure_with_reflexivity_and_witnesses`,
`formal/fstar/OWL.Closure.fsti` section 20b), which the runner consults
only as a retry after the plain closure misses a PE conclusion. The
shared closure, the DL tableau's `g_rl` input, ConsistencyTest /
InconsistencyTest / NegativeEntailmentTest scoring, and SPARQL
entailment-regime evaluation never see these triples, so every floor in
`skills/test-suites/SKILL.md` is unaffected (measured 2026-07-28:
type-positive-entailment 173 pass, 31 fail -> 178 pass, 26 fail out of
204, FAIL-name diff a strict subset; all other catalogs unchanged).

The layer's banner documents the deliberate weakenings versus full
(iff) comprehension — premise-anchored witnesses only, one canonical
instance per declared class/property, single stratified pass with no
witness-of-witness — following ter Horst's pD* if-semantics design
(JWS 3(2-3), 2005), which is what keeps the generator finite and
terminating. Three sibling rules in the same pass close the related
list-synthesis comprehension tests (`WebOnt-unionOf-003/-004`,
`WebOnt-oneOf-004`).

### Non-monotonic / negation-as-failure inference

Tests requiring NaF (e.g. WebOnt fixed-point complementOf) are
monotonically unreachable by OWL-RL closure and out of scope for any
Datalog-style closure loop. Tracked in #58.

### XSD facet semantics beyond datatype subClass hierarchy

The XSD numeric subClass hierarchy (`xsd:byte ⊑ xsd:short ⊑ xsd:int ⊑
xsd:integer` etc.) is in scope as built-in axioms.
Facet-level reasoning (e.g. `xsd:nonNegativeInteger ∩
xsd:nonPositiveInteger ⊑ xsd:short`) is not.

## Update protocol

When a scope decision changes (in either direction), update this file
**in the same commit** that introduces the new feature or removes the
last code path supporting the dropped one. Do not let the doc drift.
