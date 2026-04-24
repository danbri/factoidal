# OWL 2 RL PositiveEntailmentTest triage (2026-04-24)

**Agent Zeta — research-only.** No `.fst` / `.ml` edits. Diagnosis only.

## Source data

- Runner: `formal/fstar/ocaml-output/owl_runner` (HEAD `4b7650e`).
- Catalog: `third_party/testing/owl/profile-RL.rdf` (1896 triples, 91 cases,
  30 PositiveEntailmentTests).
- Verbose run: `/tmp/owl_runner_verbose.out` (first missing triple per FAIL).
- F\* closure: `RDF.Graph.Executable.fst` `owl_rl_closure_step` (line 2114).
  Already implements: cls-eqc1/2, prp-eqp1/2, prp-symp, prp-trp, prp-ifp,
  prp-inv1/2, eq-ref/sym/trans/rep-s/p/o, cls-minc1-bridge, cls-svf2-qual,
  cls-minc-qual1, cls-maxqc1, cls-exactqc1, cls-maxc2, cls-avf1.

## Score

3 PASS, 27 FAIL out of 30. PASSes are: WebOnt-equivalentClass-002,
WebOnt-equivalentProperty-002, WebOnt-sameAs-001.

## Per-test classification

Format: `name — mode — blocked-on — effort`. Mode legend:

- **(a)** trivially closable; missing one named OWL-RL rule.
- **(b)** cardinality (min/max/qualified).
- **(c)** non-monotonic (negation, complementOf, contrapositive).
- **(d)** sameAs propagation across graphs/annotations.
- **(e)** vocabulary axiom emission (owl:Thing / xsd: hierarchy / NamedIndividual).
- **(f)** out-of-scope for OWL 2 RL (DL features, fresh existential witnesses).

| # | Test | Mode | Blocked-on | Effort |
|---|---|---|---|---|
| 1 | DisjointClasses-001 | (c) | conclusion = `Stewie rdf:type _:b1; _:b1 owl:complementOf Girl` — needs to fabricate complementOf bnode from `Boy owl:disjointWith Girl` + `Stewie a Boy`. This is contrapositive negation; OWL-RL has cax-dw (yields inconsistency, not complementOf triples). | big / out-of-scope |
| 2 | DisjointClasses-003 | (c) | same as #1, ternary disjoint. | big / out-of-scope |
| 3 | New-Feature-DisjointDataProperties-002 | (a) | conclusion: `_:b1 rdf:type owl:AllDifferent` (plus DisjointDataProperties rule emitting differentFrom set). Need rule `prp-adp` (DisjointDataProperties → differentFrom on members with conflicting values), or simpler: emit `_:b a owl:AllDifferent` whenever DisjointDataProperties holds. | 1 rule |
| 4 | New-Feature-DisjointObjectProperties-001 | (a) | `Peter owl:differentFrom Lois` from `Peter hasFather X; Peter hasMother X; DisjointObjectProperties(hasFather hasMother)`. This is OWL 2 RL/RDF rule **prp-pdw** (or `prp-adp` for n-ary). | 1 rule |
| 5 | New-Feature-DisjointObjectProperties-002 | (a) | as #3 but ObjectProperty side. Same rule prp-adp. | 1 rule |
| 6 | New-Feature-Keys-003 | (a) | OWL 2 RL/RDF rule **prp-key**: HasKey + matching values → owl:sameAs. Not implemented. | 1 rule (medium — keys involve list iteration) |
| 7 | New-Feature-ObjectPropertyChain-001 | (a) | OWL 2 RL/RDF rule **prp-spo2**: SubObjectPropertyOf( ObjectPropertyChain ... ). Not implemented (only prp-spo1 via rdfs subPropertyOf). | 1 rule |
| 8 | New-Feature-ObjectPropertyChain-BJP-002 | (f / harness bug) | runner reports "no-premise" — the test has `propertyChainAxiom` + annotation; parser may skip annotated axiom. Inspect parser before classifying. | unknown (probably parser/annotation, 1 module) |
| 9 | New-Feature-ObjectPropertyChain-BJP-003 | (a) | another prp-spo2 case (chain p p → p, twice for ternary). | 1 rule (same as #7) |
| 10 | New-Feature-ObjectQCR-002 | (b) | conclusion needs `_:b1 rdf:type owl:Class` synthesised from a qualified-cardinality restriction in premise. Probably needs scm-cls (every Restriction is owl:Class) — small omission. | 1 rule |
| 11 | New-Feature-ReflexiveProperty-001 | (a) | OWL 2 RL/RDF rule **prp-rfl**: ReflexiveProperty → x p x for every individual. Not implemented. | 1 rule |
| 12 | WebOnt-I4.6-003 | (d) | premise: `C1 owl:sameAs C2` with C1, C2 owl:Class. Conclusion: `C1 owl:equivalentClass C2`. Need rule: `(x sameAs y) ∧ (x a owl:Class) ∧ (y a owl:Class) → x equivalentClass y`. Not in standard OWL-RL/RDF table; status="Proposed". | 1 rule (small) |
| 13 | WebOnt-I4.6-005-Direct | (d) | annotation on c1 must propagate to c2 via owl:equivalentClass. OWL-RL does NOT propagate predicates through equivalentClass (only via sameAs). Needs scm-equivalentClass-as-sameAs for named classes (proposed in #12) plus eq-rep-s. | 1 rule (chains with #12) |
| 14 | WebOnt-I5.26-010 | (f) | conclusion has `_:n owl:onProperty :p` — fresh restriction bnode synthesised from a someValuesFrom premise; existential witness. | out-of-scope |
| 15 | WebOnt-I5.5-005 | (a) | conclusion: `_:b0 rdf:type owl:Class`. Likely scm-cls (Restriction → Class) on a bnode that already has `rdf:type owl:Restriction` in the premise. Quick win. | 1 rule (scm-cls) |
| 16 | WebOnt-I5.8-006 | (e) | needs xsd:byte rdfs:subClassOf xsd:short axiom; closure then derives `p rdfs:range xsd:short` from `p rdfs:range xsd:byte`. **Vocabulary axioms missing for the XSD numeric hierarchy.** | 1 module (XSD datatype subclass axioms) |
| 17 | WebOnt-I5.8-008 | (e) | needs xsd:short rdfs:subClassOf xsd:int and xsd:unsignedInt rdfs:subClassOf xsd:int + intersection of two ranges. Pure XSD vocab axiom problem. | 1 module (same as #16) |
| 18 | WebOnt-I5.8-009 | (e) | xsd:nonNegativeInteger ∩ xsd:nonPositiveInteger ⊆ xsd:short — needs facet semantics, not just subClass. | 1 module (XSD facet, harder) |
| 19 | WebOnt-I5.8-011 | (e) | empty-graph entailment that xsd:integer rdf:type rdfs:Datatype. Pure axiomatic — emit datatype declarations for the entire XSD hierarchy at closure start. | trivial (vocab axiom set) |
| 20 | WebOnt-differentFrom-001 | (a) | OWL-RL rule **eq-diff1 symmetry**: `(a differentFrom b)` should imply `(b differentFrom a)`. Not in standard table but trivially sound (OWL semantics treats differentFrom as symmetric). | 1 rule (small, like eq-sym) |
| 21 | WebOnt-equivalentClass-003 | (a) | premise: `C1 rdfs:subClassOf C2; C2 rdfs:subClassOf C1`. Conclusion: `C1 owl:equivalentClass C2`. **Rule scm-eqc2** (mutual subClassOf → equivalentClass). Not implemented (we have only the forward direction cls-eqc1/2). | **1 rule (cheap, high-value)** |
| 22 | WebOnt-equivalentClass-008-Direct | (d) | premise has c1 equivalentClass c2 + c1 :annotate "...". Conclusion: c2 :annotate "...". Annotation-property propagation via equivalentClass. OWL-RL does NOT do this for named classes (only via sameAs). Same fix family as #12. | 1 rule (chained with #12) |
| 23 | WebOnt-equivalentProperty-003 | (a) | premise: `hasHead rdfs:subPropertyOf hasLeader; hasLeader rdfs:subPropertyOf hasHead`. Conclusion: `hasHead owl:equivalentProperty hasLeader`. **Rule scm-eqp2** — symmetric of #21. | **1 rule (cheap, high-value)** |
| 24 | WebOnt-imports-011 | (f / harness) | conclusion `_:b0 rdf:type owl:Ontology` from premise's named owl:Ontology — appears to be IRI-vs-bnode parsing artefact (`xml:base` empty?). Investigate parser; likely not an OWL rule problem. | unknown (parser) |
| 25 | chain2trans1 | (a) | premise: `p owl:propertyChainAxiom (p p)`. Conclusion: `p rdf:type owl:TransitiveProperty`. **Rule scm-trans-from-chain** (synonym recognition: chain of length 2 of p with itself ⇒ transitive). Not in standard OWL-RL/RDF table but sound. Effort low if added as a special-case scm rule. | 1 rule (medium) |
| 26 | owl2-rl-rules-fp-differentFrom | (c) | `fp` is FunctionalProperty; premise: `Y2 fp X2; Y1 fp X1; X1 differentFrom X2`. Conclusion: `Y1 differentFrom Y2`. This is **prp-fp contrapositive** — non-monotonic. (eq-diff1 in standard table yields inconsistency; deriving differentFrom requires negation-as-failure.) | big / out-of-scope |
| 27 | owl2-rl-rules-ifp-differentFrom | (c) | symmetric: InverseFunctionalProperty contrapositive. Same problem as #26. | big / out-of-scope |

## Ranked plan (cheapest first)

### Tier 1 — single OWL-RL rule, schema-level, trivial (5 wins)

1. **#21 WebOnt-equivalentClass-003 — `scm-eqc2`**: when `C rdfs:subClassOf D ∧ D rdfs:subClassOf C` and both named, emit `C owl:equivalentClass D`. Mirror of existing cls-eqc1/2 rewriter. ~20 lines F\*.
2. **#23 WebOnt-equivalentProperty-003 — `scm-eqp2`**: same pattern for properties. Mirror of existing prp-eqp1/2 rewriter.
3. **#20 WebOnt-differentFrom-001 — `eq-diff-sym`**: `(a differentFrom b) → (b differentFrom a)`. Mirror of existing `owl_rule_sameAs_symmetry` exactly, just s/sameAs/differentFrom/.
4. **#11 New-Feature-ReflexiveProperty-001 — `prp-rfl`**: `(P a owl:ReflexiveProperty) ∧ ?x in indivs → (x P x)`. Iterate over `owl_thing_subject_iris` set already used by Group E.
5. **#15 WebOnt-I5.5-005 — `scm-cls` (Restriction)**: every `_:b a owl:Restriction` already in graph also gets `_:b a owl:Class`. Tiny axiom emission.

Expected delta: **+5** (3→8 PASS).

### Tier 2 — single rule, slightly larger (4 wins)

6. **#7 New-Feature-ObjectPropertyChain-001 — `prp-spo2`**: `(P owl:propertyChainAxiom (P1 ... Pn)) ∧ (x P1 ?y1) ∧ ... ∧ (?yn-1 Pn z) → (x P z)`. Requires walking RDF list. Reuse list-flatten helper.
7. **#9 New-Feature-ObjectPropertyChain-BJP-003 — same prp-spo2**.
8. **#4 New-Feature-DisjointObjectProperties-001 — `prp-adp`**: `DisjointProperties(P1,...Pn) ∧ (x Pi y) ∧ (x Pj y) (i≠j) → ⊥`. The PositiveEntailment side wants the contrapositive over different objects: `(x P1 y) ∧ (x P2 z) ∧ DisjointObjectProperties(P1, P2) → (y differentFrom z)`. This is the *same* contrapositive trick as #26/#27 but it works because P1, P2 are distinct properties (no inverse-functional conditional needed). Wait — the actual conclusion is `Peter differentFrom Lois` which IS contrapositive on a single shared object. Re-read: premise has `Peter hasFather Lois; Peter hasMother Lois; DisjointObjectProperties(hasFather hasMother)`. Conclusion: `Peter differentFrom Lois`. **Hmm — this requires NaF.** Move to Tier 3 / out-of-scope.
9. **#12 WebOnt-I4.6-003 — sameAs-implies-equivalentClass on named owl:Class**: `(C1 sameAs C2) ∧ (C1 a owl:Class) ∧ (C2 a owl:Class) → (C1 equivalentClass C2)`. Status="Proposed" in catalog; sound under OWL-RL.
10. **#13 WebOnt-I4.6-005-Direct — chains on #12** + existing eq-rep-s on annotation properties. Once #12 emits sameAs ⇒ equivalentClass, and we already have eq-rep-s, this should fall out IF we treat equivalentClass as sameAs for *named* classes (not for bnode restrictions). Add `owl_rule_namedClass_equivalentClass_to_sameAs`.

Expected delta from Tier 2: **+4** (#7, #9, #12, #13). Total 8→12 PASS.

### Tier 3 — module-sized (3 wins)

11. **#19 WebOnt-I5.8-011 — XSD datatype axioms**: emit `xsd:integer rdf:type rdfs:Datatype` etc. for all XSD types as part of the OWL-RL "axiomatic triples" set. Maybe 30 lines.
12. **#16 WebOnt-I5.8-006 + #17 WebOnt-I5.8-008 — XSD subClass hierarchy**: emit `xsd:byte rdfs:subClassOf xsd:short`, `xsd:short rdfs:subClassOf xsd:int`, etc. Standard XSD numeric hierarchy. ~50 lines of axiom data.
13. **#3 New-Feature-DisjointDataProperties-002 — `_:b a owl:AllDifferent`**: bnode synthesis of an AllDifferent header from DisjointDataProperties premise. Borderline (-introducing a bnode is fragile in fixpoint loops).

Expected delta: **+3** (covers tests 16, 17, 19). #18 (I5.8-009) needs facet semantics — leave for later.

### Tier 4 — out-of-scope for OWL 2 RL/RDF closure (negation / fresh witnesses)

- **#1 DisjointClasses-001, #2 DisjointClasses-003**: contrapositive complementOf bnode synthesis. (mode c)
- **#26 fp-differentFrom, #27 ifp-differentFrom**: prp-fp/ifp contrapositive (NaF).
- **#5 DisjointObjectProperties-002, #4 DisjointObjectProperties-001 (revised)**: prp-pdw contrapositive.
- **#14 WebOnt-I5.26-010**: existential witness (someValuesFrom → fresh bnode).
- **#18 WebOnt-I5.8-009**: facet semantics on XSD nonNeg ∩ nonPos.
- **#22 WebOnt-equivalentClass-008-Direct (revised)**: rolls into #13.

Net out-of-scope: **5 tests** (#1, #2, #14, #26, #27, plus #18). One catch-all: `New-Feature-Keys-003` (#6) — OWL-RL **does** include prp-key but it's medium effort (list traversal). Implementable.

### Investigation tickets (not OWL-RL rules)

- **#8 BJP-002 "no-premise"** — RDF/XML parser annotation handling. Open ticket; might unlock easy +1.
- **#24 WebOnt-imports-011** — bnode-vs-IRI for empty-base owl:Ontology. Parser, not closure. Open ticket; +1 if fixed.

## Summary delta projection

- Tier 1 (5 cheap rules): **+5**, → 8/30 PASS.
- Tier 2 (3 more rules + propagation): **+3**, → 11/30.
- Tier 3 (XSD axioms module): **+3**, → 14/30.
- Investigation (parser tickets): **+2 if both unblocked**, → 16/30.
- Tier 4 (NaF / DL): unreachable without leaving the OWL-RL profile.

**Realistic ceiling for pure OWL-RL closure work = ~14/30 (47%)**. The
remaining 16 tests need either NaF, existential witnesses, facet semantics,
or DL-grade reasoning — which the OWL 2 RL profile explicitly does not
include.

## Surprises

- **chain2trans1** (#25) is positively shocking — concluding
  `p a owl:TransitiveProperty` from `p propertyChainAxiom (p p)` is sound
  but isn't in the standard OWL 2 RL/RDF table. Easy add though.
- The two **fp/ifp-differentFrom** tests (#26, #27) are PositiveEntailment
  but require non-monotonic reasoning — they can never be closed by a
  monotonic Datalog system. These are technically *misclassified* for the
  RL profile — the catalog asserts they fall in RL, but no OWL 2 RL/RDF
  rule fires. Likely the expectation is "RL-conformant tools may answer
  YES via a separate consistency check." That's a **harness-shape** issue,
  not a rule-implementation issue.
- The **I5.8 datatype tests** (4 tests, ~13% of failures) are entirely
  about not having the XSD numeric subClass hierarchy as built-in axioms.
  One module solves three of them.
- **Bnode handling matches expectations** — the runner notes "structural
  only" matching is approximate, but I see no fail explicitly attributable
  to bnode-iso failure (verbose output points at *missing* triples, not
  bnode-mismatch on triples we did emit).

## Files to edit (not done — handoff list)

- `formal/fstar/RDF.Graph.Executable.fst`:
  - Add `owl_rule_scm_eqc2`, `owl_rule_scm_eqp2`, `owl_rule_diff_symmetry`,
    `owl_rule_reflexive_property`, `owl_rule_scm_cls_restriction`,
    `owl_rule_prp_spo2`, `owl_rule_named_sameAs_to_equivClass`.
  - Wire into `owl_rl_closure_step` after existing rules.
  - Extend `owl_thing_axioms` (or add new fn) with XSD `rdfs:Datatype` and
    XSD numeric `rdfs:subClassOf` axioms for I5.8 family.
- No patch-script changes needed (rules are pure F\*).

## How to verify (after fixes)

```
cd formal/fstar
./build-ocaml.sh         # extract + compile
./ocaml-output/owl_runner -v
```

Look for new PASS lines. Score line at the bottom should rise from
"3 pass, 27 fail" toward target 14/30.
