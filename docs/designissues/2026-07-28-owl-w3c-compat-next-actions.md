# OWL 2 W3C conformance — prioritized next actions (2026-07-28)

Scope: what is actually failing in the OWL 2 W3C test suite right now, grouped
by root cause (read from the failing tests' own premise/conclusion fixtures,
not guessed from test names), and a commit-sized action list ordered by
tests-gained per unit of effort.

Method note: every group below cites the specific fixture triples that were
read to establish the root cause. Groups C, D(partial), E(partial), F, H are
each backed by at least one fully-read premise/conclusion pair per pattern.
Groups G, J, K, L are backed by 1-2 read examples per group and extrapolated
across the rest of the group's members by shared `test:description` /
`test:status` metadata — flagged inline where a member was not individually
read.

## 1. Current scores

| Suite | Score | Source |
|---|---|---|
| type-positive-entailment (DL regime) | 140 pass, 64 fail (out of 204), 2 skipped (functional-syntax-only) | `pe-fresh2.log` / `cons-fresh.log`, rerun this session |
| type-inconsistency | 124 pass, 3 fail (out of 127), 1 skipped (semantics-scope) | `semdir-fresh.log`, rerun this session |
| type-negative-entailment (standalone catalog) | 23 pass, 0 fail (out of 23) | committed `owl_type_negative_entailment_results.log` |
| type-negative-entailment (NE section inside type-positive-entailment.rdf catalog run) | 22 pass, 1 fail (out of 23) — WebOnt-imports-002 | `cons-fresh.log` |
| type-consistency | 352 pass, 0 fail (out of 352), 2 skipped (functional-syntax-only) | `cons-fresh.log` |
| syntax-dl (species classifier: DL vs FULL) | 319 pass, 2 fail (out of 321), 2 skipped | committed `owl_syntax_dl_results.log` |

### Profile suites — the numbers handed into this task were stale; corrected below

`docs/test-results/latest.json` timestamps itself `2026-07-28 06:30 UTC`. The
`OWL.Closure.fsti` module was last edited `2026-07-28 09:53 UTC` and
re-extracted to `OWL_Closure.ml` at `10:02 UTC`; the committed
`bin/linux-x86_64/owl_runner` binary is from `14:03 UTC` (committed
`14:50 UTC`) — all **after** `latest.json` was generated. Rerunning the
profile catalogs against the current binary this session:

| Suite | Task-provided (stale, 06:30 UTC) | Rerun this session (current binary) |
|---|---|---|
| owl2_profile_el | 108 pass, 12 fail (out of 120) | **118 pass, 2 fail (out of 120), 1 skipped** |
| owl2_profile_ql | 83 pass, 4 fail (out of 87) | **85 pass, 2 fail (out of 87)** |
| owl_rl_positive_entailment (profile-RL.rdf, PE section) | 28 pass, 2 fail (out of 30) | 28 pass, 2 fail (out of 30) — unchanged, this one was accurate |

🧭 Ten tests that were reported failing (`New-Feature-SelfRestriction-001/002`,
`New-Feature-BottomDataProperty-001`, `New-Feature-BottomObjectProperty-001`,
`WebOnt-Restriction-001/002`, `WebOnt-disjointWith-001`,
`WebOnt-miscellaneous-302-Direct`, `bnode2somevaluesfrom`,
`somevaluesfrom2bnode`) now pass under the current binary — apparently fixed
by today's `OWL.Closure.fsti` edit before this task started. **Action:
regenerate `docs/test-results/latest.json` and the committed
`owl_profile_el_results.log` / `owl_profile_ql_results.log`** (site-and-dashboard
skill) so the dashboard stops under-reporting. The only profile-suite fails
remaining anywhere are `WebOnt-I5.26-010` and `WebOnt-I5.5-005`, both already
covered under Group C below.

## 2. Failure taxonomy — the 64 type-positive-entailment fails

64 fails, grouped by what actually has to change to fix them. Group letters
carry into §4's action list.

### Group A — missing OWL/RDFS vocabulary axiomatic triples (12 tests, LOW effort)

Built-in RDF/RDFS/OWL vocabulary terms that the RDF-Based semantics declares
with a fixed type/domain/range, and our closure never asserts. Confirmed by
reading `rdfbased-sem-prop-label-type`'s fixture: premise is an **empty**
graph; conclusion is exactly `rdfs:label rdf:type owl:AnnotationProperty`.
Same shape for the other 8 `rdfbased-sem-prop-*-type` tests (rdfs:comment,
owl:deprecated, rdfs:seeAlso, rdfs:isDefinedBy, owl:backwardCompatibleWith,
owl:incompatibleWith, owl:priorVersion, owl:versionInfo — all typed
`owl:AnnotationProperty`), for `WebOnt-imports-010` (`owl:imports rdfs:domain
owl:Ontology ; rdfs:range owl:Ontology`), and for `WebOnt-I5.5-001`/`-002`
(`rdf:first`/`rdf:rest rdf:type owl:FunctionalProperty`).

Tests: `rdfbased-sem-prop-backwardcompatiblewith-type-annot`,
`rdfbased-sem-prop-comment-type`, `rdfbased-sem-prop-deprecated-type`,
`rdfbased-sem-prop-incompatiblewith-type-annot`,
`rdfbased-sem-prop-isdefinedby-type`, `rdfbased-sem-prop-label-type`,
`rdfbased-sem-prop-priorversion-type-annot`,
`rdfbased-sem-prop-seealso-type`, `rdfbased-sem-prop-versioninfo-type`,
`WebOnt-imports-010`, `WebOnt-I5.5-001`, `WebOnt-I5.5-002`.

Fix: a static axiom table in `OWL.Closure.fst`/`.fsti` — a fixed list of
`(iri, type/domain/range triple)` facts unconditionally added to every
closure (no algorithm, no traversal). Closure-rule work, F*-first.

### Group B — RDFS domain/range propagation through subPropertyOf (2 tests, LOW effort)

`rdfbased-sem-rdfsext-domain-subprop`: premise is `p1 rdfs:subPropertyOf p2 .
p2 rdfs:domain c .`; conclusion is `p1 rdfs:domain c .` — i.e. domain (and
symmetrically range) must propagate down a subPropertyOf chain, which plain
rdfs2/rdfs3 does not give you without also combining subPropertyOf
transitivity.

Tests: `rdfbased-sem-rdfsext-domain-subprop`, `rdfbased-sem-rdfsext-range-subprop`.

Fix: one closure rule in `OWL.Closure.fst`: `p1 subPropertyOf p2, p2 domain/range
c ⟹ p1 domain/range c`. (Contrast with the already-passing
`rdfbased-sem-rdfsext-domain-superclass`/`range-superclass`, which is the
dual "domain c, c subClassOf d ⟹ domain d" rule — already implemented per
`cons-fresh.log`'s PASS list.)

### Group C — comprehension-principle entailments: oneOf/unionOf/enum, incl. floating class expressions (9 tests, LOW-MEDIUM effort)

`WebOnt-oneOf-002`: premise `TShirt owl:oneOf (small medium large)`;
conclusion `small rdf:type TShirt` — enumerated-class membership, the classic
missing rule. Confirmed via direct read: `OWL.Closure.fsti` recognizes
`owl_oneOf_iri` and `owl_unionOf_iri` **only** inside the
`is_owl_construct_iri` predicate (lines 1094/1096) — there is no forward
comprehension rule anywhere else in the file. `rdfbased-sem-enum-inst-included`
is the same rule under a different name. `WebOnt-unionOf-003`/`004` are the
union analogue. `New-Feature-DisjointUnion-001` is `owl:disjointUnionOf` =
unionOf comprehension + pairwise disjointness on the same list.
`WebOnt-I5.5-005` and `WebOnt-I5.26-010` are the same rule family applied to
a **floating** (unreferenced) class expression — the conclusion is just the
bnode-shaped triples of an anonymous `owl:unionOf`/`owl:Restriction`
declaring itself, which RDF-Based (OWL Full) comprehension entails "for
free" once its structural parts (a property, a class) are declared, even
though it never appears in an axiom. `WebOnt-I5.5-005` is also one of the
2 `syntax-dl` species fails (see §3) — same underlying rdf:List shape trips
both the closure rule and the DL-species checker, so fixing the list
traversal likely closes both at once.

Tests: `WebOnt-oneOf-002`, `WebOnt-oneOf-003`, `WebOnt-oneOf-004`,
`WebOnt-unionOf-003`, `WebOnt-unionOf-004`, `rdfbased-sem-enum-inst-included`,
`New-Feature-DisjointUnion-001`, `WebOnt-I5.5-005`, `WebOnt-I5.26-010`.

Fix: new closure rules in `OWL.Closure.fst`, sibling to the existing
`owl_rule_cls_int1` (intersectionOf decomposition, x∈C ⟹ x∈Ci) — `cls-oneof`
(each list member ⟹ member of the oneOf class) and `cls-uni` (member of any
disjunct ⟹ member of the union class), both walking the same `decode_iri_list`
list-traversal helper `cls-int1` already uses. `disjointUnionOf` layers a
pairwise-disjoint emission on top once `cls-uni` exists.

### Group D — cardinality reasoning (4 tests, MEDIUM effort)

`WebOnt-cardinality-001`: premise `c ⊑ Restriction(p, maxCardinality 1) ⊓
Restriction(p, minCardinality 1)`; conclusion is the same — a
`test:ProfileIdentificationTest` demonstrating `owl:cardinality N` is
shorthand for the min/max pair. `rdfbased-sem-restrict-maxqcr-inst-obj-one`:
premise has `w` with two `p`-edges to `x1`,`x2`, both typed `c`, and `z ⊑
maxQualifiedCardinality(p, c, 1)`; conclusion is `x1 owl:sameAs x2`. That
needs an equality-merge derivation, not just membership propagation — same
territory `OWL.QueryRewrite.fst`'s `CE_MaxCardinality` anchor rewrite already
works around on the query side (issue #236) but this test needs the actual
`owl:sameAs` triple materialized by closure, not rewritten around at query
time.

Tests: `WebOnt-cardinality-001`, `WebOnt-cardinality-003`,
`WebOnt-cardinality-006`, `rdfbased-sem-restrict-maxqcr-inst-obj-one`.

Fix: `owl:cardinality` ⟹ min+max pair is a trivial closure rule
(cardinality-001/003; -006 additionally needs Group C's intersectionOf
interaction, already partially present via `cls-int1`). The max-QCR→sameAs
rule (`cls-maxqc1`'s equality-forcing form) is real semantic work in
`OWL.Closure.fst` — flag per rule #11: this must derive the `owl:sameAs`
triple in F*-verified closure, not be patched in as OCaml-side
runner logic, and must not be conflated with #236's query-rewrite anchor
(different mechanism, different bug).

### Group E — property-characteristic propagation axioms (9 tests, MEDIUM effort)

`WebOnt-FunctionalProperty-003`: premise `prop owl:FunctionalProperty ;
owl:inverseOf inv`; conclusion `inv rdf:type owl:InverseFunctionalProperty` —
Functional + inverseOf ⟹ the inverse is InverseFunctional (and vice-versa for
`-004`). `WebOnt-complementOf-001`: premise `A owl:complementOf B`;
conclusion `B owl:complementOf A` — complementOf is symmetric.
`WebOnt-I5.21-002`: premise spells out `owl:disjointWith` only in one
direction across an 11-class clique (each class lists disjointWith for
classes not yet seen); conclusion requires the **full** symmetric closure
(every pair, both directions) — i.e. `owl:disjointWith` is symmetric, same
rule family as complementOf. `WebOnt-equivalentProperty-004`/`-005`:
equivalentProperty must propagate property characteristics (Functional/
InverseFunctional/Symmetric/Transitive) between the two equivalent
properties, not just domain/range. `WebOnt-SymmetricProperty-002` combines
symmetric-property extensional semantics with an oneOf-based domain
(overlaps Group C's list machinery).

Tests: `WebOnt-FunctionalProperty-003`, `WebOnt-FunctionalProperty-004`,
`WebOnt-InverseFunctionalProperty-003`, `WebOnt-InverseFunctionalProperty-004`,
`WebOnt-SymmetricProperty-002`, `WebOnt-complementOf-001`,
`WebOnt-equivalentProperty-004`, `WebOnt-equivalentProperty-005`,
`WebOnt-I5.21-002`.

Fix: a small family of independent axiom-propagation rules in
`OWL.Closure.fst` (each is a few lines: symmetric-predicate rules for
`complementOf`/`disjointWith`, an inverseOf/Functional cross rule, and
equivalentProperty characteristic-copying). Split into 2-3 commits by
sub-family rather than one; each is independently testable.

### Group F — AllDifferent / distinctMembers forward comprehension (3 tests, LOW effort)

`WebOnt-differentFrom-002`: premise is `owl:AllDifferent` with
`owl:distinctMembers (Fred Wilma Barney Betty)` (4 members); conclusion is
`Barney owl:differentFrom Wilma`. Confirmed by reading `OWL.Closure.fsti`:
`distinctMembers` is recognized only as a construct IRI (line 1100); the only
AllDifferent-related rule present, `owl_rule_differentFrom_to_allDifferent`
(~line 3494), runs the **opposite** direction — it synthesizes a canonical
2-member `AllDifferent` scaffold FROM existing `differentFrom` pairs, for
other rules to consume (targets `New-Feature-DisjointObjectProperties-002`
per its own comment). The forward direction these 3 tests need — walk an
`owl:AllDifferent`'s `distinctMembers`/`members` list and emit the full
N-choose-2 pairwise `differentFrom` closure — does not exist.

Tests: `WebOnt-AllDifferent-001`, `WebOnt-differentFrom-002`,
`WebOnt-distinctMembers-001`.

Fix: new closure rule in `OWL.Closure.fst`, `cls-differentFrom` (forward):
decode an AllDifferent node's member list (reuse the same list-decoder as
Group C/F's list handling) and emit every pairwise `differentFrom`. Same
shape as the existing reverse rule, just the other direction — should sit
right next to it with a shared list-decode helper.

### Group G — OWL Full meta-modeling axioms, DL explicitly excluded (3 tests, PARK — see 🧭)

`WebOnt-Class-001`: premise is **empty**; conclusion is `rdfs:Class
owl:equivalentClass owl:Class` — a meta-model axiom that only holds under
OWL Full's comprehension over the RDFS/OWL vocabulary itself. All three
tests carry `test:species FULL` only, with an explicit
`owl:NegativePropertyAssertion` denying `test:species DL` for each — the W3C
suite itself says these are OWL-Full-only, not OWL DL entailments.

Tests: `WebOnt-Class-001`, `WebOnt-Class-002`, `WebOnt-Class-003`.

Recommendation: park. Implementing bespoke Full meta-axioms for 3 tests when
the project's stated target is RDF Core / RDFS / OWL(DL+RL/EL/QL profiles) /
SHACL / SPARQL is a poor tests-gained/effort trade unless OWL Full punning
becomes an explicit goal.

### Group H — hard DL98-style tableau stress tests (9 tests, HIGH effort)

`WebOnt-description-logic-201`: "ABox test from DL98 systems comparison" —
premise is a large TBox/ABox (dozens of named classes, restrictions,
disjointness) whose conclusion lists ~10+ `rdf:type` assertions for one
individual, only derivable via full classification (intersection/union/
cardinality/disjointness interaction at scale, not a single closure rule).
`description-logic-202/206/208/661/662/901/903` share the same DL98-corpus
shape (confirmed by shared `test:creator Sean Bechhofer` /
`test:description "DL Test:"` pattern — not each fixture individually read).
`Consistent-but-all-unsat`: "An ontology that is consistent, but all named
classes are unsatisfiable" — a deliberately adversarial OWL 2 stress case
(nominal + cardinality + disjointness interplay), read in full.

Tests: `WebOnt-description-logic-201`, `-202`, `-206`, `-208`, `-661`, `-662`,
`-901`, `-903`, `Consistent-but-all-unsat`.

Fix: real tableau classification in `Tableau.fst`/`Tableau.Refute.fst` (the
module already exists but per its own header is a skeleton — see
`OWL.Closure.fsti`'s comment at ~4451: "the tableau currently returns None
for everything non-trivial"). Not commit-sized; this is the long pole of
the DL-species reasoning work, tracked separately from the closure-rule
items above.

### Group J — cardinality/complement/range-intersection interplay (5 tests, MEDIUM-HIGH effort)

`WebOnt-I5.2-004`: premise defines an unsatisfiable `Nothing` class via
combined min/max cardinality on the same property, then derives
`notA owl:complementOf A` from it — genuine interaction between cardinality
unsatisfiability and complement construction, not a single rule.
`WebOnt-I5.24-002`: "OWL, unlike RDFS, uses iff semantics for range" —
premise `prop rdfs:range A`, `A rdfs:subClassOf B`; conclusion involves an
`owl:intersectionOf` built from the range class — combines Group B/C-style
list/range reasoning with the OWL-specific range-iff quirk.
`WebOnt-I5.2-006`, `WebOnt-I5.24-003`, `-004` share the same
`test:creator`/pattern family (not each individually read).

Tests: `WebOnt-I5.2-004`, `WebOnt-I5.2-006`, `WebOnt-I5.24-002`,
`WebOnt-I5.24-003`, `WebOnt-I5.24-004`.

Fix: likely `Tableau.fst` territory (cardinality+complement interaction) for
I5.2-004/006; I5.24-x may be closable with a targeted `OWL.Closure.fst` rule
once someone reads the -003/-004 fixtures directly — flagged here as
needing that read before scoping a commit.

### Group K — Extracredit-status combinatorial/datatype-facet tests (6 tests, HIGH effort, LOW priority)

`WebOnt-I5.8-004`: `test:status test;Extracredit` — "There are precisely 128
different values of xsd:byte that are also xsd:unsignedInt" — exact
datatype-facet interval counting. The W3C suite itself marks these as bonus,
not required, tests. `-010`/`-017` share the `Extracredit` status (not
individually read). `WebOnt-extra-credit-002/003/004` — same status by
name.

Tests: `WebOnt-I5.8-004`, `WebOnt-I5.8-010`, `WebOnt-I5.8-017`,
`WebOnt-extra-credit-002`, `WebOnt-extra-credit-003`, `WebOnt-extra-credit-004`.

Fix: datatype value-space facet reasoning (byte ∩ unsignedInt cardinality,
etc.) — real work, low return given `Extracredit` status. Deprioritize
below every other group.

### Group L — RDFS-compatible-semantics-for-OWL corner cases (2 tests, MEDIUM-HIGH effort, LOW priority)

`WebOnt-I5.3-014`/`-015`: both self-describe in `test:description` as "This
entailment does not hold under the RDF Semantics, but does under the RDFS
Compatible Semantics for OWL" — Herman ter Horst-authored edge cases in how
`rdf:type`'s own domain/range and subPropertyOf interact with class-hood.
Niche, isolated axioms; not part of any broader missing-rule family found
elsewhere in this taxonomy.

Tests: `WebOnt-I5.3-014`, `WebOnt-I5.3-015`.

## 3. Other suites — briefer

### 3 type-inconsistency fails

- `Minus Infinity is not in owl:real` — datatype value-space/facet reasoning
  (owl:real excludes -INF; needs numeric-datatype interval handling). Read
  in full: functional-syntax premise combines `DataAllValuesFrom(dp
  owl:real)`, `DataSomeValuesFrom(dp DataOneOf("-INF"^^xsd:float
  "-0"^^xsd:integer))`, and a `NegativeDataPropertyAssertion(dp a
  "0"^^xsd:unsignedInt)`. Datatype-facet work, MEDIUM-HIGH effort.
- `WebOnt-description-logic-502` — "the classic 3-SAT problem" encoded via
  nested `owl:oneOf`/`owl:differentFrom` pairs. Read in full: genuine
  worst-case combinatorial tableau reasoning. HIGH effort, low priority
  (deliberately adversarial by design).
- `WebOnt-description-logic-909` — integer multiplication via chained
  `owl:FunctionalProperty`/`owl:inverseOf` cardinality arithmetic. Read in
  full: another deliberately adversarial DL98 stress test. HIGH effort, low
  priority.

Both DL98 fails belong with Group H's family (same tableau gap); the
owl:real fail is standalone datatype-facet work.

### 2 syntax-dl species fails

Committed `owl_syntax_dl_results.log`:
`FAIL: FS2RDF-literals-ar [species] verdict=FULL expected=DL` and
`FAIL: WebOnt-I5.5-005 [species] verdict=FULL expected=DL`.

- `WebOnt-I5.5-005`: same test as Group C above — the species checker
  (`OWL2.SyntaxDL.fst`) misclassifies the floating-unionOf-over-raw-rdf:List
  shape as OWL Full. Likely fixed by the same list-traversal work as Group C.
- `FS2RDF-literals-ar`: read the premise in full — it combines (a) every XSD
  datatype spelled in lowercase (`xsd:unsignedint`, `xsd:anyuri`, etc.), (b)
  `owl:rational`, and (c) an `rdf:XMLLiteral` value containing a **fully
  nested** `<rdf:RDF>...</rdf:RDF>` document, plus (d) an `owl:Axiom`
  reification annotating an `rdf:type` triple. Root cause not isolated this
  session — any of (b)/(c)/(d) is a plausible trigger for the DL-species
  checker's FULL verdict. Next step for whoever picks this up: bisect the
  premise into three sub-ontologies (datatype-battery only / XMLLiteral-only
  / owl:Axiom-only) run through `owl_runner --species` to isolate before
  touching `OWL2.SyntaxDL.fst`.

### WebOnt-imports-002 (NE fail) — runner/catalog plumbing, not F* semantics

This `NegativeEntailmentTest` exists specifically to check that a reasoner
must **not** treat a term from an unimported namespace as pulling in that
namespace's axioms. Read `bin/owl-runner/owl_runner.ml`'s
`load_imports_into_premise` (~line 1132): it merges every
`test:importedOntology` catalog link into the premise **unconditionally**,
regardless of whether the premise graph itself contains an `owl:imports`
triple pointing at that IRI. For this one test, that blanket merge is wrong
— the premise ontology never declares `owl:imports`, so nothing should be
pulled in, but the runner pulls it in anyway and the closure over-derives.

Fix location: `bin/owl-runner/owl_runner.ml`,
`load_imports_into_premise`/its caller. Gate the merge on the premise graph
actually containing `<premise-ontology-IRI> owl:imports <import_iri>` before
calling `parse_import_cached`. ⚠️ This is catalog/fixture-assembly plumbing
(deciding which document to hand to the closure), not new entailment logic
— the check itself is a syntactic "does this graph contain this triple"
lookup, not reasoning, so it stays inside rule #11's I/O-glue allowance. Do
**not** let this turn into conditional semantics living in the runner;
if the fix needs anything beyond a plain triple-membership check, it
belongs in F* instead.

### Profile EL/QL fails

Per §1, current binary shows only `WebOnt-I5.26-010` and `WebOnt-I5.5-005`
failing across EL, QL, and RL profile PE sections — both already covered by
Group C. No profile-specific closure gap remains once `docs/test-results/
latest.json` is regenerated.

## 4. Prioritized action list

Ordered by (tests gained) / (estimated effort), one commit-sized item each.

1. **Regenerate `docs/test-results/latest.json` + committed
   `owl_profile_el_results.log`/`owl_profile_ql_results.log`.** Zero code
   change — 10 tests already fixed are being under-reported. (site-and-
   dashboard skill.)
2. **Group A — vocabulary axiomatic-triple table.** `OWL.Closure.fst`/`.fsti`:
   add the fixed `(iri, triple)` list for `rdfs:label`/`comment`/
   `isDefinedBy`/`seeAlso`, `owl:deprecated`/`versionInfo`/
   `backwardCompatibleWith`/`incompatibleWith` (all → AnnotationProperty),
   `owl:imports` (domain/range Ontology), `rdf:first`/`rdf:rest` (→
   FunctionalProperty). Pure data, no algorithm. **12 tests, lowest effort
   in the list.**
3. **Group C — `cls-oneof`/`cls-uni` comprehension rules.** `OWL.Closure.fst`,
   sibling to existing `owl_rule_cls_int1`; reuse `decode_iri_list` (used
   for individuals here, not just class IRIs — check the decoder's type
   contract before reusing wholesale). **9 tests, also fixes 1 of the 2
   syntax-dl species fails.**
4. **Group F — `cls-differentFrom` forward AllDifferent/distinctMembers
   rule.** `OWL.Closure.fst`, mirrors the existing reverse rule
   `owl_rule_differentFrom_to_allDifferent` at ~line 3494 but walks
   distinctMembers→pairwise differentFrom instead of the other way. **3
   tests, low effort.**
5. **Group B — rdfsext domain/range-through-subPropertyOf rule.**
   `OWL.Closure.fst`, dual of the already-passing domain/range-through-
   subClassOf rule. **2 tests, low effort.**
6. **WebOnt-imports-002 runner fix.** `bin/owl-runner/owl_runner.ml`: gate
   `load_imports_into_premise` on an actual `owl:imports` triple in the
   premise. **1 test (NE), low effort, plumbing only — no F* change.**
7. **Group E — property-characteristic propagation family, split into 2-3
   commits:** (a) symmetric-predicate rules for `complementOf`/
   `disjointWith`; (b) Functional↔InverseFunctional-via-inverseOf; (c)
   equivalentProperty characteristic-copying. `OWL.Closure.fst`. **9 tests,
   medium effort — do not land as one commit, each sub-rule is
   independently testable.**
8. **Group D — cardinality shorthand + max-QCR→sameAs.** Split: (a)
   `owl:cardinality` → min+max pair is trivial (2 tests); (b) max-QCR
   equality-forcing rule needs real closure-side equality derivation (2
   tests) — **do this in `OWL.Closure.fst`, not as a QueryRewrite-side
   anchor; keep it clearly separate from issue #236's query-rewrite hack**,
   since #236 explicitly narrows to a query-time workaround and this needs
   the actual triple materialized.
9. **FS2RDF-literals-ar bisection.** Before touching `OWL2.SyntaxDL.fst`,
   split the premise into 3 sub-ontologies and rerun `owl_runner --species`
   on each to find which of {lowercase-datatype battery, nested
   XMLLiteral, owl:Axiom reification} trips the FULL verdict. **1 test,
   effort unknown until bisected — do the bisection as its own
   (non-code) diagnostic step first.**
10. **Group J — I5.2/I5.24 cardinality+complement+range interplay.** Read
    the 3 not-yet-read fixtures (`I5.2-006`, `I5.24-003`, `I5.24-004`)
    before scoping; likely split between `Tableau.fst` (I5.2-x) and
    `OWL.Closure.fst` (I5.24-x). **5 tests, medium-high effort.**
11. **Group H / DL98 + `Consistent-but-all-unsat` + `description-logic-502`/
    `-909`.** Real tableau classification work in `Tableau.fst`/
    `Tableau.Refute.fst`, which is currently a documented skeleton. **11
    tests total (9 PE + 2 inconsistency), highest effort — this is the
    long pole, track as its own multi-session program, not a commit-sized
    item.**
12. **Group K — Extracredit datatype-facet tests.** Deprioritize; W3C marks
    these as bonus. **6 tests, high effort, lowest priority.**
13. **Group L — I5.3-014/015 RDFS-compatible-semantics corner cases.**
    Niche, isolated axioms with no broader payoff. **2 tests, lowest
    priority alongside Group G.**
14. **Group G — OWL Full meta-modeling axioms.** Park (see 🧭 below). **3
    tests, not recommended unless OWL Full becomes an explicit goal.**

## 5. Open questions for the owner

🧭 **Is OWL Full punning/meta-modeling (Group G, 3 tests: `WebOnt-Class-001/
002/003`) in scope at all?** The W3C suite itself marks these DL-excluded
(FULL-only). Confirming "no" lets item 14 be closed as won't-fix rather than
carried as an open gap.

🧭 **Is the `Tableau.fst`/`Tableau.Refute.fst` skeleton (Group H, 9 PE +
2 inconsistency = 11 tests, the DL98 stress corpus) a near-term priority, or
should the next several sessions focus on the closure-rule items (1-8 above,
~38 tests) first and leave real tableau classification for a dedicated
multi-session push?** The closure-rule items are individually commit-sized;
the tableau work is not.

🧭 **`docs/test-results/latest.json` under-reports 10 already-fixed tests
right now** (§1) — confirming this is worth an immediate regen (item 1)
before any further OWL work, so nobody re-investigates tests that already
pass.
