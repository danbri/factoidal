# The F\* OWL engine, audited for soundness and for its proved boundary

2026-09-07. Worktree `wt/fstar-owl-audit` on `db2812b28`. Engine:
`formal/fstar` (`bin/darwin-arm64/owl_runner`). Differential oracle:
`formal/lean4` as recorded in
[`2026-09-07-lean-owl-corpus-gap.md`](2026-09-07-lean-owl-corpus-gap.md).

Owner question, 2026-09-07, verbatim: "F\* rule is unsound - should we
do a deeper investigation into whether we managed to fuck up the F\*
version?"

## 0. The answer, before the detail

One rule was unsound and is deleted. One inconsistency check was unsound
and is repaired. Neither moves a published catalog score. The
measurement that matters is not those two, it is the boundary they came
from: **82 closure rules, 24 of them carrying a proof, 58 not.** All 24
are OWL 2 RL table rows. **Not one of the 45 named extensions has a
licensing lemma**, and only four have a truth-preservation lemma. The
two defects were both found in the unproved 45, by a second
implementation rather than by anything in this tree.

## 1. Rule inventory

Source: the 82 `owl_rule_*` functions in `formal/fstar/OWL.Closure.fsti`,
their class from the engine ledger in `formal/fstar/OWL.RL.Spec.fst`
(Landing 4), and the two proof registries — `val owl_rule_*_licensed`
in `formal/fstar/OWL.RL.Refinement.fst` (every emission is licensed by
the transcribed table row) and `val owl_rule_*_sound` in
`formal/fstar/OWL.Semantics.Soundness.fst` (every emission is true in
every model of the input).

Classes, per the ledger's own legend: `[row]` implements a named row of
the OWL 2 RL/RDF rule table
(<https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules>);
`[ext]` is a named extension beyond the table; `[axm]` materialises an
axiomatic-triple table; `[mode]` fires only under a catalog semantics
mode.

| class | rules | licensing lemma | truth-preservation lemma | neither |
|---|---:|---:|---:|---:|
| `[row]` OWL 2 RL table row | 33 | 20 | 20 | 13 |
| `[ext]` extension | 45 | **0** | 4 | 41 |
| `[axm]` axiomatic triples | 3 | 0 | 0 | 3 |
| `[mode]` semantics-mode gated | 1 | 0 | 0 | 1 |
| **total** | **82** | **20** | **24** | **58** |

The 20 with both lemmas: `equivalent_class`, `equivalent_property`,
`scm_eqc2`, `scm_eqp2`, `scm_dom2`, `scm_rng2`, `subprop_domain_range`,
`symmetric_property`, `transitive_property`, `inverse_of`, `functional`,
`inverse_functional`, `property_chain_2`, `prp_key`, `cls_hv1`,
`cls_hv2`, `cls_avf1`, `cls_int1`, `cls_oneof`, `cls_uni`. Four more
carry truth-preservation only: `chain_to_transitive`,
`disjoint_with_propagation`, `scm_cls_restriction`,
`symmetric_metapredicates`.

The RDFS rows the OWL-RL fixpoint interleaves (rdfs2/3/5/7/9/11, i.e.
prp-dom, prp-rng, scm-spo, prp-spo1, cax-sco, scm-sco) come from
`RDFS.Closure` and are licensed separately in
`RDF.Entailment.RDFS.Refinement`; they are not counted above.

### 1a. What "extension" covers, and what licenses it

The ledger's `[ext]` tag promises that each extension's justification
"has a stated home" — the rule's own banner comment. That is a prose
argument, not a lemma. Reading them, they fall into four groups.

1. **Contrapositives of RL clash rows** (11 rules):
   `pdw_to_differentFrom`, `pdw_shared_value_to_differentFrom`,
   `fp_diff_to_diff`, `ifp_diff_to_diff`, `cax_dw_to_differentFrom`,
   `differentFrom_symmetry`, `allDifferent_to_differentFrom`,
   `differentFrom_to_allDifferent`, `disjoint_to_complement`,
   `inverseOf_domain_range_flip`, `named_sameAs_to_equivClass`. The RL
   table states these conditions as CLASHES with no consequent; the
   engine derives their contrapositive as a fact. Each banner argues the
   model-theoretic step. These are the most defensible of the 45 and the
   easiest to close with lemmas.
2. **The comprehension and existential-witness layer** (11 rules):
   `cls_hasself2_synth`, `cls_svf_thing_materialize`,
   `cls_svf_thing_witness`, and the eight `comp_*` rules. Cited to OWL 2
   RDF-Based Semantics section 8.2's comprehension conditions
   (<https://www.w3.org/TR/owl2-rdf-based-semantics/>). Section 3 below.
3. **Cardinality and restriction decompositions** (about 10 rules):
   `cardinality_to_min_max`, `cls_exactqc1`, `cls_maxqc_comp`,
   `cls_minc_qual1`, `cls_svf2_qualified`, `minc1_bridge`,
   `svf2_existential_witness`, `hasvalue_card_disjoint`,
   `singleton_nominal_functionality`, `fp_pinned_subproperty`. Several
   of these carry known narrowness — `cls_maxqc_comp` is the #236
   anchor rewrite CLAUDE.md already flags as sound-but-narrow.
4. **Characteristic and vocabulary transfers** (the rest):
   `inverse_characteristics`, `equivalent_property_characteristics`,
   `reflexive_property`, `oneof_set_equivalence`, `cls_uni_elim`,
   `avf_thing_to_range`, `extensional_symmetry`, `dt_range_intersect`,
   `transitive_to_chain`, `scm_cls_restriction`.

### 1b. Rules whose ledger class was already known to be wrong

The ledger records five `[row]` claims that a 2026-08-05 licensing pass
corrected against the actual table: `cls_int1` implements cls-int2,
`cls_uni` implements scm-uni (and its `owl:disjointUnionOf` branch is an
unlabelled extension on top), `scm_dom2` implements scm-dom1, `scm_rng2`
implements scm-rng1. Those corrections came out of writing the licensing
lemmas — which is the argument for writing the other 58.

### 1c. The clash checks

`is_inconsistent` has twelve checks. Ten are OWL 2 RL Table 8
no-consequent conditions. Two are extensions: (10) `dt-range-clash`
(section 4 below) and (11) the bottom-property existential clash. None
of the twelve has a lemma in either registry.

## 2. Differential against the Lean tree

The like-for-like comparison is recorded in
[`2026-09-07-lean-owl-corpus-gap.md`](2026-09-07-lean-owl-corpus-gap.md)
and is not re-run here; that record's method — profile catalogs Lean RL
against F\* RL, `type-*` catalogs Lean `--dl` against F\* DL — is the
one that avoids comparing two different procedures.

After the Lean landing of 2026-09-07 evening (commit `d61c18221`), the
three profile catalogs are **F\*-complete and Lean-complete on RL and
QL** (126 of 126, 87 of 87). The remaining directional differences:

**F\* passes, Lean fails — 2 units, 2 ids** (profile-EL only):

| id | why |
|---|---|
| `WebOnt-someValuesFrom-003` | F\*'s `svf2_existential_witness` is a depth-capped rule that chains a NAMED filler class to depth two; the Lean layer's `svf-thing-wit` covers the `owl:Thing` filler only. |
| `New-Feature-Keys-002` | Needs a `prp-key` + `owl:differentFrom` clash row that the Lean PE-only layer never sees, an InconsistencyTest being scored. |

Both are Lean gaps, not F\* defects.

**Lean passes, F\* fails:** on the profile catalogs, none — F\* scores
every unit. On `type-positive-entailment.rdf` the Lean `--dl` run beats
F\* on the ConsistencyTest section (204 pass, 0 fail against F\*'s 199
pass, 5 fail); F\*'s five are `unsupported` cap escapes
(<https://github.com/danbri/factoidal/issues/326>), not wrong verdicts.

**F\* passes where the Lean tree refused on soundness grounds — 3 units,
1 id.** `WebOnt-I4.6-005-Direct` (profile-RL, -EL, -QL). The Lean record
declines to port the rule that produced the F\* pass, with the argument
restated in section 3. This is the whole of the third list, and it is
the one that mattered.

## 3. Defect (a): `equivalentClass` does not entail `sameAs`. FIXED.

`OWL.Closure.fsti`'s `owl_rule_named_equivClass_to_sameAs_mode` emitted
`C owl:sameAs D` and `D owl:sameAs C` from `C owl:equivalentClass D`
whenever both were named classes and at least one carried some property
assertion beyond class-hood, under a `test:semantics=DIRECT` gate. Once
that identity existed, `eq-rep-s` copied every assertion about `C` onto
`D`.

**It is unsound under both semantics.** Under the Direct Semantics,
`EquivalentClasses(C D)` is the condition `(C)^C = (D)^C` on the two
class expressions' extensions
(<https://www.w3.org/TR/owl2-direct-semantics/>, Table 2), while
`SameIndividual(C D)` is `(C)^I = (D)^I` on their individual
interpretations; punning keeps the two readings of one IRI independent
(OWL 2 Structural Specification section 5.8), so coextension entails
nothing about identity. Under the RDF-Based Semantics,
`owl:equivalentClass` is the section 5.8 condition
`ICEXT(S(c)) = ICEXT(S(d))` and `owl:sameAs` is `S(c) = S(d)`
(<https://www.w3.org/TR/owl2-rdf-based-semantics/>); two distinct
resources may have equal class extensions in a model.

**The gate described what the rule avoided, not what licensed it.** The
DIRECT gate exists so that `WebOnt-I4.6-004` — an RDF-Based
NegativeEntailmentTest asserting that a bare `equivalentClass` must NOT
entail `sameAs` — keeps passing. A gate that names the test it must not
break is not a licence. The `has_extra_property` guard likewise: it
narrows the blast radius, it does not make the inference valid.

**How the ledger let it through.** `OWL.RL.Spec.fst` classified it
`[mode] converse, catalog-gated (owl_semantics_direct)`. Every other
class in that ledger — `[row]`, `[ext]`, `[axm]` — names a source of
authority. `[mode]` names a dispatch mechanism, and the rule was
admitted on that tag alone with no licence stated anywhere. This is the
lesson worth carrying: a ledger entry that records HOW a rule is
switched on, in a column meant to record WHY it is valid, is a hole
disguised as a row.

**The fix.** The two functions and the call site are deleted
(`OWL.Closure.fsti`), the ledger entry replaced with the removal note
and the counts corrected 84 → 82 (`OWL.RL.Spec.fst`). The sound
converse, `owl_rule_named_sameAs_to_equivClass`, is untouched.

**Keeping `WebOnt-I4.6-005-Direct` on a licensed route.**
`OWL.DirectMapping.Filter.fst` now recognises the nine built-in
annotation properties of Structural Specification section 5.5
(`rdfs:label`, `rdfs:comment`, `rdfs:seeAlso`, `rdfs:isDefinedBy`,
`owl:deprecated`, `owl:versionInfo`, `owl:backwardCompatibleWith`,
`owl:incompatibleWith`, `owl:priorVersion`), reusing
`OWL.Closure.owl_builtin_annotation_properties` rather than restating
it. That test's conclusion is exactly `C2 rdfs:comment "An example
class."`; under the Direct Semantics an AnnotationAssertion contributes
no condition to the interpretation, and the test's own
`test:description` says so. It passes because there is no logical
conclusion left to check, which is what the W3C fixture intends — the
same route the Lean tree took. The runner already gated this filter on
DIRECT-only `test:semantics`, so nothing reaches a test whose applicable
semantics includes the RDF-Based reading.

**Regression fixture:**
`tests/local/owl/equivalentclass_not_sameas.sh` — six checks: no
fabricated `sameAs` either way; the annotation not copied; the
non-annotation `dc:creator` not copied (the worse of the two, a
manufactured ordinary fact); the licensed `cls-eqc1` subClassOf pair
still derived; the sound converse still derived.

## 4. Defect (b): `dt-range-clash` decided disjointness by tree reachability. FIXED.

`is_inconsistent` check (10) reported an inconsistency when a property's
declared `rdfs:range` datatype was not reached from the asserted
literal's datatype in `xsd_hierarchy_edges`. Its banner justified this
by asserting that XSD value spaces are "identical, in a subtype
relation, or fully disjoint — never partially overlapping".

That premise is true of the PRIMITIVE types and false of the DERIVED
integer types the check is applied to. `xsd_hierarchy_edges` is a tree:
`xsd:int` and `xsd:nonNegativeInteger` both reach `xsd:integer` and
neither reaches the other, yet their value spaces overlap. So
`p rdfs:range xsd:nonNegativeInteger` with `x p "5"^^xsd:int` was
reported INCONSISTENT, and 5 is a non-negative integer (XSD 1.1
Datatypes section 3.4.20).

**The fix** states the disjointness instead of inferring it from
non-reachability. `xsd_value_space_family` puts each recognised datatype
in one of three families — character strings, booleans, numbers — which
XSD 1.1 Datatypes section 3.3 gives pairwise disjoint value spaces, and
every derived datatype's value space is a subset of its base's, so a
derived type stays in its base's family. `xsd_value_spaces_disjoint`
fires only across families. An unrecognised datatype yields no verdict.

This is WEAKER than the old check. A same-family pair — range
`xsd:negativeInteger` with a `xsd:positiveInteger` literal — is no
longer reported, because deciding it needs the literal's VALUE, which
this check does not compute. A withheld verdict is sound; the
over-firing was not. The check still fires on `string-integer-clash`,
the InconsistencyTest it was written for.

**Unit fixture:** `tests/unit/owl_dt_range_clash_unit.ml`, 12 pass,
0 fail (out of 12) — four cross-family pairs that must still clash,
five overlapping or identical pairs that must not (including the
`xsd:int` / `xsd:nonNegativeInteger` regression in both directions),
and three that pin the OLD predicate's behaviour. Those last three
matter for anti-pattern 28: `xsd_is_subtype` is still defined, so the
suite asserts directly that neither of the two overlapping datatypes
reaches the other — which is exactly what made the old check fire —
and that a genuine subtype pair does reach, so the tree is shown
correct as a subtype tree and wrong as a disjointness test. Without
them the suite would show only that the case passes now, not that it
ever failed.

## 5. Defect (c): the witness closure is in F\*, but unproved.

The claim under audit was that
`owl_rl_closure_with_reflexivity_and_witnesses` — the function every
`PositiveEntailmentTest` is scored through — might be OCaml, and so
anti-pattern 15.

**It is not.** It is defined at `OWL.Closure.fsti` line 6584 as
`owl_rl_closure_with_reflexivity_and_witnesses_mode`: the plain RL
closure, then `cls_hasself2_synth`, `cls_svf_thing_materialize`,
`cls_svf_thing_witness`, then the eight `comp_*` rules, then one plain
re-closure. `bin/owl-runner/owl_runner.ml`'s
`apply_closure_with_witnesses` only chooses BETWEEN F\* entry points and
handles regime staging, the 30-second per-stage cap and its fallbacks.
That is consumer-tool orchestration, not semantics. Rule 15 is not
violated and rule 11 is not violated.

**What IS true, and is the more useful finding.** All eleven of those
rules are `[ext]`, and all eleven are in the 58 with no lemma. They are
verified F\* — total, terminating, extracted rather than hand-written —
and that is a real property. It is not soundness. Nothing in the tree
states that a triple emitted by `comp_range_avf` is true in every model
of the input, and no test can establish it: the corpus can only show
that no PREMISE ASSERTED CONSISTENT was refuted, which is
`type-consistency.rdf`'s job and is a much weaker statement than
truth-preservation.

The layer is deliberately kept off the shared fixpoint. The banner
records why, measured: folding it in took DL-regime
`type-inconsistency.rdf` from 124 pass, 3 fail to 63 pass, 64 fail. It
is applied only to the `PositiveEntailmentTest` path and never to the
consistency paths. That containment is what keeps the unproved layer
from deciding a consistency verdict — a good design, arrived at from a
score regression rather than from an argument.

**Consequence for how the score is described.** The F\*
`PositiveEntailmentTest` figures for every catalog rest on eleven
unproved derivation rules plus the tableau materialisation. They should
not be reported as verified entailments. Sections 6 and 7 say what may
be.

## 6. Scores, before and after

Reference: the committed serial logs in
`formal/fstar/ocaml-output/owl_*_results.log`, which are the project's
published numbers. Before/after pairs were measured in this worktree
with the pre-fix and post-fix `bin/darwin-arm64/owl_runner`.

| catalog / unit | committed (serial) | before (this worktree) | after (this worktree) |
|---|---|---|---|
| `profile-RL` PE / NE / Cons / Inc | 30 / 6 / 76 / 14, 0 fail each | same | **same** |
| `profile-QL` PE / NE / Cons / Inc | 20 / 3 / 58 / 6, 0 fail each | same | **same** |
| `profile-EL` PE / NE / Cons / Inc | 29 / 6 / 71+1 fail / 13, 1 skip | same | **same** |
| `type-inconsistency` Inc | 126 pass, 1 fail (of 127) | 125 pass, 2 fail | **125 pass, 2 fail** |
| `type-negative-entailment` NE / Cons | 23 pass 0 fail; 22 pass 1 fail | same | **same** |

**No score moved.** Removing an unsound rule that costs nothing is the
good case: the two tests it was scoring
(`WebOnt-I4.6-005-Direct`, `WebOnt-equivalentClass-008-Direct`) still
PASS on the annotation-filter route, `WebOnt-I4.6-004` still PASSes as
a NegativeEntailmentTest, and `string-integer-clash` still fires as an
InconsistencyTest. Verified per-test in the before and after logs.

**A measurement caveat, stated because it changed a number.** The
`type-inconsistency` figure reads 125 pass, 2 fail here against the
committed 126 pass, 1 fail. That difference is NOT the fix: it is
identical in the before and after runs, and it comes from running
catalogs in parallel. `owl_runner` puts a 30-second SIGALRM cap on each
test's closure and falls back on a trip, so a catalog measured under
load loses tests at the cap boundary that a serial run keeps. Any
before/after pair from this suite must be measured under the same
concurrency, and a figure from a loaded machine must not be compared
with a committed serial one. The three profile catalogs are far below
the cap and are unaffected.

## 7. Verdict

The two defects are real and are fixed, and neither was costing a test
— which is the least interesting fact in this record. What the audit
found is the shape of the trust surface. **Of the 82 rules the F\* OWL
closure applies, 24 carry a machine-checked statement of why they are
allowed to fire: 20 with both a licensing lemma against the transcribed
OWL 2 RL table and a truth-preservation lemma against the model theory,
4 with truth-preservation only. The other 58 carry a prose banner.** The
proved 24 are, with four exceptions, exactly the RL table rows; **not one
of the 45 named extensions has a licensing lemma**, and the eleven-rule
comprehension and existential-witness layer that every
`PositiveEntailmentTest` score is computed through is entirely inside
the unproved 45. Both defects found this week were in that 45, and both
were found by a second implementation rather than by any check in this
tree — the corpus cannot see them, because a corpus can only show that
no premise asserted consistent was refuted, which is much weaker than
truth-preservation, and because neither defect's wrong arm is exercised
by a W3C fixture at all. So the correct description of the F\* OWL
result is: the RL table rows are verified F\* and, for 20 of 33, proved
sound and proved to implement the row they claim; everything the engine
does beyond the table is verified F\* — total, terminating, extracted,
not hand-written — and unproved, and that includes the layer the
headline entailment numbers depend on. The engine's own containment
discipline is what has kept the unproved layer honest so far: it is
applied to the PositiveEntailment path only and never to a consistency
verdict, a separation arrived at from a measured score regression
rather than from an argument.

## 8. What to do next, in order

1. **Close the eleven contrapositive extensions with licensing lemmas**
   (section 1a group 1). They are the shortest proofs in the 45 and
   they cover the `differentFrom` family that several InconsistencyTest
   passes run through.
2. **State truth-preservation for the eleven-rule witness layer**, or
   stop describing the PE numbers as verified. `CompStar` /
   `comprehensionLayer_sound` in the Lean tree is the same obligation,
   also open (`docs/theorem-registry.md`).
3. **Give `is_inconsistent`'s twelve checks lemmas.** A clash row's
   soundness obligation is the simplest kind — the condition must be
   unsatisfiable — and a wrong one produces an INCONSISTENT verdict on
   a consistent graph, which is the worst failure this engine can have.
   Defect (b) was one of these.
4. **Retire the `[mode]` class from the ledger, or make it name a
   licence.** It was the one class that recorded a switch instead of a
   reason, and it is where the unsound rule hid.
5. **Port the two remaining F\*-only profile passes to Lean**
   (`WebOnt-someValuesFrom-003`, `New-Feature-Keys-002`) so the two
   engines agree on the profile catalogs and the differential keeps its
   power. It found both of this week's defects.

## 9. Method notes, for whoever runs this again

* **The differential is the instrument that worked.** Neither defect is
  visible to the F\* test suite, to `make verify`, or to reading the
  rule in isolation — the DIRECT gate and the `has_extra_property`
  guard both read as careful engineering. What exposed them was a
  second implementation being asked to reproduce the same verdict and
  refusing. Keep both trees scoring the same corpus.
* **A targeted OCaml extraction is not a build.** `build-ocaml.sh`'s
  `extract` step injects eight OCaml `include` lines at the top of
  `RDF_Graph_Executable.ml` (mechanical re-export of the F\* `include`s,
  script line 1079). Running `fstar.exe --codegen OCaml` on single
  modules by hand skips that, and the next `compile` fails with
  `Unbound type constructor RDF_Graph_Executable.subject` — a sibling of
  anti-pattern 11. Reapply the header, or run the real `extract`.
* **A committed `.ml` can be behind its `.fst`.** The compile also
  failed on `Unbound value RDF_Entailment_Regime.rdf_inconsistent`,
  which had nothing to do with this work: the RDF 1.2 landing committed
  the `.fst` and correctly did not commit the `.ml`. Re-extract any
  module whose `.fst` moved since the last full extraction.
* **Do not score under load.** Section 6's caveat.
* **A test binary chosen by `-x` is not a runnable binary.**
  `formal/fstar/ocaml-output/factoidal` is a committed symlink into one
  platform's `bin/` directory, so `-x` passes everywhere and the binary
  runs on one platform. Probe with `--version`.
