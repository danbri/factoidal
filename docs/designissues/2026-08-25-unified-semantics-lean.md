# 2026-08-25 — Unified model theory in Lean 4: LBase/IKL over every semantic language in the tree

## Status

Design (Stage 0 of
[https://github.com/danbri/factoidal/issues/598](https://github.com/danbri/factoidal/issues/598)).
No code lands with this document. Every Lean signature and theorem
statement below is a proposal; each one becomes real only in the stage
that proves it, under that stage's gate.

Stages 1-7 have since landed, and so has the §4.7 RIF Core stage that
correction note 15 deferred (`Unified/RifEmbed.lean`, 2026-08-26,
[https://github.com/danbri/factoidal/issues/612](https://github.com/danbri/factoidal/issues/612);
correction notes 38-41 — its gate theorems are full iffs against the
Datalog least fixpoint, NOT against the native RIF engine, for the
reason note 38 gives). Read this document with the correction
notes below, which record where the implementation contradicted it.
The stage 7 account of what was proved, at what strength, with the
named gaps and the defects the proof attempts found, is
[`docs/designissues/2026-08-26-lbase-account.md`](2026-08-26-lbase-account.md);
its public version is hub post 43,
`docs/web/hub/43-one-model-theory-under-all-of-it.md`.

### Stage 1 correction notes (2026-08-25)

Stage 1 landed (`formal/lean4/L4Factoidal/Unified/`, registry section
9 in [`docs/theorem-registry.md`](../theorem-registry.md)). Four
points of this document were wrong in Lean's eyes and are corrected by
the implementation; the sections below are NOT edited in place, so
read them with these notes:

1. **§2.3 bound-name spelling.** The `_:` spelling cannot support the
   hypothesis-free gate theorem: `RDF.isIri` accepts `"_:x"` as a
   well-formed IRI, so a graph containing the IRI `_:x` next to the
   blank node `x` would have that IRI captured by the closure, and
   `unified_adequate_simple` as stated (no freshness hypothesis) is
   FALSE under that spelling. Landed instead: colon-free injective
   bound names (`bnodeName b = "_" ++ escape b`, `:` → `%c`,
   `%` → `%p`). Every well-formed IRI contains a colon, so freshness
   holds unconditionally (`bnodeName_ne_iri`) and the gate theorem
   needs no side condition.
2. **§4.1 `liftInterp` "dom preserved".** Impossible as stated:
   `CL.fn` receives only the DENOTATIONS of the `literalValueOf`
   arguments, and with `dom = r.idom` the lexical form and datatype
   IRI that `r.iLit` needs cannot be recovered (`iStr`/`iName` need
   not be injective). Landed domain: `Option String × r.idom` — the
   second component is the RDF denotation (what the transfer lemma
   equates), the first tags name/string denotations with their
   source string for the operator to decode. `rel` reads only the
   second component.
3. **§2.4 decoration formula.** The formula
   `atom (name "urn:cl:def:names") [term n, that (rdfToTheory G)]`
   contradicts this same section's scoping bullet: re-closing `G`
   inside `that` shadows the dataset-wide binding and loses the
   blank-node sharing the bullet establishes. Landed:
   `that (rdfBody G)` — the unscoped body — under the dataset-level
   closure. AMENDED 2026-08-26 (note 37): the decoration is no longer
   the whole contribution — a named graph the DEFAULT graph decorates
   with `urn:cl:def:asserts` also contributes
   `atom (that (rdfBody G)) []`, the zero-ary assertion of its
   proposition.
4. **§6.1 DatasetEmbed "N-Quads round-trip corollaries".** No native
   theorem to compose with yet: the tree's round-trip theorem covers
   only the empty graph (`Syntax/SyntaxTheorems.lean`). Deferred to
   [https://github.com/danbri/factoidal/issues/576](https://github.com/danbri/factoidal/issues/576).

Two clarifications that are refinements, not corrections: `EntailEquiv`
landed as per-interpretation satisfaction-equivalence (stronger than
mutual entailment, and what the merge proof delivers), and the merge
operation the §4.1 statement calls `RDF.merge` landed as
`Unified.mergeGraphs` (union after `Graph.prefixBnodes`
standardizing-apart; the native tree has the renaming but no named
merge operation). Stage 1 landed without `DSchema.lean` /
`unified_adequate_d`, which go with the D-entailment landing.

### D-entailment landing notes (2026-08-25)

`Unified/DSchema.lean` landed (`dSchema`, `unified_adequate_d`, the
§5.1 separating model). Three notes in the same spirit as 1–4 above:

5. **§4.1 native anchor.** As the parenthetical under the
   `unified_adequate_d` statement anticipated, the native tree had NO
   model-theoretic D-entailment: `RDF/Semantics.lean` stops at
   `SimpleEntailsMt`, and `RDF/EntailmentTheorems.lean` deliberately
   gives the `literalValueEq` regime variants no soundness theorem.
   `RDF.DInterpCond` / `RDF.DEntailsMt` are therefore introduced with
   the landing (in the `RDF` namespace, inside `Unified/DSchema.lean`),
   as `EntailsUnder` over interpretations that (a) identify literals
   `literalValueEq D` accepts and (b) exclude `literalIllFormed D`
   literals from every property extension's object position. This is
   the fragment of RDF 1.1 Semantics §7 the tree's executable datatype
   machinery expresses; completeness against the full §7
   D-interpretation class (value-space structure) is not claimed.
   `RDF/EntailmentRdfsDatatypeClash.lean`, which §4.1 cites, is the
   `rdfs:range` clash rule — that is RDFS-regime material and rides
   with stage 2, not with `dSchema`.
6. **The decided corollary is deferred, with a machine-checked
   reason.** The executable anchor `RDF.regimeEntails .d` exists, but
   the characterisation theorem the simple corollary composed with
   (`simpleEntails_iff_mt`) has no D analogue, and the correspondence
   is FALSE without triple-term-freedom hypotheses: the procedure's
   inconsistency check collects literals inside RDF 1.2 triple terms
   (`Term.literals` recurses through `tripleTerm`), while both model
   theories — native `iTt` and the `urn:cl:def:tripleTerm` operator —
   read a triple term as an uninterpreted function of its components'
   denotations, so a triple-term-interior ill-typed literal yields no
   contradiction. `dEntailsMt_tt_gap` plus a `#guard` pin the
   disagreeing pair. The future corollary needs a native
   D-interpolation lemma under `GraphTtFree` on both graphs.
7. **§2.5 quantification domain.** The value-identification rows are
   stated over literal PAIRS `literalValueEq D` accepts (which covers
   the cross-datatype numeric chain, e.g. `xsd:integer`/`xsd:int`),
   not per-datatype lexical-form pairs as §2.5's wording suggests —
   matching what `Regime.literalEq` actually decides with. The
   exclusion rows stay silent about ill-typed terms beyond the
   exclusion itself, as §5.1 requires; the separating model
   (`dSepInterp`, satisfies value identification + the translated
   ill-typed graph, refutes the exclusion axiom) is in
   `Unified/DSchema.lean` next to the schema rather than in
   `Witnesses.lean`.

### Stage 2 landing notes (2026-08-25)

`Unified/RhoDfSchema.lean` and `Unified/RdfsSchema.lean` landed
(recovered from an interrupted agent run, verified and completed).
Four notes in the same spirit as 1–7:

8. **§4.2 ρdf gate strength.** The design statement carried
   `RhoDfModelFragGraph` hypotheses. Landed instead: the gate theorem
   `unified_adequate_rhoDf` is an UNCONDITIONAL iff against the native
   model-theoretic relation `RDF.RhoDfEntails` (which postdates this
   document's statement). The fragment, closedness and
   triple-term-freedom hypotheses belong to the DECIDED corollary
   `unified_adequate_rhoDf_decided`, where the native Herbrand
   construction (`rhoDfClosed_iff`) needs them; each has an executable
   sufficient check (`rhoDfClosedCheck`, `RDFS.isRhoDfFrag`)
   dischargeable by `decide` on concrete inputs.
9. **§4.2 full-RDFS strength, §3 schema signatures, and the bridge's
   home.** (a) The document predicted soundness-only for full RDFS,
   citing Finding C-1. C-1 blocks the EXECUTABLE characterisation,
   not model-theoretic adequacy: `unified_adequate_rdfs` landed as a
   FULL unconditional iff against `RDF.RdfsEntails` (itself
   `EntailsUnder` over the §9 conditions); no decided RDFS corollary
   is stated, and C-1's witness pair is restated at the unified level
   (`rhoDf_not_entails_selfLoop_unified` vs
   `rdfs_entails_selfLoop_unified` — also the strictness witness
   between the two schemas). (b) `rdfSchema` landed WITHOUT the `D`
   parameter (the native `RDF.RdfConditions` carries none; rdfD1 is
   excluded by both engines), and `rdfsSchema` takes a
   `RDF.DatatypeSet`, adding the `dMinimal` rows the native bundle
   carries. (c) §3's `rdfsSchema` docstring folded the
   type-application bridge into the schema; that would make the gate
   iff FALSE — `liftInterp` gives every non-binary predication an
   empty extension, so no lifted interpretation satisfies the bridge
   over a non-empty type extension. Landed: `typeBridge` is a
   SEPARATE one-sentence schema with a conservativity theorem over
   translated graphs (`typeBridge_conservative`, by rel-surgery
   `bridgeify`) and a machine-checked separation outside the
   translated fragment (`bridge_derives_classApp` /
   `rdfsSchema_no_classApp` on the LBase class-application sentence).
10. **§5.7 finite-slice, and one weakening.** (a) The landed schemas
    index their axiom rows by the native predicates
    `RDF.RdfAxiomatic` / `RDF.RdfsAxiomatic`, which carry the FULL
    infinite `rdf:_n` families — both sides of every gate iff
    quantify over the same family, so no landed theorem consumes a
    finite-slice-suffices lemma. It becomes load-bearing only for a
    decided full-RDFS corollary, which C-1 independently blocks;
    recorded as the stage's named open lemma in the registry, not
    proved. (b) One recorded weakening: `unified_rdfs_closure_sound`
    (and `RDF.axiomaticTriples_hold` under it) carries the hypothesis
    `rdf:XMLLiteral ∈ D`. The closure's seed table
    (`RDFS.rdfsAxiomaticTriplesFixed`, 40 rows) contains
    `rdf:XMLLiteral rdf:type rdfs:Datatype` and
    `rdf:XMLLiteral rdfs:subClassOf rdfs:Literal`, which RDF 1.1
    Semantics §9.3 does NOT list as RDFS axiomatic triples (the note
    after the spec's table: RDF-D interpretations MAY fail to
    recognize `rdf:XMLLiteral`/`rdf:HTML`); the spec-faithful 38-row
    `RDF.rdfsAxiomaticTriples` table rightly excludes them, and the
    two rows are true in a §9 interpretation exactly when
    `rdf:XMLLiteral` is recognised. `#guard`s pin the table mismatch
    in `Unified/RdfsSchema.lean`.

### D-entailment repair note (2026-08-25, issue 602)

11. **Correction note 6 mis-attributed the divergence, and §2.5's
    exclusion schema was too narrow.** Note 6 (and
    `dEntailsMt_tt_gap`) read the executable's triple-term-interior
    literal collection as the defect. The decided spec anchor
    ([https://github.com/danbri/factoidal/issues/602](https://github.com/danbri/factoidal/issues/602))
    is the RDF 1.2 Semantics Working Draft (7 April 2026,
    [https://www.w3.org/TR/rdf12-semantics/](https://www.w3.org/TR/rdf12-semantics/)
    — a WD, not a Recommendation): §5's compositional triple-term
    denotation `I(E) = IT(I(E.s), I(E.p), I(E.o))` with §7.1's "any
    triple containing the literal must be false", as the W3C rdf12
    `malformed-literal` test states ("Malformed literals are allowed
    in triple terms, but cause inconsistency"). The EXECUTABLE was
    right; the totalized model theory was the diverging layer. Landed:
    `RDF.DInterpCond` clause 2 and `dExclusionSchema` now exclude
    every term with an ill-typed MENTION (`RDF.termIllTypedMention`,
    interiors included); `dEntailsMt_tt_gap` is removed — its content
    survives as `topLevel_exclusion_insufficient_for_tt` over the
    superseded bundle `DInterpCondTopLevel`, and the flipped pin is
    `dEntailsMt_tt_illtyped` (agreement, both layers TRUE). The
    decided corollary landed as its SOUND half,
    `unified_adequate_d_decided_sound` — unconditional, no
    `GraphTtFree` (note 6's prediction that the corollary needs
    triple-term-freedom is withdrawn); the COMPLETE half is the
    registry's named open lemma (D-Herbrand literal quotient by
    `literalValueEq D` + `bindable`-restricted search completeness),
    and is not a triple-term matter.

### Stage 3 landing notes (2026-08-25)

`Unified/Datalog.lean` and `Unified/DatalogClosures.lean` landed
(the generic least-fixpoint theorems and the closure-engine
exhibits). Four notes in the same spirit as 1–11:

12. **§3 Datalog signatures.** (a) `DAtom.pred` landed as a `DTerm`
    (variable or constant), not the `String` of §3's sketch: rdfs7's
    and eq-rep-p's heads predicate on a VARIABLE, which CL's
    unsegregated universe reads directly; a string predicate cannot.
    (b) `DatalogProgram` landed with a `wf` PROOF FIELD
    (definiteness + the colon-free variable discipline), so the
    "no existential heads" comment of §3 is enforced by construction —
    a rule of rdfD1's shape cannot be written into a program
    (`rdfD1Shape_not_wf` pins the rejection). (c) `DRule` therefore
    has no separate wf story of its own; `DTerm` has no function
    symbols in ANY position, which only shrinks the class §3 sketched.
13. **§4.3 exhibit statement.** The design equation
    `(rhoDfProgram.lfp (factsOf g) fuel).toGraph = RDFS.closureFix g`
    is not the landed form, per the stage 2 salvage's instruction:
    agreement is MEMBERSHIP equality
    (`rhoDf_closure_datalog_agree`), because the engine's list
    order/`Triple.eqb` dedup cannot match a generic fixpoint's list.
    The landed hypotheses are exactly the stage 2 decided corollary's
    engine-side pair (`rhoDfClosedCheck`, `isRhoDfFrag`, both
    `decide`-dischargeable) plus Datalog-side `FuelAdequate`
    (executable check `saturatedCheck`), plus `RhoDfModelObjectOk` on
    the queried triple's object — the encoding gives literal /
    triple-term objects placeholder constants, so injectivity (and
    the iff) holds ON the ρdf model fragment, where the engine's
    completeness story lives anyway. The Datalog rules mirror the
    DIAGONAL specification relations `Rdfs*Derives` — NOT the engine
    step functions — so the decode direction lands on `RhoDfClosed`,
    blank-node classes included (the engine step's rdfs9 blank-node
    gap is closed by the closedness hypothesis, exactly as in
    stage 2's `rdfs9BnodeConclusions`).
14. **§4.3's second exhibit tier is instance-level.** The RDFS-Plus
    tier (`rdfsPlusProgram`: the six ρdf rows + the 13 OWL
    equality/property rows + the four schema-level inverseOf flips —
    the RL closure's non-list, non-clash core) landed with agreement
    against `RDFS.rdfsPlusClosure` established on the demo instances
    of `RDFS/RDFSPlus.lean` in both directions — as a `decide`d
    theorem on the TransitiveProperty demo, and as native-evaluated
    build-time `#guard` pins on the sameAs and inverseOf demos, whose
    substitution closures exceed the kernel `decide` budget (the
    kernel re-evaluates each unshared fixpoint round) — plus the
    generic gate theorem instantiated on one. A GENERAL bridging
    theorem in the ρdf style is not claimed for this tier: the native
    tier itself claims no chain-level completeness, and the engine's
    per-row IRI-subject guards (`subjIri`) restrict firings the
    Datalog rules do not, so the general membership iff is not
    expected to hold off the demo shapes without a new fragment
    predicate. Recorded as the stage's named open item, not a defect.
15. **§4.7 RIF Core did not ride with stage 3.** The document offered
    the split ("if it grows, it splits out as its own M stage");
    taken: `unified_adequate_rifCore` needs `rifCoreToTheory` plus
    the frame/positional-atom desugaring of `RIF/Translation.lean`,
    which is its own module's work. The generic theorem it will
    instantiate is landed and generic (n-ary atoms were built for
    exactly this — RIF positional atoms of arity ≠ 2 need no new
    machinery).

### Stage 4 correction notes (2026-08-26)

Stage 4 landed (`OWL/RLSemantics.lean`, `OWL/RLHerbrand.lean`,
`Unified/OwlRlSchema.lean`, `Unified/OwlRlAdequacy.lean`; registry
section 9). Five points of §4.4 are corrected by the implementation,
and note 21 (added later the same day) corrects two of those notes in
turn.

16. **§4.4's `owlRlSchema D` takes no `D`.** The OWL 2 RL datatype rows
    (Table 7) range over the FIXED tables `builtinDatatypeAxioms`,
    `xsdAxiomTriples` and `rangeIntersectLicenses` of
    `OWL/RLRules.lean`, not over a recognised-datatype parameter.
    Landed as `owlRlSchema : Schema`.

17. **§4.4's `owlRl_row_condition (row : RlRowId)` is not one iff over
    an enumeration of ALL rows.** `RlRowId` in `Unified/OwlRlSchema.lean`
    enumerates the 66 PLAIN Horn rows only, and the bridge is a
    one-directional per-row family (`cond_*`), not an iff. Direction:
    schema sentence → `RlCond*`. The sentence is strictly STRONGER than
    the condition (a `DRule` quantifies its predicate position over the
    whole domain; the condition quantifies over `WfIri`), so an iff is
    false as stated.

18. **Nine rows are carried by the interpretation-class condition, not
    by the schema.** `OwlRlInterpCond` carries prp-spo2 and prp-key
    (their premise relation is TERNARY — cell, subject, object — and
    `RDF.Interp.iext` is binary, so the reserved binary helper
    predicates that serve the other seven collection rows cannot serve
    these two; each needs a sentence family indexed by list length),
    cls-maxc2 / cls-maxc1 / cls-maxqc1 / cls-maxqc2 (a cardinality
    literal embeds as a `funapp` of `urn:cl:def:literalValueOf`, which
    is not a `DTerm`) and the three comprehension rows (existential
    heads, excluded by `DRule.definiteB`). `unified_owlRl_sound` names
    `OwlRlInterpCond` in its statement, so the boundary is visible in
    the theorem.

19. **`unified_owlRl_complete_ground` landed in condition-bundle form,
    not schema-relative form.** `owlRl_complete_ground` states ground
    completeness over `RDF.Interp` + `RlConditions`/`RlClashConditions`.
    The schema-relative form needs `liftInterp (rlHerb c)` to satisfy
    every row sentence, and `liftInterp r` reads a binary predication as
    `r.iext p.2 x.2 y.2` — so satisfaction quantifies EVERY position,
    the predicate position included, over the whole of `r.idom`. That
    full-domain reading is true for `rlHerb c` but is a second pass over
    all 79 rows, not a corollary of `rlHerb_conditions`.

20. **The completeness model needs a fragment, and the fragment is
    narrow.** `RlHerbFrag` (`OWL/RLHerbrand.lean`) requires: every
    object an IRI or blank node; `rdf:nil` heads no cons cell;
    `owl:disjointWith` has IRI endpoints; no reserved `urn:cl:def:` IRI
    anywhere. Clause (a) excludes every graph whose closure carries a
    cardinality literal — which includes any graph declaring
    `owl:ObjectProperty`, because the minc1 comprehension row emits an
    `owl:minCardinality "1"` triple. The completeness direction
    therefore does not reach cardinality-bearing ontologies.

21. **Correction note 18 is superseded in part, and one of its reasons
    was wrong** (2026-08-26, later the same day,
    [issue 613](https://github.com/danbri/factoidal/issues/613)).
    `OwlRlInterpCond` now carries FIVE rows, not nine.

    **What moved.** `Unified/Datalog.lean` gained `DTerm.lit`, a term
    constructor carrying an `RDF.WfLiteral` whose `toCl` is
    `embedTerm (.literal l)` and whose `val` is the denotation
    `restrictInterp` gives `iLit`. A cardinality-literal row is then an
    ordinary `DAtom`, so cls-maxc2 is a plain Horn row
    (`RlRowId.clsMaxc2`) and cls-maxc1, cls-maxqc1, cls-maxqc2 are
    plain clash rows (`RlNegRowId`). `owlRlSchema_cardinality_rows`
    states the four as consequences of schema satisfaction alone.

    The new constructor is free in the MODEL-theoretic layer
    (`DTerm.wfB` holds of every literal: the colon discipline is about
    capture under the universal closure, and a literal binds nothing).
    It is not free in the OPERATIONAL layer: `herbInterp`'s domain is
    the constant names, so a rigid literal term denotes outside that
    Herbrand universe. `DTerm.litFreeB` names the restriction and
    `herb_holds_iff`, `herb_ground_mem_iff`, `herb_satisfiesSchema`,
    `datalog_lfp_complete` and `datalog_lfp_iff_entails` carry it as a
    hypothesis. Every existing call site discharges it by computation,
    so no landed gate theorem weakens in substance.

    **The reason that was wrong.** Note 18 said the reserved helper
    predicates "cannot serve" prp-spo2 and prp-key because the relation
    to encode is ternary and `RDF.Interp.iext` is binary. `DAtom` is
    n-ary, and such a helper need never appear in `restrictInterp i` —
    it is internal to the schema and to the bridge proof, so a ternary
    helper IS writable. The real obstruction is
    `Unified/RdfTransport.lean`'s `liftInterp`, which reads `rel p
    args` as `False` at every arity other than 2: a schema row with a
    ternary head would be false at `liftInterp r` for every RDF
    interpretation `r`, i.e. at exactly the models note 19's
    schema-relative completeness needs. The per-length sentence family
    keeps every row binary and costs no model, so it remains the route
    for these two rows. Neither was attempted.

    **Existential heads: a decision, not a blockage.** A `Schema` is a
    predicate on `CL.Sentence`, so cax-dw-comp, cls-maxqc1-comp and
    minc1-comp CAN be put in one. The decision is not to, for two
    costs. (i) The head of `RlCondCompDw` is not a conjunction of
    atoms — `CompProps` carries two universally quantified
    implications and a five-variable one — so each row is a bespoke CL
    sentence with a bespoke satisfaction lemma, an instance of no
    family in `Unified/OwlRlSchema.lean`. (ii) An existential head
    removes the least-model property the completeness direction of the
    stage-3 class rests on (`datalog_lfp_complete`; the same boundary
    `rdfD1Shape_not_wf` pins at the program layer). If they are ever
    admitted it should be as a SEPARATE sub-schema, so that the
    definite `owlRlSchema` stays available for the completeness work.

    **Note 20's expected remedy does not work.** Note 20 records
    `RlHerbFrag` clause (a) as the narrowness, and
    [issue 613](https://github.com/danbri/factoidal/issues/613) item 3
    expected a `DTerm` cardinality literal to widen it. It does not.
    Clause (a) exists for eq-ref, object form: `RlCondEqRefO` demands
    `y owl:sameAs y` for every object `y`, `rlHerb`'s `iext` reads "the
    triple is in the graph", so `y` must be expressible as an
    `RDF.Subject` — and RDF 1.1 Concepts §3.1 gives a triple an IRI or
    a blank node as subject, never a literal. `frag_obj_subject` is
    consumed at fifteen sites of `rlHerb_conditions`. The obstruction
    is the RDF term algebra reproduced in the syntactic model, not the
    Datalog term type. Widening past clause (a) needs a different
    `rlHerbIext` for the `owl:sameAs` row, after which
    `rlHerb_triple_decode` would decode an atom that `OWL.RL.Derives`
    cannot produce — so the fragment and the decode step have to move
    together, or not at all.

    Measured with the landing: OWL probe 1131 pass, 316 fail, 2 skip,
    8 unsupported (out of 1457) — unchanged, the closure engine was not
    touched. SPARQL 1.1 entailment sentinel 70 pass, 0 fail (out of 70)
    in both trees.

### Stage 5 correction notes (2026-08-26)

Stage 5 landed (`Unified/OwlDlDirect.lean`,
`Unified/OwlDlAdequacy.lean`; registry section 9). Six points of §4.5
and §5.3 are corrected or made precise by the implementation.

21. **The tableau's name spaces had to be separated from the RDF
    route's, and the repair is an encoding, not a type change.**
    `OWL.Role` and `OWL.Ind` are `abbrev … := String`, so an individual
    named `"x"` sits in the same string space as the COLON-FREE bound
    names `Unified/RdfEmbed.lean` reserves for blank nodes.
    `OWL/Tableau.lean`'s header invites tightening `Role`/`Ind` to
    `RDF.WfIri`; that was REJECTED. `exWitness` MINTS a fresh
    individual name and `leqMerge` RENAMES one, so both rules would
    acquire an IRI well-formedness obligation and the freshness side
    condition `x ∉ indsOf A` would have to be restated over a subtype;
    and Direct Semantics reads an individual as a structural entity,
    not as an RDF IRI (§5.3). Landed instead: `dlName tag s` =
    `urn:owl:dl:` ++ tag ++ `escape s`, with `tag ∈ {i, c, r}` for
    individual, class and role. Every translated name carries a colon,
    so it is distinct from every `bnodeName` and from every bound
    variable; the three tags make the name spaces pairwise disjoint;
    `escape` is injective, so `dlDecode` recovers the tableau name.
    The gate theorem therefore carries NO freshness hypothesis.

22. **§4.5's gate is stated over `owlDlDirect R A ++ roleAxiomSentences R`,
    which double-counts.** `owlDlDirect` already receives `R`. Landed:
    `owlDlDirect R A = roleAxiomSentences R ++ A.map assertionSentence`,
    and `unified_adequate_dl` is stated over `owlDlDirect R A` alone.

23. **The lift CANNOT use `Unified/RdfTransport.lean`'s tag-product
    domain, and the reason is the cardinality translation.**
    `liftInterp` (stage 1) takes `dom := Option String × r.idom` so
    that the predicate position carries its name identity. That answer
    is UNSOUND for the DL route: `atMost n r` translates to the
    negation of an existential over `n + 1` PAIRWISE DISTINCT domain
    elements, and a product domain has distinct pairs whose `δ`
    components coincide — so an interpretation whose OWL reading
    satisfies `atMost 1 r` would violate the translated sentence.
    Landed: `dom := δ ⊕ String`, with both extensions FALSE on the
    right summand, so every witness a counting formula can use lies in
    the left summand where distinctness is distinctness in `δ`
    (`card_sum_iff`, `sem_inl` in `Unified/OwlDlDirect.lean`).

24. **The transfer is stated once against a compatibility predicate,
    not run twice.** §4.1's pattern proves the restriction and lift
    transfers separately. `OWL.Interp` carries no structure beyond two
    extension families, so `DLCompat i I` (class and role extensions
    read off `i.rel` at the translated names) suffices:
    `sat_conceptFormula` and `satisfiesAll_owlDlDirect_iff` are proved
    against it and instantiated at `restrictInterpDL i` and at
    `dlCompat_lift`. Only `sem_inl` — the left-injection lemma for the
    sum domain — is a second induction over `OWL.Concept`.

25. **`speciesIsDl` cannot serve as the stage 5 fragment guard.**
    `OWL/SyntaxDL.lean`'s species checker takes RDF `Graph`s
    (five of them) and decides OWL 2 DL membership from triples. The
    Direct-Semantics route does not factor through graphs (§5.3) and
    the tree has NO reader from `Graph` to `List OWL.Assertion`, so
    there is no place to attach it: it would guard a different input.
    The stage 5 fragment guard is STRUCTURAL instead — `OWL.Concept`
    and `OWL.Assertion` ARE the fragment, so `refuted_unified_unsat`
    needs no fragment hypothesis at all. What the tableau fragment
    omits relative to OWL 2 DL (nominals, datatypes, functional roles,
    inverse roles, property chains, TBox axioms other than the role
    box) is recorded as boundary rows in the registry, not as a guard
    that does not fit.

26. **Tableau COMPLETENESS is not available, so the gate is one
    direction plus a satisfiability `↔`.** `unified_adequate_dl` is a
    full `↔` between CL satisfiability of the translation and
    `OWL.Consistent`. The refutation gate `refuted_unified_unsat` is
    soundness only: `OWL/Tableau.lean`'s `Refuted` has no blocking
    condition and no ⊔-saturation strategy, and
    `OWL/TableauTheorems.lean` proves soundness only, so
    `¬ OWL.Consistent R A → OWL.Refuted R A` is not derivable here.
    Recorded as a registry gap row rather than weakened into a claim.

### Stage 6 correction notes (2026-08-26)

`Unified/SparqlQuery.lean` and `Unified/SparqlAdequacy.lean` landed
(BGP matching and the entailment regimes). Six notes in the same
spirit as 1-26:

27. **§4.6's single membership iff splits into a pivot plus two
    theorems.** The statement
    `μ ∈ evalBgp b g ↔ (μ.domExact b ∧ μ.rangeIn g ∧ Entails …)`
    cannot be proved, and not for want of effort: membership in
    `evalBgp b g` is LIST membership of a `Binding`, and two of its
    properties are invisible to any semantic condition. (a) ORDER —
    the evaluator conses bindings as it walks subject → predicate →
    object, left to right through the pattern list, so the mapping it
    returns is one particular permutation of the pairs. (b)
    COARSENESS — `tryBindTerm`'s already-bound arm keeps the FIRST
    term bound to a variable and only compares the graph's own term to
    it with `Term.eqb`, so a returned mapping's terms need only be
    engine-equal to the graph's, not structurally identical
    (`SPARQL/BgpRefinement.lean`'s header records the same point for
    its own conclusion). Landed instead: the pivot
    `BgpMatches μ b g` (every pattern instantiates under μ into `g` by
    engine equality), the gate `unified_adequate_bgp` as a full iff
    between the pivot and `Answers`, `bgp_eval_sound` (unconditional)
    and `bgp_eval_complete` (agreement up to `Term.eqb`). The two
    chains `unified_adequate_bgp_engine` and
    `unified_bgp_answers_returned` are what a reader of §4.6 wanted.
    Also withdrawn: the `μ.domExact b` conjunct. It is not needed —
    the term model REFUTES an unbound variable through the tag
    component of its denotation rather than excluding it by
    assumption — so the gate carries no domain hypothesis at all.

28. **`UQuery` carries the pattern, not an arbitrary `CL.Sentence`.**
    §3's `structure UQuery where vars : List VarName; body :
    CL.Sentence` makes `UQuery.instantiate` a capture-avoiding
    name-substitution over `CL.Sentence`, which needs a substitution
    engine plus a non-capture lemma that is false in general (a
    substituted term can be captured by an enclosing `all` / `ex`).
    The bodies this stage produces are quantifier-free conjunctions of
    atoms, where the substitution and the compositional definition
    agree, so the landed structure carries `pattern : SPARQL.Bgp` and
    `body` is the derived accessor `bgpBody [] q.pattern` — exactly
    the open body §3 names. If a later stage needs `UQuery` over an
    arbitrary sentence, the substitution engine is the work item, not
    a rename.

29. **`regimeToSchema` is the SPECIFICATION table; the engine
    dispatcher is narrower, and the two disagree on `"RDFS"`.**
    `RDFS.entailmentClosureForQueryExt` recognises `x-rdfscore` and
    `x-rdfsplus` and routes EVERY other string — `"RDFS"`,
    `"OWL-RL"`, a typo — to `OWL.RL.closure`. Its own module header
    states this. So a regime row that said "RDFS regime" without
    saying WHICH closure would misdescribe the engine.
    `regimeToSchema` resolves the four W3C names through
    `RDF.Regime.ofName?` (whose `.rdfs` closure is
    `RDFS.fullClosure`), `regimeDispatchSchema` records what the
    dispatcher selects, and a `#guard` pins the disagreement.
    `regime_sound_rdfs` is stated against `RDF.Regime.closure .rdfs`
    and says so.

30. **Regime soundness landed for `simple`, `x-rdfscore` and `RDFS`;
    `x-rdfsplus` did not, and regime completeness is a different
    claim.** §4.6's `regime_sound` shape landed once as
    `regime_sound_of_closureHolds`, whose premise is the regime's own
    content. `x-rdfsplus` has no closure-soundness theorem to supply
    that premise: stage 3 landed the RDFS-Plus Datalog tier at
    demo-instance strength, and `RDFS/RegimeDispatch.lean`'s own claim
    column already refuses chain-level completeness for it because
    `owl:sameAs` breaks the Herbrand construction — that refusal
    transfers verbatim. Separately: §4.6's parenthetical "x-rdfscore
    (with the ↔ form, via stage 2)" is delivered as
    `regime_rhoDf_answers_closure_iff`, a full iff saying the
    MATERIALISATION is answer-preserving. That is not "the engine
    returns every ρdf answer", which needs the closure to be
    SATURATED — the `rhoDfClosedCheck` hypothesis the stage 2 decided
    corollary carries. Recorded as a gap row, not folded into the iff.

31. **The `x-ikl-*` family is a dataset TRANSFORM, so it enters as a
    premise-list transform and gets no schema.**
    `CL.IklRegime.extendDataset` does not close a graph under rules;
    it merges the content of every ASSERTED proposition into the
    default graph. `ikl_extend_entailed` is the one theorem about the
    merge: the extended default graph's Skolem reading is entailed by
    `iklPremises ds` — the dataset's own graphs, read Skolem-wise —
    unconditionally and independently of the suffix. What it
    deliberately does NOT claim: that the merge is CONSERVATIVE (no
    landed theorem ties the `urn:cl:def:asserts` decoration to
    `CL.IklRespectsThat`), and anything about named subsets, which
    stay deferred to
    [https://github.com/danbri/factoidal/issues/581](https://github.com/danbri/factoidal/issues/581)
    per the owner ruling recorded there. SUPERSEDED 2026-08-26 by note
    37: the merge IS now tied to `CL.IklRespectsThat` — the embedding
    asserts an `urn:cl:def:asserts`-decorated named graph zero-arily,
    and `ikl_extend_entailed` is stated over `datasetToTheory` rather
    than `iklPremises`.

32. **`Term.eqb` is coarser than syntactic identity, and without a
    schema row for that the SOUNDNESS half is false.** `Graph.mem` is
    stated over `RDF.Term.eqb`, which identifies literals differing in
    language-tag CASE and `rdf:XMLLiteral` lexical forms that are
    exclusive-canonical-XML equal. Two such literals embed to
    DIFFERENT CL terms, so a plain CL interpretation may separate
    them, and "the pattern instantiates to a triple `Graph.mem` finds
    in `g`" would not imply the instantiated body is entailed. Landed:
    `termEqSchema`, one `eq` row per `Term.eqb`-equal pair — the same
    LBase §2.4 axiom-schema mechanism §2.5 already uses for the
    D-entailment value rows. `herbQ` (the term model) had to be built
    for the same reason: `RDF.herbrand`'s domain is `Term` under
    structural equality, so it violates the schema; quotienting the
    domain by `Term.eqb` repairs exactly that and nothing else.
    Recorded while proving `termEqSchema_nontrivial`: `String.toLower`
    does not reduce in the Lean kernel, so neither `decide` nor `rfl`
    discharges `langTagEq "EN" "en" = true`; the theorem carries the
    language-tag fact as a hypothesis and the concrete instance is
    pinned by `#guard`.

33. **The `x-ikl-*` regime's premise reading and the dataset embedding
    are DIFFERENT readings of a dataset, and they disagree.** Note 31
    recorded that no landed theorem tied the `urn:cl:def:asserts`
    decoration to `CL.IklRespectsThat`. `Unified/ClBridge.lean`
    ([https://github.com/danbri/factoidal/issues/609](https://github.com/danbri/factoidal/issues/609)
    item 3) settles what that gap is. `iklPremises ds` asserts the
    default graph AND every named graph; `datasetToTheory ds` asserts
    the default graph and reads a named graph as ONE decoration,
    `atom(names)[n, that(rdfBody G)]`, which asserts nothing.
    `ikl_reading_diverges_from_dataset_embedding` proves the two
    disagree on `wDs`, the translation `CL.toRdfDataset` really
    produces for `((that (Dead OBL)))`: the asserted proposition's
    content triple is entailed by `iklPremises` and is not entailed by
    `datasetToTheory`. `embedding_refutes_content_ikl` shows IKL
    coherence does not repair it — coherence constrains a
    proposition's zero-ary relation extension, and the embedding puts
    the `that`-term in the second argument of `urn:cl:def:names`.
    Two consequences for note 31's own statement:
    `mergeWhere_entailed` proves `ikl_extend_entailed` holds for EVERY
    selection predicate over the named graphs, so "unconditionally and
    independently of the suffix" understates it — the theorem is also
    independent of the assertion test, and therefore does not certify
    issue 581's narrowing; and `regime_sound_ikl`'s soundness is
    relative to a premise reading in which assertion and mention are
    already identified. The repair is stated:
    `IklAssertionCommitment` is the regime's own encoding commitment
    over the decoration vocabulary alone, and under it plus coherence
    the embedding entails the whole extended default graph on the
    blank-node-free fragment (`embed_entails_extension`). Adopting it
    as a regime condition, or restating regime soundness over
    `datasetToTheory`, is the engine-side decision this note does not
    take.

    SUPERSEDED 2026-08-26 by note 37: the owner took the second
    option, and the embedding was changed rather than the condition
    adopted. `IklAssertionCommitment` and `commitment_not_derivable`
    are removed; the theorem names in this note now read
    `decorationOnly_*` and refer to the superseded embedding
    `decorationOnlyToTheory`.

34. **`CL.IklRespectsThat` had no model in the tree.** Every theorem
    over it — `CL.IklEntails`, `CL.sat_assert_that`, and now note 33's
    refutations — needed one, and none existed: a coherent
    interpretation makes zero-ary predication on a proposition decide
    satisfaction of the sentence expressing it, which is a fixpoint,
    and the ad-hoc finite models in `Unified/Witnesses.lean` and
    `CL/Examples.lean` all fail it (`CL/Examples.lean`'s header says
    so of `tiny`). `Unified/ClBridge.lean` §5 builds one: `propModel`
    has domain `Prop`, a proposition IS a `Prop`, and `pSat` writes
    the model's own satisfaction out as a recursion over the CL syntax
    — which is what breaks the circularity between `CL.Sat` and
    `Interp.iProp`. `pSat_eq` proves the recursion agrees with
    `CL.Sat` clause by clause, and `propModel_coherent` turns that
    into `IklRespectsThat` for every relation reading making zero-ary
    predication transparent.

35. **The finite satisfaction checker's agreement is now proved, and
    one of the four conditions its header named is not a hypothesis.**
    `CL/FiniteSatTheorems.lean` proves `satFin_eq`
    ([#609](https://github.com/danbri/factoidal/issues/609) item 1)
    under three hypotheses — lawful `BEq` on the domain type, domain
    completeness, no sequence-marker quantifier — each shown not
    removable by a separating pair. The fourth condition
    `CL/FiniteSat.lean`'s header listed, valuation-independence of the
    IKL `that`-reading, is a property of `FiniteInterp.toInterp` (its
    `iProp` is a lookup keyed by canonical CLIF text), so it is
    `rfl`, not a side condition. What the header condition is really
    about is recorded as a boundary instead: `witFin_not_ikl_coherent`
    shows the finite reading does not meet `IklRespectsThat` in
    general, so `satFin_eq` is agreement with `fi.toInterp`, not with
    IKL entailment. Note 34's `propModel` is the coherent
    interpretation the finite reading is not.

    A method note that cost time: `CL/Semantics.lean`'s satisfaction
    group is compiled by well-founded recursion, so `simp only [Sat]`
    cannot fire at `fi.toInterp` — the valuation `v.ind : String → α`
    type-checks against `String → fi.toInterp.dom` only at DEFAULT
    transparency, and `simp` matches at `implicit`. One
    `rw [Sat]`-proved clause lemma per constructor, stated over an
    arbitrary `Interp`, is the fix; they are public in
    `CL/FiniteSatTheorems.lean` for any later proof over `CL.Sat`.

36. **CLIF reader adequacy is a fragment statement with two obstacles,
    not a theorem** ([#609](https://github.com/danbri/factoidal/issues/609)
    item 2, `CL/ClifAdequacy.lean`). Annex A carries no meaning
    function of its own, so the only adequacy claim available is the
    round trip against the serialiser, and that is FALSE in general:
    `Sentence.toClif` guards NAME spellings through `renderName` but
    writes a sequence marker as the raw `"..." ++ m`, so
    `.atom (.name "P") [.seqmark "a b"]` serialises to `(P ...a b)`
    and reads back with TWO argument items. The string-level `#guard`s
    already in `CL/Clif.lean` cannot see it — the misparse
    re-serialises to the same text. `marksLexable` is the fragment,
    found by measuring 38 shapes.

    The general lemma is open (it needs `lexAcc` fuel-monotonicity and
    a decomposition over `++`, then the same for `parseSExpr`).
    INSTANCE-level theorems are open too, for a different reason
    worth recording: the kernel cannot reduce this parser at useful
    sizes. Measured 2026-08-26 on a 16 GB container, `(P a)` and
    `(P a b)` reduce in 4-6 s while `(P ...a b)` and
    `(forall (x) (P x))` exhaust memory and are killed after
    150-200 s; the cliff is in the string primitives the lexer goes
    through, not the grammar. Any future plan that assumes `rfl` or
    `decide` can pin a parser instance in this tree should start from
    that measurement.

### Dataset-embedding repair note (2026-08-26, issue 609 item 3)

37. **The repair for note 33 is a change to the EMBEDDING, not an
    adopted condition.** Owner ruling (2026-08-26, verbatim): "The
    correct path is (3.)" — change the embedding so the `that`-term
    sits where IKL coherence bites. Landed in
    `Unified/DatasetEmbed.lean`: a named graph the DEFAULT graph
    decorates with `urn:cl:def:asserts` now contributes a SECOND
    conjunct, `atom (that (rdfBody G)) []` — the proposition applied
    as a relation with no arguments, which is CLIF's own
    cancelling-parentheses assertion `((that S))` and the position
    `CL.IklRespectsThat` constrains. The naming decoration
    `atom(names)[n, that(rdfBody G)]` is retained, so the graph-name
    identification the regime relies on is unchanged, and a named
    graph WITHOUT the decoration still asserts nothing.

    What follows, all in `Unified/ClBridge.lean`:

    * `embed_asserts_decorated_graphs` DERIVES the regime's encoding
      commitment from `CL.IklRespectsThat` alone. The adopted
      condition `IklAssertionCommitment` and its non-derivability
      witness `commitment_not_derivable` are REMOVED — both were
      statements about the superseded embedding.
    * `ikl_extend_entailed` and `regime_sound_ikl` are restated over
      `[datasetToTheory ds]` under `CL.IklRespectsThat`, and moved out
      of `Unified/SparqlAdequacy.lean` into `Unified/ClBridge.lean`.
      This answers note 33's "engine-side decision this note does not
      take": regime soundness is now soundness with respect to the
      unified layer's own dataset reading.
    * The new statement is SENSITIVE to the `urn:cl:def:asserts` test,
      which note 33 recorded that the old one was not:
      `embedding_sees_the_assertion_decoration` entails the content
      over `wDs` and refutes it over `wDsMentioned` — the same dataset
      with the assertion decoration deleted — while `iklPremises`
      entails it over both. The superseded, predicate-blind statement
      stays as `iklPremises_extend_entailed` beside
      `mergeWhere_entailed`, which is the measurement that condemned
      it.
    * Note 33's divergence theorems are NOT deleted. They are
      restated about `decorationOnlyToTheory` — the superseded
      reading, kept in `Unified/DatasetEmbed.lean` — where they remain
      true: `ikl_reading_diverges_from_decoration_only_embedding` and
      `decorationOnly_refutes_content_ikl`. This is the
      `topLevel_exclusion_insufficient_for_tt` pattern of note 11.
      `decorationOnly_strictly_weaker` pins the two readings apart:
      `coherentBlind` satisfies the superseded one and refutes the
      repaired one.

    What the repair does NOT claim. `ikl_extend_entailed` still
    carries the fragment guard `datasetBnodeNames ds = []` (every
    `ToRdf` output occupies it; `#guard` pins it for the witness, not
    proved for all texts). It still says nothing about the SUFFIX —
    all `x-ikl-*` suffixes route to one handler, per the owner ruling
    in [https://github.com/danbri/factoidal/issues/581](https://github.com/danbri/factoidal/issues/581). It is soundness only; no completeness claim
    in either direction. And `datasetToTheory` is now
    VOCABULARY-SENSITIVE: it gives `urn:cl:def:asserts` a meaning, so
    it is no longer a reading of an arbitrary RDF dataset that adds
    nothing to RDF 1.1 Concepts §4 — it is the unified layer's reading
    of a dataset in which that decoration is the layer's own reserved
    vocabulary, alongside `urn:cl:def:names`,
    `urn:cl:def:literalValueOf` and `urn:cl:def:tripleTerm`.
    `dataset_decoration_asserts_nothing` is what survives of the
    RDF 1.1 neutrality: an undecorated named graph asserts nothing.

### RIF Core stage correction notes (2026-08-26, issue 612)

`Unified/RifEmbed.lean` landed: the deferred §4.7 stage that
correction note 15 split out of stage 3. Four notes.

38. **§4.7's `unified_adequate_rifCore` is NOT landed against the
    native engine, and cannot be while three definitions are
    `partial`.** The sketch puts `t ∈ RIF.Engine.saturate rs g fuel`
    on the left. `RIF/Engine.lean`'s `groundTm`, `matchFormula` and
    `qualifyTm` are `partial def`. A Lean `partial def` compiles to an
    opaque constant: it has no equation lemmas, the kernel cannot
    reduce it, and nothing about what it COMPUTES is available to a
    proof. The theorem needs exactly the missing fact — that a
    substitution `matchFormula` returns makes the body true in the
    fact set — so it cannot be stated, let alone proved.
    `RIF/EngineTheorems.lean` was already written around this limit:
    its `Licensed` predicate MENTIONS `matchFormula`'s output rather
    than characterising it, which is why that module proves
    PROVENANCE and its own header declines to call the result
    soundness. `decide` is blocked for the same reason, so not even a
    concrete instance can be a theorem.

    Landed instead: the same gate theorem with `DatalogProgram.lfp` —
    the total least fixpoint of the SAME rules read as a Datalog
    program — on the left. `rifCore_lfp_iff_entails_atom` (n-ary) and
    `rifCore_lfp_iff_entails` (§4.7's triple shape) are FULL IFFs,
    obtained by instantiating stage 3's two generic theorems rather
    than re-proving them. Agreement with
    `RIF.Saturate.saturateGraph` is pinned by
    `rifEngineDatalogAgrees` `#guard`s under COMPILED evaluation,
    which can see through the `partial def`s — evidence at the
    strength of note 14's RDFS-Plus pins, not a theorem. Making the
    three definitions total is the named prerequisite; it is a change
    to `RIF/Engine.lean` and therefore its own piece of work.

    Two smaller corrections in the same sketch: there is no
    `RIF.RuleSet` type (a rule set is `List RIF.Rule`; `RifRuleSet`
    abbreviates it locally rather than editing `RIF/Syntax.lean`), and
    no `RIF.Engine.saturate` (the graph-level entry point is
    `RIF.Saturate.saturateGraph`).

39. **The desugaring lands on the unified layer's OWN triple
    predications, and that fixes the fragment.** §4.7 asked for RIF
    Core rules "over the same triple predications the rest of the
    unified layer uses". That is achievable — and it is what makes
    this stage different from `Unified/DatalogClosures.lean`, which
    encodes RDF terms into a tagged constant vocabulary (`"i:"` /
    `"b:"`) and therefore states its entailments over sentences of
    that vocabulary rather than over `tripleAtom`. Here a `rif:iri`
    constant with a well-formed IRI lexical form maps to the IRI
    STRING ITSELF, so `(rifTripleFact t).sentence = tripleAtom t`
    holds definitionally on the fragment, and the premise list is
    satisfaction-equivalent to `[rdfToTheorySk g]`
    (`satisfiesAll_tripleAtoms_iff`). The conclusion is
    `rdfToTheory [t]` exactly as §4.7 writes it.

    The price is the fragment: `TripleIriOnly` / `GraphIriOnly`.
    Blank nodes are excluded because `Unified/RdfEmbed.lean` spells a
    blank-node bound name COLON-FREE by construction and the Datalog
    class requires a constant to contain a colon; literals are
    excluded because `embedTerm` maps a literal to a FUNCTIONAL term
    and the class has no function symbols. Both are consequences of
    the class and of stage 1's freshness decision, not of any choice
    made here. Off the fragment `rifCoreConstName` mints a reserved
    `urn:rif:c:` name and nothing is proved about it.

40. **RIF-DTB built-ins, `Equal`, `Or` and `Exists` are outside the
    class, and the module says so with `decide`d rejection
    theorems.** The Datalog class has no equality atom, no built-in
    predicate, no disjunctive body and no existentially quantified
    body variable, so all 197 RIF-DTB built-ins are outside it. This
    is a narrower fragment than the native engine covers: the engine
    decides a named subset of the built-ins and answers `.undecided`
    for the rest, whereas the unified layer says nothing at all about
    a rule that uses one. `rifEqualBodyRule_rejected`,
    `rifBuiltinBodyRule_rejected`, `rifOrBodyRule_rejected`,
    `rifFunctionTermRule_rejected` and
    `rifExistentialHeadRule_rejected` pin each exclusion; the last is
    the class's definiteness gate doing the same job RIF's own
    `ruleSafe` does.

41. **`RIF.collectAtoms` had to be restated structurally, and that is
    a fact about `decide`, not about the function.**
    `RIF/Translation.lean`'s `collectAtoms` recurses through a `foldr`
    closure over `List Formula`, so Lean compiles it by WELL-FOUNDED
    recursion, and a well-founded definition does not reduce in the
    kernel — every `decide` in this module would have got stuck on
    it. `rifCollect` / `rifCollectList` is its structural twin,
    clause for clause, mutual over the nested `Formula` /
    `List Formula` inductive. The two are pinned against each other by
    `#guard` on every rule the module names, the rejected boundary
    shapes included. Nothing here says `collectAtoms` is wrong; the
    same pattern will recur wherever a `decide`d instance needs a
    function the elaborator compiled by well-founded recursion.

## 1. Goal and provenance

Owner direction (2026-08-25, verbatim, from
[https://github.com/danbri/factoidal/issues/598](https://github.com/danbri/factoidal/issues/598)):

> "Do it, with ultimate integration of all the semantic languages we
> implement here including rdf core semantics, rdfs, rhoDF/rdfscore,
> owl rl, owl dl tableaux, sparql 1.x, nquads etc. Throw in an lbase
> and datalog if you like just bind it all together in lean deeply. We
> want more than previously merely using f+ as a vibe coding
> functional language. Lean-backed lbase ikl gives a unifying account
> of w3c logical assertion and querying and logic languages."

### The lineage

**LBase** (R. V. Guha and Patrick Hayes, *LBase: Semantics for
Languages of the Semantic Web*, W3C Working Group Note, 10 October
2003, [https://www.w3.org/TR/lbase/](https://www.w3.org/TR/lbase/))
proposed one first-order base language into which each Semantic Web
language translates, so that "the model theory of Lbase is the model
theory of all the Semantic Web Languages" (§2, Outline of Approach).
Its §3.0 recipe is: a translation procedure per language, a vocabulary
set, and axioms/axiom schemas that constrain the vocabulary's intended
meanings; the translation of a graph conjoined with the instantiated
axioms is the graph's "axiomatic equivalent" A(G). The Note supplies a
sketch translation table for RDF (§3.0): classes become unary
predicates, properties binary relations, `rdf:type` becomes predicate
application, a typed literal `"sss"^^ddd` becomes the term
`LiteralValueOf('sss', TR[ddd])`, a blank node becomes a variable, and
an RDF graph becomes "the existential closure of the conjunction of
the translations of all the triples in the graph." The Note also names
its own limits (§4.0): no "propositional attitudes or true second
order constructs". It was never normative, never completed, and
never machine-checked.

**IKL** (Hayes/Menzel, IKRIS 2006; primary reference the IKL guide,
[https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html))
extends Common Logic (ISO/IEC 24707) with the proposition-forming
`(that S)` term — exactly the facility LBase §4.0 says LBase lacks.
This repository already formalizes the ISO/IEC 24707 §6.2/§6.3
interpretation and satisfaction clauses plus the IKL proposition
domain in
[`formal/lean4/L4Factoidal/CL/Semantics.lean`](../../formal/lean4/L4Factoidal/CL/Semantics.lean)
(tracking
[https://github.com/danbri/factoidal/issues/580](https://github.com/danbri/factoidal/issues/580)).

### The binding rule

The existing native Lean formalizations — the RDF model theory in
`RDF/Semantics.lean`, the decision procedures in `RDF/Entailment.lean`,
the closures in `RDFS/` and `OWL/`, the tableau in `OWL/Tableau.lean`,
the algebra in `SPARQL/Algebra.lean` — **remain ground truth**. The
unified theory is the checked common layer above them. At every stage,
adequacy of the translation is proved **in both directions** against
the native formalization of that language: the translation-based
entailment relation and the native relation pick out the same pairs,
as a Lean theorem with no `sorry`, no user `axiom`, no
`native_decide`, no `partial`. This is the relation LBase asserted and
never established: the Note's §3.0 table carries the caveat "this
should not be referred to as an accurate or normative semantic
description." Here the accuracy claim is the deliverable.

## 2. The interpretation structure

### 2.1 What is already there

`CL.Interp`
([`formal/lean4/L4Factoidal/CL/Semantics.lean`](../../formal/lean4/L4Factoidal/CL/Semantics.lean))
supplies:

* `dom : Type`, `domWit : dom` — one unsegregated universe of
  discourse (ISO/IEC 24707 §6.2), non-empty;
* `iName : String → dom` — every name denotes an individual;
* `iStr : String → dom` — quoted-string denotation;
* `rel : dom → List dom → Prop` — relation extension over finite
  sequences (variadic; arity is not fixed anywhere);
* `fn : dom → List dom → dom` — functional extension;
* `iProp : Sentence → (String → dom) → (String → List dom) → dom` —
  the IKL proposition domain: the individual a sentence expresses
  under a pair of valuations.

The `EntailsUnder (conds : Interp → Prop)` pattern — entailment
relative to a class of interpretations — is already the extension
mechanism in both `CL/Semantics.lean` and `RDF/Semantics.lean`.

### 2.2 The extension decision: conditions and schemas

The unified layer adds **no fields** to `CL.Interp`. Each language
embeds through (a) a translation into `CL.Sentence`, (b) an **axiom
schema** — a possibly-infinite set of sentences, LBase §2.4 style —
and (c) where a constraint is not expressible as object-language
sentences, an interpretation-class condition in the `EntailsUnder`
bundle. A schema is represented as a set:

```lean
/-- An axiom schema: a (possibly infinite) set of sentences.
LBase §2.4 axiom schemes; the rdf:_n families of RDF 1.1 Semantics
need exactly this. -/
abbrev Schema := CL.Sentence → Prop

def SatisfiesSchema (i : CL.Interp) (S : Schema) : Prop :=
  ∀ s, S s → CL.Satisfies i s

def EntailsSchema (conds : CL.Interp → Prop) (S : Schema)
    (premises : List CL.Sentence) (conclusion : CL.Sentence) : Prop :=
  ∀ i, conds i → SatisfiesSchema i S →
    CL.SatisfiesAll i premises → CL.Satisfies i conclusion
```

Every condition bundle gets a satisfiability witness and a
non-triviality witness, per the discipline of
`RDF/SemanticsHypothesisWitness.lean` and the witness section of
[`formal/lean4/L4Factoidal/OWL/Semantics.lean`](../../formal/lean4/L4Factoidal/OWL/Semantics.lean)
— a bundle nothing satisfies makes every `EntailsSchema` statement
vacuous, and a draft theorem with a false hypothesis has verified
cleanly in this repository before.

### 2.3 How RDF terms embed

Uniform translation of a triple to binary predication, with the
property term in operator position — legal because CL is unsegregated
(the same individual has a relation extension via `rel`):

* **IRI** `i : WfIri` → `CL.Term.name i.val`. The IRI string is the
  name; no encoding.
* **Literal** `l : WfLiteral` → the functional term
  `funapp (name "urn:cl:def:literalValueOf") [str lex, name dtIri]`
  (language-tagged strings carry the tag as a third argument). This
  is LBase §3.0's `LiteralValueOf('sss', TR[ddd])` made concrete
  under the `urn:cl:def:` vocabulary that
  [`formal/lean4/L4Factoidal/CL/ToRdf.lean`](../../formal/lean4/L4Factoidal/CL/ToRdf.lean)
  already owns. The D-schema (§5.1 below) constrains this operator.
* **Blank node** → an existentially bound name. Scoping rule, stated
  precisely: **the closure is taken once, at graph level** — RDF 1.1
  Semantics §5.2
  ([https://www.w3.org/TR/rdf11-mt/#simpleentailment](https://www.w3.org/TR/rdf11-mt/#simpleentailment))
  defines graph satisfaction as "[I+A](G) = true for some mapping A",
  one assignment for the whole graph, and LBase §3.0 translates a
  graph as "the existential closure of the conjunction". So
  `rdfToTheory g` is ONE sentence: `ex (bnode bindings) (conj atoms)`,
  never one sentence per triple. Consequences, to be proved as
  stage-1 lemmas:
  * union with shared labels shares scope:
    `rdfToTheory (g ++ h)` closes over `graphBnodeIds (g ++ h)` once,
    which is NOT in general entailment-equivalent to
    `conj [rdfToTheory g, rdfToTheory h]`;
  * merge (RDF 1.1 Semantics §4.1: union after standardizing apart)
    IS: `rdfToTheory (merge g h)` is entailment-equivalent to the
    conjunction of the two closures. `RDF/DatasetMerge.lean` holds
    the native standardize-apart machinery.

  Bound-name freshness: bnode bound names use the `_:` spelling by
  default, and the translation carries a freshness obligation — the
  chosen bound names are distinct from every IRI string occurring in
  the graph (an RFC 3986 IRI's scheme starts with a letter, so `_:`
  never collides with a parsed IRI, but `RDF.isIri` is looser than
  RFC 3986; the freshness lemma is stated against the graph's actual
  IRI strings, not against the grammar).
* **RDF 1.2 triple term** →
  `funapp (name "urn:cl:def:tripleTerm") [s, p, o]` — an
  uninterpreted function of the components' denotations, the same
  reading `RDF.Interp.iTt` gives it. This keeps the embedding total
  and lets stage 1 avoid the `GraphTtFree` hypotheses where the
  native tree needs them (`herbrand`'s constant `iTt` is the native
  quarantine point; the transport constructions in §4.1 carry the
  component-wise reading instead).

### 2.4 How datasets and named graphs embed

Following the conventions of
[`formal/lean4/L4Factoidal/CL/ToRdf.lean`](../../formal/lean4/L4Factoidal/CL/ToRdf.lean)
(propositions are named graphs; the default graph carries
decorations only) run in the opposite direction, and the
individuation rule of
[https://github.com/danbri/factoidal/issues/589](https://github.com/danbri/factoidal/issues/589):

* the **default graph** is asserted: `rdfToTheory ds.default` is a
  premise;
* each **named graph** `(n, G)` contributes ONE decoration sentence
  and asserts nothing about the world:
  `atom (name "urn:cl:def:names") [term n, that (rdfToTheory G)]` —
  the graph name denotes an individual standing in the naming
  relation to the proposition the graph's translation expresses.
  RDF 1.1 Concepts §4 deliberately gives datasets no entailment
  semantics; the decoration reading adds none.
* blank-node scope for a dataset is dataset-wide (RDF 1.1 Concepts
  §4: blank nodes may be shared between graphs of one dataset), so
  `datasetToTheory` closes existentially once, over the whole
  dataset, with the per-graph `that`-terms inside the closure. The
  proposition a shared-bnode graph expresses then depends on the
  ambient valuation — which is exactly why `iProp` takes the
  valuations as arguments (quantifying-in, `CL/Semantics.lean`
  module header).
* individuation: `iProp` is keyed on syntax, so proposition identity
  beyond syntactic identity is a CONDITION, not a structural fact.
  Stage 1 adds `PropAlphaInvariant : CL.Interp → Prop` (alpha-variant
  sentences express the same proposition — issue 589's semantic
  minimum, condition (1)); the stronger `=p` identities stay in the
  defined relation per issue 589 and are out of scope here.
* the `x-ikl-*` assertion rule
  ([`formal/lean4/L4Factoidal/CL/IklRegime.lean`](../../formal/lean4/L4Factoidal/CL/IklRegime.lean)):
  a default-graph `urn:cl:def:asserts` decoration of a proposition
  IRI corresponds, on the unified side, to the additional premise
  `atom (that (rdfToTheory G)) []` — IKL's assertion-as-zero-ary
  predication, tied to satisfaction by `IklRespectsThat`
  (`sat_assert_that`). The stage-6 regime theorem makes
  `IklRegime.extendDataset` adequate against exactly this reading.

### 2.5 Datatype maps

D-interpretations (RDF 1.1 Semantics §7,
[https://www.w3.org/TR/rdf11-mt/#datatype-entailment](https://www.w3.org/TR/rdf11-mt/#datatype-entailment))
enter as a schema-plus-condition pair parameterised by the recognised
set `D : List RDF.WfIri`, reusing the executable lexical-space and
value-space machinery of `RDF/Datatypes.lean`
(`literalIllFormed`, `valueInSpace`, `literalValueEq`):

* **value identification** (schema): for recognised `d` and lexical
  forms `s₁, s₂` with the same value under the tree's
  lexical-to-value mapping, the sentence
  `eq (literalTerm s₁ d) (literalTerm s₂ d)` — §7's "literals with
  the same value are interchangeable", the fact `Regime.literalEq`
  decides with `literalValueEq D`;
* **ill-typed exclusion** (schema): for each recognised `d` and each
  lexical form outside `d`'s lexical space, the sentence
  `neg (ex [x, r] (atom r [x, literalTerm s d]))` — no true
  predication holds of the ill-typed literal in object position.
  §5.5 below records why this encoding (rather than partial
  denotation) is the decided treatment and what it costs.

## 3. Per-language translation signatures

Signatures only; implementations are the stages' work. Namespace
`L4Factoidal.Unified` throughout. `RDF`, `RDFS`, `OWL`, `SPARQL`,
`RIF`, `CL` abbreviate the existing `L4Factoidal.*` namespaces.

```lean
/-! ## Stage 1 — RDF core + N-Quads -/

/-- A graph as ONE sentence: the existential closure, over the graph's
blank nodes, of the conjunction of one binary predication per triple
(LBase §3.0's last row; RDF 1.1 Semantics §5.2 graph satisfaction). -/
def rdfToTheory (g : RDF.Graph) : CL.Sentence

/-- The Skolem reading: blank nodes as free names, no closure
(RDF 1.1 Semantics §6). Used by BGP adequacy (stage 6), where answers
name the graph's own terms. -/
def rdfToTheorySk (g : RDF.Graph) : CL.Sentence

/-- A dataset: dataset-wide existential closure of the asserted
default-graph theory plus one `urn:cl:def:names` decoration per named
graph, the named graph's content under a `that`-term (§2.4). -/
def datasetToTheory (ds : RDF.Dataset) : CL.Sentence

/-- RDF axiomatic schema: the 8 finite axiomatic triples
(`RDF/VocabularyAxioms.rdfAxiomaticTriples`), the infinite rdf:_n
family, and the rdfD2-shaped typing rows for D
(https://www.w3.org/TR/rdf11-mt/#rdf-entailment). -/
def rdfSchema (D : List RDF.WfIri) : Schema

/-- D-interpretation schema: value identification + ill-typed
exclusion (§2.5). -/
def dSchema (D : List RDF.WfIri) : Schema

/-! ## Stage 2 — RDFS, ρdf, x-rdfscore -/

/-- RDFS axiom schema: the 38 finite RDFS axiomatic triples, the
rdf:_n container-membership families, and one universally quantified
sentence per RDFS semantic condition / entailment-rule row of RDF 1.1
Semantics §9 (https://www.w3.org/TR/rdf11-mt/#rdfs-entailment) —
e.g. rdfs9 as
`(forall (x a b) (if (and (rdfs:subClassOf a b) (rdf:type x a))
                     (rdf:type x b)))`.
Includes the type-application bridge
`(forall (x c) (iff (rdf:type x c) (c x)))` — LBase §2's reading of
rdf:type as predicate application, stated as an axiom rather than a
translation special case, which CL's unsegregated universe permits. -/
def rdfsSchema (D : List RDF.WfIri) : Schema

/-- The ρdf sub-schema: exactly the six rule rows of
`RDFS/Closure.lean` (rdfs2, rdfs3, rdfs5, rdfs7, rdfs9, rdfs11) —
no axiomatic triples, no reflexivity rows. -/
def rhoDfSchema : Schema

/-- The x-rdfscore regime's schema: rhoDfSchema (the regime closes
with `RDFS.closureFix`; `RDFS/RegimeDispatch.lean`). Named separately
so the regime table (stage 6) can cite it. -/
def rdfsCoreSchema : Schema

/-! ## Stage 3 — Datalog -/

/-- A Datalog atom over the unified vocabulary: predicate name applied
to variables/constants. No function symbols in derived positions. -/
structure DAtom where
  pred : String
  args : List DTerm

/-- A rule: definite Horn clause, NO existential variables in the
head (every head variable occurs in the body). rdfD1's surrogate
blank nodes are outside this class by construction — the same
exclusion `RDFS/FullClosure.lean` documents. -/
structure DRule where
  head : DAtom
  body : List DAtom

structure DatalogProgram where
  rules : List DRule

/-- Rules read as universally closed implications. -/
def DatalogProgram.toSchema (p : DatalogProgram) : Schema

/-- One materialisation step over a fact set, and the fuel-bounded
least fixpoint (the shape `RDFS/FixedPoint.lean` and the closures
already use). -/
def DatalogProgram.step (p : DatalogProgram) (facts : List DAtom) : List DAtom
def DatalogProgram.lfp  (p : DatalogProgram) (facts : List DAtom) (fuel : Nat) : List DAtom

/-! ## Stage 4 — OWL 2 RL -/

/-- One universally quantified Horn sentence (or sentence family, for
the list-valued rows) per OWL 2 RL/RDF rule-table row implemented in
`OWL/RLRules.lean` (https://www.w3.org/TR/owl2-profiles/#OWL_2_RL,
Tables 4-9), each carrying its row id. The sentences are the
object-language counterparts of the `Cond*` interpretation conditions
of `OWL/Semantics.lean`, and the stage proves that correspondence
(§4.4). -/
def owlRlSchema (D : List RDF.WfIri) : Schema

/-! ## Stage 5 — OWL DL, Direct Semantics, the tableau -/

/-- Class expression to open formula with one free name
(OWL 2 Direct Semantics Table 5,
https://www.w3.org/TR/owl2-direct-semantics/, restricted to the
fragment of `OWL/Tableau.lean`: names, Booleans, value restrictions,
qualified/unqualified cardinality — cardinality via equality and
pairwise distinctness, both first-order). -/
def conceptFormula (c : OWL.Concept) (x : String) : CL.Sentence

def assertionSentence  (φ : OWL.Assertion)  : CL.Sentence
def roleAxiomSentences (R : OWL.RoleAxioms) : List CL.Sentence

/-- The Direct Semantics route: ontology (tableau fragment) straight
to sentences. This mapping does NOT factor through RDF graphs — see
§5.3. -/
def owlDlDirect (R : OWL.RoleAxioms) (A : List OWL.Assertion) : List CL.Sentence

/-! ## RIF Core (in-repo; the issue's "etc.") -/

/-- RIF Core rules as universally closed implications over the same
triple predications, per the desugaring the RIF/RDF/OWL combination
specification fixes (https://www.w3.org/TR/rif-rdf-owl/ §5;
frames/member/subclass to triples as in `RIF/Translation.lean`).
Positional atoms of arity ≠ 2 reuse `RIF/Translation.lean`'s
documented encoding. -/
def rifCoreToTheory (rules : RIF.RuleSet) : List CL.Sentence

/-! ## Stage 6 — SPARQL 1.x -/

/-- A satisfaction query: distinguished variables plus an open body
sentence (variables as free names under a reserved `?`-prefix
spelling). -/
structure UQuery where
  vars : List SPARQL.VarName
  body : CL.Sentence

def sparqlBgpToQuery (b : SPARQL.Bgp) : UQuery

/-- The body with a solution mapping applied to its free variables. -/
def UQuery.instantiate (q : UQuery) (μ : SPARQL.Binding) : CL.Sentence

/-- μ answers q in a theory, under a condition bundle and schema. -/
def Answers (conds : CL.Interp → Prop) (S : Schema)
    (premises : List CL.Sentence) (q : UQuery) (μ : SPARQL.Binding) : Prop

/-- A regime string to its schema + condition bundle. Covers the
W3C-named regimes of `RDF.Entailment.Regime`, the experimental
x-rdfscore / x-rdfsplus of `RDFS/RegimeDispatch.lean`, and the
x-ikl-* family of `CL/IklRegime.lean`
(https://github.com/danbri/factoidal/issues/581). -/
def regimeToSchema (regime : String) (D : List RDF.WfIri) :
    Option (Schema × (CL.Interp → Prop))
```

## 4. Adequacy theorem statements per stage

Statements only, in the form each stage's gate checks. Each names the
native formalization it is proved against. `Unified.Entails` is
`CL.Entails`; `EntailsSchema` as in §2.2.

### 4.1 Stage 1 — RDF core + N-Quads

Proved against
[`formal/lean4/L4Factoidal/RDF/Semantics.lean`](../../formal/lean4/L4Factoidal/RDF/Semantics.lean)
and, through its `simpleEntails_iff_mt`, against the decision
procedure of
[`formal/lean4/L4Factoidal/RDF/Entailment.lean`](../../formal/lean4/L4Factoidal/RDF/Entailment.lean).
Mechanism: a transport pair —
`liftInterp : RDF.Interp → CL.Interp` (dom preserved; `rel` on the
denoted property restricted to 2-element sequences is `iext`;
`literalValueOf`/`tripleTerm` operators realised from `iLit`/`iTt`)
and `restrictInterp : CL.Interp → RDF.Interp`
(`iext p x y := rel (interp of p) [x, y]`) — with a satisfaction
transfer lemma in each direction.

```lean
/-- Stage 1 gate theorem. -/
theorem unified_adequate_simple (g h : RDF.Graph) :
    Unified.Entails [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.SimpleEntailsMt g h

/-- Corollary chain to the executable engine, via
`RDF.simpleEntails_iff_mt` (triple-term-free graphs, where the native
Herbrand construction applies). -/
theorem unified_adequate_simple_decided (g h : RDF.Graph)
    (hg : RDF.GraphTtFree g) (hh : RDF.GraphTtFree h) :
    Unified.Entails [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.simpleEntails g h = true

/-- Scoping lemmas (§2.3): merge is conjunction; shared-label union
is single-scope closure. Proved against `RDF/DatasetMerge.lean`. -/
theorem rdfToTheory_merge (g h : RDF.Graph) :
    EntailEquiv [rdfToTheory (RDF.merge g h)]
                [rdfToTheory g, rdfToTheory h]

/-- D-entailment. Proved against `RDF.Entailment.Regime.d`'s
components (`literalValueEq`, `literalIllFormed`,
`Regime.inconsistent`) and the D-clash module
`RDF/EntailmentRdfsDatatypeClash.lean`. -/
theorem unified_adequate_d (D : List RDF.WfIri) (g h : RDF.Graph) :
    EntailsSchema (fun _ => True) (dSchema D)
        [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.DEntailsMt D g h
```

(`RDF.DEntailsMt` is the model-theoretic D-entailment the stage also
introduces natively if it is not yet stated; the executable anchor is
`RDF.regimeEntails .d`.)

### 4.2 Stage 2 — RDFS + ρdf/x-rdfscore

Proved against `RDF/EntailmentRdfsModelTheory.lean` (soundness side)
and
[`formal/lean4/L4Factoidal/RDFS/RhoDfCompleteness.lean`](../../formal/lean4/L4Factoidal/RDFS/RhoDfCompleteness.lean)
(the ρdf completeness side, Herbrand construction).

```lean
/-- Soundness over the full RDFS schema: everything the native RDFS
closure emits is schema-entailed. Anchor: `RDFS.fullClosure` and the
per-row soundness of `RDF/EntailmentRdfsModelTheory.lean`. -/
theorem unified_rdfs_closure_sound (D : List RDF.WfIri) (g : RDF.Graph)
    (t : RDF.Triple) (h : t ∈ RDFS.fullClosure D cmps g) :
    EntailsSchema (fun _ => True) (rdfsSchema D)
      [rdfToTheory g] (rdfToTheory [t])

/-- Stage 2 gate theorem: on the ρdf model fragment, unified
entailment under the ρdf sub-schema coincides with ρdf entailment,
hence (by `RhoDfCompleteness`) with the executable
closure-then-instance decision. -/
theorem unified_adequate_rhoDf (g h : RDF.Graph)
    (hg : RDF.RhoDfModelFragGraph g) (hh : RDF.RhoDfModelFragGraph h) :
    EntailsSchema (fun _ => True) rhoDfSchema
        [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.RhoDfEntailsMt g h
```

Full-RDFS completeness is NOT claimed: `RhoDfCompleteness.lean`'s
Finding C-1 (the `rdfs:subClassOf` self-loop witness pair) shows RDFS
entailment differs from simple entailment of the closure even on the
fragment, so the completeness half is stated for ρdf/x-rdfscore
exactly as the native tree states it.

### 4.3 Stage 3 — Datalog

```lean
/-- The generic theorem, proved once: for a Datalog program and a
ground fact base, the fuel-adequate least fixpoint contains a ground
atom iff the program-as-schema plus facts entail it. Soundness is an
induction on `step`; completeness is the minimal-model (Herbrand)
argument, the same construction `RhoDfCompleteness` uses, done once
at the generic level. -/
theorem datalog_lfp_iff_entails (p : DatalogProgram)
    (facts : List DAtom) (a : DAtom) (hg : a.ground)
    (hfuel : FuelAdequate p facts fuel) :
    a ∈ p.lfp facts fuel
      ↔ EntailsSchema (fun _ => True) p.toSchema
          (facts.map DAtom.toSentence) a.toSentence

/-- Exhibits, one per closure engine: the ρdf closure
(`RDFS/Closure.lean`), the RDFS-Plus closure (`RDFS/RDFSPlus.lean`),
and the OWL RL closure's non-list core, each as a `DatalogProgram`
whose lfp agrees with the engine's output. -/
theorem rhoDfClosure_is_datalog (g : RDF.Graph) :
    (rhoDfProgram.lfp (factsOf g) fuel).toGraph = RDFS.closureFix g
```

### 4.4 Stage 4 — OWL 2 RL

Proved against
[`formal/lean4/L4Factoidal/OWL/RLTheorems.lean`](../../formal/lean4/L4Factoidal/OWL/RLTheorems.lean)
(T2 licensing / T4 fixpoint completeness over `OWL.RL.Derives`) and
[`formal/lean4/L4Factoidal/OWL/Semantics.lean`](../../formal/lean4/L4Factoidal/OWL/Semantics.lean)
(the `Cond*` interpretation conditions).

```lean
/-- The schema-to-condition correspondence, one lemma per row: a CL
interpretation satisfies the row's schema sentence iff its
restriction satisfies the row's `OWL.Cond*`. This is the bridge that
lets the unified layer reuse the native condition family. -/
theorem owlRl_row_condition (i : CL.Interp) (row : RlRowId) :
    CL.Satisfies i (owlRlSentence row) ↔ CondOf row (restrictInterp i)

/-- Stage 4 gate theorem, soundness: every triple the RL closure
emits is schema-entailed (via T2's `Derives` and per-row
truth-in-every-model over the schema). -/
theorem unified_owlRl_sound (D : List RDF.WfIri) (g : RDF.Graph)
    (t : RDF.Triple) (h : OWL.RL.Derives g t) :
    EntailsSchema (fun _ => True) (owlRlSchema D)
      [rdfToTheory g] (rdfToTheory [t])

/-- Completeness at the fragment: the closure is the Datalog decider
for the ground-atomic consequences of the schema (instantiating
stage 3's generic theorem through T4). -/
theorem unified_owlRl_complete_ground (D : List RDF.WfIri)
    (g : RDF.Graph) (t : RDF.Triple) (hsat : Saturated g fuel)
    (hcons : ¬ RlClash g)
    (h : EntailsSchema (fun _ => True) (owlRlSchema D)
           [rdfToTheory g] (rdfToTheory [t]))
    (hground : t.ground) :
    t ∈ OWL.RL.closure g fuel
```

Note the scope enlargement this stage carries: `RLTheorems.lean`
names truth preservation (the model-theoretic half) as NOT ported
from F\*. `unified_owlRl_sound` requires exactly that half; proving it
over the unified schema IS the port, and the stage is sized for it
(§7).

### 4.5 Stage 5 — OWL DL and the tableau

Proved against
[`formal/lean4/L4Factoidal/OWL/Tableau.lean`](../../formal/lean4/L4Factoidal/OWL/Tableau.lean)
(`Interp.sem`, `Refuted`) and
[`formal/lean4/L4Factoidal/OWL/TableauTheorems.lean`](../../formal/lean4/L4Factoidal/OWL/TableauTheorems.lean).

```lean
/-- Stage 5 gate theorem: Direct-Semantics satisfiability of the
tableau fragment coincides with unified-theory satisfiability of the
direct translation. -/
theorem unified_adequate_dl (R : OWL.RoleAxioms) (A : List OWL.Assertion) :
    (∃ i : CL.Interp,
        CL.SatisfiesAll i (owlDlDirect R A ++ roleAxiomSentences R))
      ↔ (∃ (δ : Type) (I : OWL.Interp δ) (ν : OWL.Ind → δ),
           OWL.RespectsRBox I R ∧ OWL.SatAll I ν A)

/-- The clash calculus against the unified theory: a refutation is a
proof of unified unsatisfiability (composes `TableauTheorems`
refutation soundness with the ← transport above). Relates the
three-valued verdict contract of
https://github.com/danbri/factoidal/issues/586: "inconsistent" =
unified-unsatisfiable; "consistent" (model built) =
unified-satisfiable; "unknown" claims nothing. -/
theorem refuted_unified_unsat (R : OWL.RoleAxioms) (A : List OWL.Assertion)
    (h : OWL.Refuted R A) :
    ¬ ∃ i : CL.Interp,
        CL.SatisfiesAll i (owlDlDirect R A ++ roleAxiomSentences R)
```

### 4.6 Stage 6 — SPARQL 1.x

Proved against
[`formal/lean4/L4Factoidal/SPARQL/Algebra.lean`](../../formal/lean4/L4Factoidal/SPARQL/Algebra.lean)
(`evalBgp`), `RDFS/RegimeDispatch.lean`, and `CL/IklRegime.lean`.

```lean
/-- BGP adequacy at the solution-mapping level, simple regime:
membership in the algebra's BGP answer set coincides with ground
entailment of the instantiated body from the Skolem reading of the
graph (§5.4 states the multiplicity delimitation). -/
theorem unified_adequate_bgp (b : SPARQL.Bgp) (g : RDF.Graph)
    (μ : SPARQL.Binding) :
    μ ∈ SPARQL.evalBgp b g
      ↔ (μ.domExact b ∧ μ.rangeIn g ∧
         Unified.Entails [rdfToTheorySk g]
           ((sparqlBgpToQuery b).instantiate μ))

/-- One theorem shape for regime soundness, instantiated per regime:
if `regimeToSchema r D = some (S, conds)`, then every solution the
regime's materialisation-based evaluator returns is an `Answers`
witness over the unified theory. Instances: simple, D, RDF, RDFS
(`RDF.Entailment.Regime`); x-rdfscore (with the ↔ form, via stage 2);
x-rdfsplus (soundness only — `RDFS/RegimeDispatch.lean` deliberately
does not claim chain-level completeness); x-ikl-* (against
`IklRegime.extendDataset`, under `IklRespectsThat` +
`PropAlphaInvariant`, with the assertion-decoration premise of
§2.4). -/
theorem regime_sound (r : String) (D : List RDF.WfIri)
    (hr : regimeToSchema r D = some (S, conds))
    (ds : RDF.Dataset) (b : SPARQL.Bgp) (μ : SPARQL.Binding)
    (h : μ ∈ regimeEval r D ds b) :
    Answers conds S [datasetToTheorySk ds] (sparqlBgpToQuery b) μ
```

### 4.7 RIF Core

```lean
/-- Agreement with the native forward-chaining engine
(`RIF/Engine.lean`): a fact the engine derives is entailed by the
rules-as-sentences plus the facts, and conversely on the ground
fragment via the stage 3 generic theorem (RIF Core rules are in the
Datalog class). -/
theorem unified_adequate_rifCore (rs : RIF.RuleSet) (g : RDF.Graph)
    (t : RDF.Triple) :
    t ∈ RIF.Engine.saturate rs g fuel
      ↔ EntailsSchema (fun _ => True) (fun s => s ∈ rifCoreToTheory rs)
          [rdfToTheorySk g] (rdfToTheory [t])
```

## 5. Hard points — decided treatments and their risks

### 5.1 D-entailment and ill-typed literals

RDF 1.1 Semantics §7.1: an ill-typed literal "cannot denote
anything", so any graph containing one is D-unsatisfiable. CL
totalises denotation — `iStr` and `fn` are total — so "no referent"
is not directly representable. **Decided treatment**: total
denotation plus the ill-typed **exclusion schema** (§2.5): for every
recognised-datatype ill-typed literal, an axiom that no predication
with it in object position is true. A translated graph containing
such a literal contradicts its own exclusion axiom, so the theory is
unsatisfiable and entails everything — the same extension of the
entailment relation §7.2 derives, and the same verdict
`Regime.inconsistent` computes. **Risk**: the encodings agree on
entailment between translated graphs, and the adequacy theorem
(4.1's `unified_adequate_d`) is exactly the check; but the ill-typed
literal's term still denotes an individual inside the model, so
statements the object language can make ABOUT that individual (e.g.
through `eq`) have no counterpart in the native semantics. The
schema must therefore stay silent about ill-typed terms beyond the
exclusion axioms; a value-identification axiom accidentally
quantifying over them would be unsound. The stage-1 witness file
carries a model separating the two readings to keep this visible.

### 5.2 Blank-node scoping across graph merge

**Decided treatment**: graph-level (and for datasets, dataset-level)
existential closure, §2.3/§2.4, with `rdfToTheory_merge` and the
shared-scope union lemma as proved facts rather than conventions.
**Risk**: the translation of a graph is not compositional
triple-by-triple — any lemma that decomposes a translated graph must
go through the closure. Mitigation: an unscoped body-level
translation (`rdfBody : Graph → CL.Sentence`, no closure) is the
recursion vehicle; `rdfToTheory` is `ex` over it; the native
blank-node locality lemmas (`RDF/Semantics.lean`,
`AssignmentsAgreeOn`) transport to valuation-locality on the CL side.

### 5.3 OWL's two semantics

OWL 2 has two model theories: Direct Semantics
([https://www.w3.org/TR/owl2-direct-semantics/](https://www.w3.org/TR/owl2-direct-semantics/)),
defined on the structural ontology, and RDF-Based Semantics
([https://www.w3.org/TR/owl2-rdf-based-semantics/](https://www.w3.org/TR/owl2-rdf-based-semantics/)),
defined on graphs. **Direct Semantics does not factor through RDF
graphs**: `owlDlDirect` maps the ontology (here, the tableau
fragment's `Concept`/`Assertion`/`RoleAxioms`) straight to sentences
— complement, disjunction and cardinality translate to `neg`/`disj`/
counting formulae, none of which is the translation of any RDF graph.
**Decided treatment**: the unified layer hosts BOTH routes side by
side over the same `CL.Interp`: `owlRlSchema` on the graph route
(stage 4), `owlDlDirect` on the structural route (stage 5). How they
relate: the OWL 2 correspondence theorem (OWL 2 RDF-Based Semantics
§7.2) states the entailment-preservation relation between the two on
mapped ontologies; this program does NOT undertake to machine-check
it. Within the tree the two routes meet only through test agreement
(the OWL suites both engines run). **Risk**: a reader may take the
shared universe as a claim that the routes agree; the LBase account
document (stage 7) states explicitly that no such theorem is proved
here.

### 5.4 SPARQL bag semantics versus set-based entailment

SPARQL 1.1 §18 evaluates to multisets; entailment is a relation, not
a counter. **Decided treatment**: the unified layer claims BGP
matching adequacy at the **solution-mapping level** — membership in
the answer set, theorem 4.6 — over the Skolem reading
`rdfToTheorySk` (RDF 1.1 Semantics §6; the SPARQL 1.1 Entailment
Regimes recommendation's answer-restriction conditions,
[https://www.w3.org/TR/sparql11-entailment/](https://www.w3.org/TR/sparql11-entailment/)
§2.1, restrict answers to terms of the queried graph for the same
finiteness reason). SELECT multiplicity — how many copies of μ appear
— is delegated entirely to the algebra formalization
(`SPARQL/Algebra.lean`'s list semantics and its refinement modules),
which is already the native authority for it. The unified layer makes
no multiplicity claim, and `Answers` is a `Prop`. **Risk**: none to
soundness; the delimitation must be restated wherever regime results
are reported, or a reader will take "adequate" to cover cardinality
of results. The stage-6 registry rows carry the delimitation in
their statement column.

### 5.5 Paradox and self-reference

IKL's `(that S)` admits self-referential and paradoxical texts.
**Decided treatment** — IKL's own (IKL guide, "IKL Overview" and
Appendix B): a paradoxical theory is simply unsatisfiable over the
coherent interpretations (`IklRespectsThat`); there is **no detection
obligation** — no syntactic paradox check, no truth-predicate
stratification. `IklEntails` from an unsatisfiable theory is the
everything-relation, which is the standing reading of inconsistency
everywhere else in the tree (RDF 1.1 Semantics §7.2's D-unsatisfiable
case). What MUST be proved so the condition class is not empty: a
coherent interpretation exists. Construction sketch, recorded here
because it is the one non-obvious obligation: build `dom` over a
syntactic universe containing proposition codes; define `rel` on a
code `⟨S, ν, σ⟩` applied to `[]` by strong induction on the size of
`S` — well-founded because `Sat` reaches `iProp` only through
`denotTerm`, which never recurses into satisfaction
(`CL/Semantics.lean` makes this structural on the term), and every
`that`-subterm carries a strictly smaller sentence. **Risk**: the
witness construction is the kind of fixed-point argument that fails
in formalisation for representation reasons rather than mathematical
ones; it is scheduled early in stage 6 (it gates every x-ikl claim)
and its failure mode is a smaller-than-planned interpretation class,
not unsoundness.

### 5.6 The Datalog fragment boundary

**Decided treatment**: `DRule` forbids existential head variables and
function symbols in derived positions (§3). This puts rdfD1's
surrogate blank nodes, `owl:someValuesFrom` witness generation, and
every comprehension-style rule outside the class — matching what the
native closures already exclude (`RDFS/FullClosure.lean` documents
the rdfD1 exclusion; the RL closure mints no witnesses,
`RDFS/RegimeDispatch.lean`). The generic completeness theorem (4.3)
is therefore about ground-atomic consequences only. **Risk**: the
phrase "closure engines as provably-complete fragment deciders" must
always name the fragment: ground-atomic consequences of a
definite-Horn schema. The x-rdfsplus regime illustrates the boundary
from the other side: `owl:sameAs` equality reasoning is in the
Datalog class as rules, but the native tree deliberately does not
claim chain-level completeness for it, and the unified layer inherits
exactly that claim level (4.6).

### 5.7 Infinite axiomatic families versus finite harvest

The rdf:_n axiomatic families are infinite; the native engines
harvest the finite `rdf:_n` slice occurring in the input
(`containerMembershipIn`, `RDF/Entailment.lean`), per the finite
enumeration recipe of RDF 1.1 Semantics Appendix A
([https://www.w3.org/TR/rdf11-mt/#entailment_rules](https://www.w3.org/TR/rdf11-mt/#entailment_rules)).
**Decided treatment**: the schemas state the infinite family
(`Schema` is a set, §2.2); the adequacy proofs carry a
finite-slice-suffices lemma — consequences mentioning only harvested
`rdf:_n` IRIs are derivable from the harvested instances. This lemma
exists nowhere in the tree yet and is new stage-2 work. **Risk**:
the lemma's statement must be careful about conclusions that mention
un-harvested members (Appendix A's step 2/3 rule is the guide); a
wrong statement here would be the classic vacuous-hypothesis failure,
so it gets a witness pair like every condition bundle.

## 6. Module layout and registry rows

### 6.1 `formal/lean4/L4Factoidal/Unified/`

| File | Contents (one line) |
|---|---|
| `Theory.lean` | `Schema`, `SatisfiesSchema`, `EntailsSchema`, `EntailEquiv`, condition-bundle composition |
| `Witnesses.lean` | satisfiability + non-triviality witnesses per condition bundle and schema (the `SemanticsHypothesisWitness` discipline) |
| `RdfEmbed.lean` | term/literal/triple-term encodings, `rdfBody`, `rdfToTheory`, `rdfToTheorySk`, freshness lemmas |
| `RdfTransport.lean` | `liftInterp` / `restrictInterp` and the satisfaction transfer lemmas |
| `RdfAdequacy.lean` | stage 1 theorems (4.1) incl. merge/union scoping |
| `DatasetEmbed.lean` | `datasetToTheory`, naming decorations, `PropAlphaInvariant`, N-Quads round-trip corollaries |
| `DSchema.lean` | `dSchema`: value identification + ill-typed exclusion; the separating model of §5.1 |
| `RdfsSchema.lean` | `rdfSchema`, `rdfsSchema`, `rhoDfSchema`, `rdfsCoreSchema`; finite-slice-suffices (§5.7) |
| `RdfsAdequacy.lean` | stage 2 theorems (4.2), Finding C-1 restated at the unified level |
| `Datalog.lean` | `DAtom`/`DRule`/`DatalogProgram`, `step`/`lfp`, `toSchema`, generic lfp-iff-entails (4.3) |
| `DatalogClosures.lean` | ρdf / RDFS-Plus / RL-core exhibits as programs; per-engine agreement theorems |
| `OwlRlSchema.lean` | `owlRlSchema` row sentences with row ids; row-to-`Cond*` correspondence lemmas (4.4) |
| `OwlRlAdequacy.lean` | stage 4 soundness + ground completeness |
| `OwlDlDirect.lean` | `conceptFormula`, `assertionSentence`, `roleAxiomSentences`, `owlDlDirect` |
| `OwlDlAdequacy.lean` | stage 5 satisfiability equivalence + refutation-to-unsatisfiability (4.5) |
| `RifEmbed.lean` | `rifCoreToTheory` + agreement with `RIF/Engine` (4.7) |
| `SparqlQuery.lean` | `UQuery`, `instantiate`, `Answers`, `sparqlBgpToQuery`, `regimeToSchema` |
| `SparqlAdequacy.lean` | stage 6 BGP adequacy + the one regime-soundness theorem shape and its instances |
| `IklWitness.lean` | the coherent-interpretation construction of §5.5 |
| `LBase.lean` | the machine-checked LBase account: the TR-table correspondence, documented deviations from the 2003 Note, stage 7's statement theorems |

### 6.2 Theorem-registry rows

[`docs/theorem-registry.md`](../theorem-registry.md) gains a section
"9. Unified model theory
([https://github.com/danbri/factoidal/issues/598](https://github.com/danbri/factoidal/issues/598))",
one row per gate theorem, columns matching the registry's existing
shape (theorem, module, native anchor, status):

| Stage | Rows added |
|---|---|
| 1 | `unified_adequate_simple`, `unified_adequate_simple_decided`, `rdfToTheory_merge`, `unified_adequate_d`, dataset embedding lemmas |
| 2 | `unified_rdfs_closure_sound`, `unified_adequate_rhoDf`, finite-slice-suffices |
| 3 | `datalog_lfp_iff_entails`, one exhibit row per closure engine |
| 4 | `owlRl_row_condition` (counted N of M rows, both labelled, per the registry's counting rules), `unified_owlRl_sound`, `unified_owlRl_complete_ground` |
| 5 | `unified_adequate_dl`, `refuted_unified_unsat` |
| 6 | `unified_adequate_bgp`, `regime_sound` + one row per regime instance |
| 7 | no new theorems; the account document and hub post cite the rows above |

Registry update lands in the same commit as each proof landing, per
the registry's own maintenance rule.

## 7. Stage plan, gates, sizes

Every stage's gate: (a) the stage's bidirectional adequacy theorems
against the named native formalization, (b) full `lake build` green,
(c) no `sorry` / no user `axiom` / no `partial` / no `native_decide`
(the standing policy of
[`skills/factoidal-lean-basics/SKILL.md`](../../skills/factoidal-lean-basics/SKILL.md)),
(d) theorem-registry rows in the same commit. Sizes: S ≈ one focused
session, M ≈ several sessions / one subagent wave, L ≈ multi-wave
with harvest cycles.

| Stage | Content | Size | What makes it that size |
|---|---|---|---|
| 0 | this document | S | reading-dominated |
| 1 | RDF core + N-Quads: `Theory`/`RdfEmbed`/`RdfTransport`/`RdfAdequacy`/`DatasetEmbed`/`DSchema` | **M** | the transport pair and transfer lemmas are new but small and definitional; the native interpolation lemma already connects to the decision procedure; care concentrates in the literal/triple-term encodings, the freshness lemmas, and the §5.1 separating model |
| 2 | RDFS + ρdf/x-rdfscore schemas and adequacy | **L** | one sentence-to-condition lemma per §9 row; the Herbrand completeness transport from `RhoDfCompleteness` (829 F\* lines' worth of argument re-targeted); the finite-slice-suffices lemma is new mathematics for this tree (§5.7) |
| 3 | Datalog class + generic lfp theorem + exhibits | **M** | the generic theorem is one Herbrand construction done once; exhibits are equation-chasing against existing `step` functions; `RDFS/FixedPoint.lean` is prior art |
| 4 | OWL 2 RL schema + adequacy | **L** | 50+ row sentences and row-condition lemmas; the truth-preservation half is NOT yet ported to Lean (`RLTheorems` names it) and this stage supplies it; list-valued rows (`SeqIs`) need sequence axioms in the schema |
| 5 | OWL DL direct + tableau relation | **M** | the tableau fragment is deliberately small; `TableauTheorems` soundness exists; the counting formulae for cardinality are fiddly but bounded; the model-built direction beyond `Refuted` tracks [https://github.com/danbri/factoidal/issues/586](https://github.com/danbri/factoidal/issues/586) and only its calculus-level relation is in scope here |
| 6 | SPARQL BGP + regimes (incl. x-ikl) | **L** | BGP adequacy over the Skolem reading; the regime theorem shape with seven instances; the §5.5 coherent-interpretation witness construction; dataset/GRAPH-pattern interaction with §2.4's decorations |
| 7 | the LBase account, written | **S** | document + hub post citing landed theorems; `Unified/LBase.lean` statement stubs land with stage 1 and grow per stage |

RIF Core (4.7) rides with stage 3 (its rules are in the Datalog
class); if it grows, it splits out as its own M stage between 3
and 4.

Ordering follows the issue's staging; stages 3 and 5 have no
dependency on each other and can run as parallel waves once stage 2
lands.

## 8. What this buys

Stated at the claim level each theorem supports, nothing above it:

1. **One semantic foundation under the parser/streaming theorems**
   ([https://github.com/danbri/factoidal/issues/576](https://github.com/danbri/factoidal/issues/576)).
   Today the N-Quads/Turtle round-trip theorems bottom out at graph
   equality or isomorphism; with stage 1 they compose with
   `unified_adequate_simple` so a parse-serialize cycle is provably
   meaning-preserving in one model theory, not per-format.
2. **Closure engines as provably-complete fragment deciders.** The
   ρdf, RDFS-Plus-core and RL-core closures become instances of one
   theorem (4.3): each is the least-fixpoint decider for the
   ground-atomic consequences of its schema fragment. Claim level per
   engine stays exactly what the native tree already claims (the
   x-rdfsplus completeness gap stays a gap).
3. **Regime soundness as one theorem shape.** Seven entailment
   regimes — the four W3C-named ones, x-rdfscore, x-rdfsplus, x-ikl-*
   — become instances of `regime_sound` (4.6) instead of seven
   unrelated arguments, and a future regime lands by supplying a
   schema + condition bundle + one instance proof.
4. **The first machine-checked LBase.** The 2003 Note's programme —
   translations, vocabulary axioms, one model theory — carried out
   with its adequacy proved instead of sketched, extended by the IKL
   proposition domain the Note itself listed as missing (§4.0), over
   the languages this repository implements. Stage 7's document
   states exactly which LBase table rows are realised, where the
   realisation deviates (e.g. uniform binary predication + the
   type-application axiom, in place of the Note's per-form
   translation), and which theorems back each row.

## References

* LBase: R. V. Guha, P. Hayes, *LBase: Semantics for Languages of the
  Semantic Web*, W3C Working Group Note, 10 October 2003 —
  [https://www.w3.org/TR/lbase/](https://www.w3.org/TR/lbase/)
  (§2 Outline of Approach; §2.4 Axiom Schemas; §2.5 Entailment; §3.0
  Using Lbase; §4.0 Inadequacies).
* RDF 1.1 Semantics, W3C Recommendation, 25 February 2014 —
  [https://www.w3.org/TR/rdf11-mt/](https://www.w3.org/TR/rdf11-mt/)
  (§4.1 merge; §5.2 simple entailment; §6 Skolemization; §7
  literals/D-interpretations; §8 RDF interpretations; §9 RDFS
  interpretations; Appendix A entailment rules and the axiomatic
  triple tables).
* SPARQL 1.1 Entailment Regimes, W3C Recommendation —
  [https://www.w3.org/TR/sparql11-entailment/](https://www.w3.org/TR/sparql11-entailment/).
* OWL 2 Direct Semantics —
  [https://www.w3.org/TR/owl2-direct-semantics/](https://www.w3.org/TR/owl2-direct-semantics/);
  OWL 2 RDF-Based Semantics (§7.2 correspondence theorem) —
  [https://www.w3.org/TR/owl2-rdf-based-semantics/](https://www.w3.org/TR/owl2-rdf-based-semantics/);
  OWL 2 Profiles (RL rule tables) —
  [https://www.w3.org/TR/owl2-profiles/](https://www.w3.org/TR/owl2-profiles/).
* RIF RDF and OWL Compatibility (§5) —
  [https://www.w3.org/TR/rif-rdf-owl/](https://www.w3.org/TR/rif-rdf-owl/).
* ISO/IEC 24707, Common Logic; IKL guide —
  [https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html).
* ρdf: S. Muñoz, J. Pérez, C. Gutierrez, *Simple and Efficient
  Minimal RDFS*, Journal of Web Semantics 7(3), 2009.
* Issues:
  [https://github.com/danbri/factoidal/issues/598](https://github.com/danbri/factoidal/issues/598)
  (this programme),
  [https://github.com/danbri/factoidal/issues/580](https://github.com/danbri/factoidal/issues/580)
  (CL/IKL),
  [https://github.com/danbri/factoidal/issues/581](https://github.com/danbri/factoidal/issues/581)
  (x-ikl regimes),
  [https://github.com/danbri/factoidal/issues/589](https://github.com/danbri/factoidal/issues/589)
  (proposition individuation),
  [https://github.com/danbri/factoidal/issues/586](https://github.com/danbri/factoidal/issues/586)
  (tableau verdicts),
  [https://github.com/danbri/factoidal/issues/576](https://github.com/danbri/factoidal/issues/576)
  (parser/streaming theorems).
