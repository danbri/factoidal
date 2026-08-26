# 2026-08-26 — The LBase account: what the unified-semantics program proved

Stage 7 (final) of
[https://github.com/danbri/factoidal/issues/598](https://github.com/danbri/factoidal/issues/598).
No new theorems land with this document. Every statement below is
quoted from, or checkable against, the Lean source in
`formal/lean4/L4Factoidal/Unified/` and `formal/lean4/L4Factoidal/OWL/`,
the registry rows of
[`docs/theorem-registry.md`](../theorem-registry.md) section 9, and the
design document with its 32 correction notes,
[`docs/designissues/2026-08-25-unified-semantics-lean.md`](2026-08-25-unified-semantics-lean.md).

Public version of the same material: hub post 43,
[`docs/web/hub/43-one-model-theory-under-all-of-it.md`](../web/hub/43-one-model-theory-under-all-of-it.md).

---

## 1. What was built, and why

### 1.1 The direction

Owner direction (2026-08-25, verbatim, from
[https://github.com/danbri/factoidal/issues/598](https://github.com/danbri/factoidal/issues/598)):

> "Do it, with ultimate integration of all the semantic languages we
> implement here including rdf core semantics, rdfs, rhoDF/rdfscore,
> owl rl, owl dl tableaux, sparql 1.x, nquads etc. Throw in an lbase
> and datalog if you like just bind it all together in lean deeply. We
> want more than previously merely using f+ as a vibe coding
> functional language. Lean-backed lbase ikl gives a unifying account
> of w3c logical assertion and querying and logic languages."

### 1.2 The lineage

**LBase** (R. V. Guha and Patrick Hayes, *LBase: Semantics for
Languages of the Semantic Web*, W3C Working Group Note, 10 October
2003, [https://www.w3.org/TR/lbase/](https://www.w3.org/TR/lbase/))
proposed one first-order base language into which each Semantic Web
language translates, so that "the model theory of Lbase is the model
theory of all the Semantic Web Languages" (§2). Its §3.0 recipe has
three parts: a translation procedure per language, a vocabulary set,
and axioms or axiom schemas constraining that vocabulary. The Note
carries its own caveat on the RDF translation table — "this should not
be referred to as an accurate or normative semantic description" — and
names in §4.0 what it cannot express: "propositional attitudes or true
second order constructs".

**IKL** (Patrick Hayes and Christopher Menzel, IKRIS 2006; guide at
[https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html))
extends Common Logic (ISO/IEC 24707) with the proposition-forming
`(that S)` term — the facility LBase §4.0 records as missing. This
repository formalizes the ISO/IEC 24707 §6.2/§6.3 interpretation and
satisfaction clauses plus the IKL proposition domain in
[`formal/lean4/L4Factoidal/CL/Semantics.lean`](../../formal/lean4/L4Factoidal/CL/Semantics.lean)
([https://github.com/danbri/factoidal/issues/580](https://github.com/danbri/factoidal/issues/580)).

The unified layer is that programme carried out in Lean 4: one
`CL.Interp` (ISO/IEC 24707 §6.2, unsegregated universe), one
`Unified.Schema` (LBase §2.4 axiom schemas, represented as a set of
sentences), one `EntailsSchema` relation, and one translation per
language.

**On priority.** LBase was never completed and never machine-checked;
that is checkable from the Note itself. Whether some other project has
since machine-checked a comparable unifying account is not a fact this
repository can verify, so this document does not make a priority
claim. What it claims is stated in section 2: for each language in
this tree, a Lean theorem relating translation-based entailment to the
native formalization, at the exact strength listed.

### 1.3 The binding rule

The native Lean formalizations remain ground truth: the RDF model
theory in `RDF/Semantics.lean`, the decision procedures in
`RDF/Entailment.lean`, the closures in `RDFS/` and `OWL/`, the tableau
in `OWL/Tableau.lean`, the algebra in `SPARQL/Algebra.lean`. The
unified theory is a layer above them, and each stage's gate theorem
relates the two **in both directions** wherever both directions hold.
Where only one direction holds, the other is recorded as a gap in the
registry and in section 2 below.

Every module carries the standing Lean policy of this tree: no
`sorry`, no user `axiom`, no `partial`, no `native_decide`. The axiom
audit on every gate theorem, recorded in-source with `#print axioms`,
reports `propext`, `Classical.choice`, `Quot.sound` only.

### 1.4 Size

| Location | Modules | Lines |
|---|---|---|
| `formal/lean4/L4Factoidal/Unified/` | 17 | 11,906 |
| `formal/lean4/L4Factoidal/OWL/RLSemantics.lean`, `OWL/RLHerbrand.lean` | 2 | 3,725 |
| Total | 19 | 15,631 |

`OWL/RLSemantics.lean` supplies the model-theoretic truth layer that
`OWL/RLTheorems.lean` had recorded as not ported since it was written.
Stage 4's soundness gate needs that layer, so proving the gate was
the port.

---

## 2. The results

One row per gate theorem. Statements are quoted from the Lean source
as landed. Strength is stated with no rounding: "full iff, no side
conditions" only where the theorem carries none.

### 2.1 Stage 1 — RDF core, datasets, N-Quads

`Unified/Theory.lean`, `Witnesses.lean`, `RdfEmbed.lean`,
`RdfTransport.lean`, `RdfAdequacy.lean`, `DatasetEmbed.lean`.

```lean
theorem unified_adequate_simple (g h : RDF.Graph) :
    Entails [rdfToTheory g] (rdfToTheory h) ↔ RDF.SimpleEntailsMt g h
```

**Strength: full iff, no side conditions.** No triple-term-freedom
hypothesis: both sides read an RDF 1.2 triple term as the same
uninterpreted function of its components' denotations.

```lean
theorem unified_adequate_simple_decided (g h : RDF.Graph)
    (hg : RDF.GraphTtFree g) (hh : RDF.GraphTtFree h) :
    Entails [rdfToTheory g] (rdfToTheory h) ↔
      RDF.simpleEntails g h = true
```

**Strength: full iff under two hypotheses** — triple-term-freedom on
both graphs, which is where the native Herbrand construction applies.

Also landed: `rdfToTheory_merge` (satisfaction-equivalence, stronger
than mutual entailment), `union_shared_scope_strict` (the converse
REFUTED on a witness pair), the transport pair's transfer lemmas as a
full iff each, `bnodeName_ne_iri` (bound-name freshness against every
well-formed IRI, unconditional), and the dataset decoration lemmas
including `dataset_decoration_asserts_nothing`.

**Named gaps at stage 1.** The N-Quads round-trip corollary is blocked:
the tree's parser round-trip theorem covers only the empty graph
([https://github.com/danbri/factoidal/issues/576](https://github.com/danbri/factoidal/issues/576)).

### 2.2 D-entailment (RDF 1.1 Semantics §7 / RDF 1.2 Semantics WD §5, §7.1)

`Unified/DSchema.lean`.

```lean
theorem unified_adequate_d (D : List RDF.WfIri) (g h : RDF.Graph) :
    EntailsSchema condTrue (dSchema D) [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.DEntailsMt D g h
```

**Strength: full iff, no side conditions, any `D`, any graphs.** The
native anchor `RDF.DEntailsMt` did not exist before this landing and is
introduced with it: `RDF/EntailmentTheorems.lean` deliberately gives
the `literalValueEq` regime variants no soundness theorem.

```lean
theorem unified_adequate_d_decided_sound (D : List RDF.WfIri)
    (g h : RDF.Graph) (he : RDF.regimeEntails .d D g h = true) :
    EntailsSchema condTrue (dSchema D) [rdfToTheory g] (rdfToTheory h)
```

**Strength: soundness only, unconditional.** The complete half —
`RDF.DEntailsMt D g h → regimeEntails .d D g h = true` — is a named
open lemma pair: a D-Herbrand interpretation quotienting literals by
`literalValueEq D`, plus completeness of `searchInstance` under the
regime's restricted `Regime.bindable`.

### 2.3 Stage 2 — RDF, RDFS, ρdf, x-rdfscore, RDFS+D

`Unified/RhoDfSchema.lean`, `Unified/RdfsSchema.lean`.

```lean
theorem unified_adequate_rhoDf (g h : RDF.Graph) :
    EntailsSchema condTrue rhoDfSchema [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.RhoDfEntails g h
```

**Strength: full iff, unconditional** — stronger than the design
document's §4.2 statement, which carried `RhoDfModelFragGraph`
hypotheses (correction note 8).

```lean
theorem unified_adequate_rhoDf_decided (g h : RDF.Graph) (fuel : Nat)
    (hclosed : RDF.RhoDfClosed (RDFS.closure g fuel))
    (hf : RDF.RhoDfModelFragGraph (RDFS.closure g fuel))
    (hfe : RDF.GraphTtFree h) :
    EntailsSchema condTrue rhoDfSchema [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.simpleEntails (RDFS.closure g fuel) h = true
```

**Strength: full iff under three hypotheses**, each with an executable
sufficient check (`rhoDfClosedCheck`, `RDFS.isRhoDfFrag`) dischargeable
by `decide` on concrete inputs; the instance `unified_rhoDf_demo`
discharges all three.

```lean
theorem unified_adequate_rdfs (Dset : RDF.DatatypeSet) (g h : RDF.Graph) :
    EntailsSchema condTrue (rdfsSchema Dset) [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.RdfsEntails Dset g h
```

**Strength: full iff, unconditional, every `Dset`.** The design
document predicted soundness only, citing Finding C-1; C-1 blocks the
EXECUTABLE characterisation, not model-theoretic adequacy (correction
note 9a). `unified_adequate_rdf` and `unified_adequate_rdfs_d` land at
the same strength against `RDF.RdfEntails` and `RDF.RdfsDEntailsMt`.

```lean
theorem unified_rdfs_closure_sound (D cmps : List RDF.WfIri)
    (hcmps : ∀ c ∈ cmps, RDF.IsRdfMemberIri c)
    (hxml : RDF.rdfXMLLiteral ∈ D) (g : RDF.Graph)
    {t : RDF.Triple} (ht : t ∈ RDFS.fullClosure D cmps g) :
    EntailsSchema condTrue (rdfsSchema (fun x => x ∈ D))
      [rdfToTheory g] (rdfToTheory [t])
```

**Strength: soundness only, under two hypotheses.** The
`rdf:XMLLiteral ∈ D` hypothesis is a recorded weakening, not a
convenience: the engine's 40-row seed table contains two
`rdf:XMLLiteral` rows that RDF 1.1 Semantics §9.3's 38-row table does
not list (recognition of `rdf:XMLLiteral` is optional there).

**Named gaps at stage 2.**
* Finite-slice-suffices (design §5.7) is NOT proved. No landed theorem
  consumes it: the schemas index their axiom rows by the native
  predicates carrying the full infinite `rdf:_n` families, so both
  sides of every gate iff quantify over the same family.
* RDFS+D satisfiability for nonempty `D` is not proved; the witnesses
  are stated at `D = []`.
* No decided RDFS corollary. Finding C-1's witness pair is restated at
  the unified level: `rhoDf_not_entails_selfLoop_unified` versus
  `rdfs_entails_selfLoop_unified`, which is also the strictness witness
  between the two schemas.

### 2.4 Stage 3 — Datalog as the computable-fragment class

`Unified/Datalog.lean`, `Unified/DatalogClosures.lean`.

```lean
theorem datalog_lfp_iff_entails (p : DatalogProgram) {facts : List DAtom}
    {fuel : Nat} {a : DAtom} (hgf : ∀ b ∈ facts, b.groundB = true)
    (hg : a.groundB = true) (hfa : p.FuelAdequate facts fuel) :
    a ∈ p.lfp facts fuel ↔
      EntailsSchema condTrue p.toSchema (facts.map DAtom.sentence)
        a.sentence
```

**Strength: full iff for GROUND-ATOMIC consequences**, under ground
facts, a ground query atom, and fuel adequacy (executable check
`saturatedCheck`, `decide`-dischargeable). Soundness
(`datalog_lfp_sound`) is unconditional at any fuel.

Existential heads are unwritable by construction: `DatalogProgram`
carries well-formedness as a proof field, and `rdfD1Shape_not_wf` pins
that a witness-minting rule shape fails the gate.

```lean
theorem rhoDf_engine_iff_datalog_entails (g : Graph) (n m : Nat)
    (hcl : RDF.rhoDfClosedCheck (RDFS.closure g m) = true)
    (hf : RDFS.isRhoDfFrag (RDFS.closure g m) = true)
    (hfa : rhoDfProgram.FuelAdequate (graphFacts g) n)
    (t : Triple) (hto : RDF.RhoDfModelObjectOk t.o) :
    t ∈ RDFS.closure g m ↔
      EntailsSchema condTrue rhoDfProgram.toSchema
        ((graphFacts g).map DAtom.sentence) (tripleFact t).sentence
```

**Strength: full iff under four hypotheses**, three of them
`decide`-dischargeable. This is "closure engines as provably-complete
fragment deciders" at the level the phrase can carry: ground-atomic
consequences of a definite-Horn schema, on the ρdf model fragment.

**Named gaps at stage 3.**
* The RDFS-Plus tier (`rdfsPlusProgram`) agrees with
  `RDFS.rdfsPlusClosure` at **demo-instance strength only** — one
  `decide`d theorem on the TransitiveProperty demo, `#guard` pins on
  the sameAs and inverseOf demos. A general bridging theorem is not
  claimed: the native tier claims no chain-level completeness, and the
  engine's per-row IRI-subject guards restrict firings the Datalog
  rules do not.
* RIF Core (design §4.7) was never dispatched. The n-ary machinery it
  needs has been landed and generic since stage 3;
  `unified_adequate_rifCore` does not exist.

### 2.5 Stage 4 — OWL 2 RL

`OWL/RLSemantics.lean`, `OWL/RLHerbrand.lean`,
`Unified/OwlRlSchema.lean`, `Unified/OwlRlAdequacy.lean`.

```lean
theorem unified_owlRl_sound {g : RDF.Graph} {t : RDF.Triple}
    (hres : RlReservedFree g) (h : OWL.RL.Derives g t) :
    EntailsSchema OwlRlInterpCond owlRlSchema [rdfToTheory g] (rdfToTheory [t])
```

**Strength: soundness only, under `RlReservedFree g`.** That hypothesis
cannot be dropped: a graph using the reserved comprehension labels can
make the engine conflate a user blank node with a comprehension
witness, and soundness fails there. The
conclusion is the EXISTENTIAL closure `rdfToTheory [t]` because the
comprehension rows mint blank nodes.

The schema has 91 rows: 66 plain Horn rows indexed by `RlRowId`, 5
guarded or table-indexed families, 10 clash rows and families as
falsity-headed `DNeg` sentences, and 9 rows carried by the
interpretation-class condition `OwlRlInterpCond` — which is named in
the theorem statement, so the boundary is visible in the gate.

```lean
theorem owlRl_complete_ground {c : RDF.Graph}
    (hcut : ∀ {u : RDF.Triple}, OWL.RL.Derives c u → u ∈ c)
    (hfrag : RlHerbFrag c) (hcons : ¬ OWL.RL.Clash c)
    {t : RDF.Triple} (hp : rlReservedIri t.p = false)
    (htt : RDF.TermTtFree t.o) (hgr : RDF.tripleBnodes t = [])
    (h : OwlRlEntailsMt c [t]) : t ∈ c
```

**Strength: condition-bundle form only.** `OwlRlEntailsMt` quantifies
over `RDF.Interp` meeting `RlConditions` and `RlClashConditions`. The
schema-relative form — the same statement over
`EntailsSchema … owlRlSchema` — is NOT proved: `liftInterp` reads a
binary predication as `r.iext p.2 x.2 y.2`, so satisfaction quantifies
the predicate position over the whole domain where `RlCond*` quantifies
over `WfIri`. That reading is true for `rlHerb c`, but establishing it
is a second pass over all 79 rows, not a corollary (correction note 19).

**Named gaps at stage 4.**
* Nine rows are outside the schema, each for a structural reason:
  prp-spo2 and prp-key (ternary premise relation against binary
  `iext`); cls-maxc2, cls-maxc1, cls-maxqc1, cls-maxqc2 (a cardinality
  literal embeds as a `funapp`, not a `DTerm`); cax-dw-comp,
  cls-maxqc1-comp, minc1-comp (existential heads).
* The completeness fragment `RlHerbFrag` is narrow. Clause (a) — every
  object an IRI or a blank node — excludes every graph whose closure
  carries a cardinality literal, and the minc1 comprehension row emits
  `owl:minCardinality "1"` for each `owl:ObjectProperty` declaration.
  So the completeness direction does not reach ontologies that declare
  object properties.
* Three clash rows (cls-maxc1, cls-maxqc1, cls-maxqc2) hold VACUOUSLY
  on the fragment: their premise needs a literal object that clause (a)
  forbids. Stated in the module header and the registry.

### 2.6 Stage 5 — OWL 2 Direct Semantics and the tableau

`Unified/OwlDlDirect.lean`, `Unified/OwlDlAdequacy.lean`.

```lean
theorem unified_adequate_dl (R : OWL.RoleAxioms) (A : List OWL.Assertion) :
    (∃ i : CL.Interp, CL.SatisfiesAll i (owlDlDirect R A)) ↔
      OWL.Consistent R A
```

**Strength: full iff, no side conditions.** No fragment hypothesis
appears because `OWL.Concept` / `OWL.Assertion` / `OWL.RoleAxioms` ARE
the fragment: the SHIQ fragment of `OWL/Tableau.lean`. Equality enters
the unified theory here for the first time; cardinality translates to
a first-order counting formula over a sum domain `δ ⊕ String`, chosen
because stage 1's tag-product domain is unsound for counting
(correction note 23).

```lean
theorem refuted_unified_unsat {R : OWL.RoleAxioms} {A : List OWL.Assertion}
    (h : OWL.Refuted R A) :
    ¬ ∃ i : CL.Interp, CL.SatisfiesAll i (owlDlDirect R A)
```

**Strength: soundness only.** The converse
`¬ OWL.Consistent R A → OWL.Refuted R A` is not derivable here:
`OWL/Tableau.lean`'s `Refuted` has no blocking condition and no
⊔-saturation strategy, and `OWL/TableauTheorems.lean` proves soundness
only.

**Named gaps at stage 5.**
* Tableau completeness: open.
* Fragment boundary: nominals, datatypes and data properties,
  functional and inverse-functional roles, inverse roles, role chains,
  reflexive/irreflexive/asymmetric/disjoint role axioms, `Self`
  restrictions, and every TBox axiom other than the role box are
  outside `OWL.Concept` / `OWL.Assertion`.
* The DL-species guard does not attach: `OWL/SyntaxDL.lean`'s
  `speciesIsDl` takes RDF graphs, the Direct-Semantics route does not
  factor through graphs, and the tree has no reader from `Graph` to
  `List OWL.Assertion` (correction note 25).
* Direct versus RDF-Based correspondence (OWL 2 RDF-Based Semantics
  §7.2): NOT machine-checked. The two routes sit side by side over the
  same `CL.Interp` and are related here by nothing but that shared
  universe.

### 2.7 Stage 6 — SPARQL 1.x basic graph patterns and the regimes

`Unified/SparqlQuery.lean`, `Unified/SparqlAdequacy.lean`.

```lean
theorem unified_adequate_bgp (b : SPARQL.Bgp) (g : RDF.Graph)
    (mu : SPARQL.Binding) (hg : RDF.GraphTtFree g) (hb : BgpTtFree b) :
    BgpMatches mu b g ↔
      Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b) mu
```

**Strength: full iff between the PIVOT `BgpMatches` and `Answers`,
under two triple-term-freedom hypotheses as landed.** The forward
direction is separately available with no hypotheses at all
(`bgp_matches_answers`); the two guards are what the reflection
argument for the reverse direction needs, since the term model gives
every triple term one quarantine constant. No domain hypothesis on
`mu`: an unbound variable is refuted by the model, not excluded by
assumption.

The design document's single membership iff `μ ∈ evalBgp b g ↔ …`
cannot be proved and is withdrawn (correction note 27). Two properties
of `evalBgp`'s result are invisible to any semantic condition: the
ORDER in which the evaluator conses bindings, and the COARSENESS of
`tryBindTerm`'s already-bound arm, which compares with `RDF.Term.eqb`.
The engine sides of the gate are therefore:

* `bgp_eval_sound` — `mu ∈ SPARQL.evalBgp b g → BgpMatches mu b g`,
  unconditional;
* `bgp_eval_complete` — under `BgpTtFree b`, a mapping that matches has
  a counterpart the evaluator RETURNS, agreeing on every pattern
  variable **up to `Term.eqb`** — agreement, not membership.

**Three delimitations carried by every stage 6 row.**
1. **SPARQL 1.1 §18.3.1.** The engine matches a pattern blank node as a
   constant with that label; the specification's pattern instance
   mapping makes it a non-distinguished variable
   ([https://github.com/danbri/factoidal/issues/607](https://github.com/danbri/factoidal/issues/607)).
   The narrowing agrees with the Skolem reading, so the gate is a full
   iff — but on a blank-node-carrying pattern it is adequate TO THE
   ENGINE, not to the specification. `unified_adequate_bgp_bnodeFree`
   is the corollary on the fragment where the two readings coincide.
2. **No multiplicity claim.** `Answers` is a `Prop`; the evaluator side
   is membership.
3. **`RDF.Term.eqb` is coarser than syntactic identity** (language-tag
   case, `rdf:XMLLiteral` canonical XML), and `Graph.mem` is stated
   over it, so answers are evaluated under `termEqSchema` — one `eq`
   row per `Term.eqb`-equal pair, the same LBase §2.4 axiom-schema
   device the D-entailment value rows use.

Regime results:

| Regime | Theorem | Strength |
|---|---|---|
| the shape, once | `regime_sound_of_closureHolds` | soundness; the premise is the regime's own content |
| `simple` | `regime_sound_simple` | soundness, no hypotheses |
| `x-rdfscore` | `regime_sound_rhoDf` | soundness, no hypotheses |
| `x-rdfscore` | `regime_rhoDf_answers_closure_iff` | full iff — the MATERIALISATION is answer-preserving |
| `RDFS` | `regime_sound_rdfs` | soundness, under `IsRdfMemberIri` on the harvested members and `rdf:XMLLiteral ∈ D` |
| `x-ikl-*` | `ikl_extend_entailed`, `regime_sound_ikl` | soundness, unconditional, suffix-independent |
| `x-rdfsplus` | — | NO theorem |

**Named gaps at stage 6.**
* `x-rdfsplus` has no closure-soundness theorem to supply
  `regime_sound_of_closureHolds`'s premise: stage 3 landed that tier at
  demo-instance strength, and `RDFS/RegimeDispatch.lean` already
  refuses chain-level completeness for it because `owl:sameAs` breaks
  the Herbrand construction.
* `regime_rhoDf_answers_closure_iff` is answer-preservation of the
  materialisation, NOT "the engine returns every ρdf answer" — the
  latter needs the closure to be saturated.
* The engine's regime dispatcher is narrower than the regime table:
  `RDFS.entailmentClosureForQueryExt` recognises `x-rdfscore` and
  `x-rdfsplus` and routes every other string — `"RDFS"` and `"OWL-RL"`
  included — to `OWL.RL.closure`. A `#guard` pins the disagreement.
* The `x-ikl-*` merge is not proved CONSERVATIVE: no landed theorem
  ties the `urn:cl:def:asserts` decoration to `CL.IklRespectsThat`.
  Named subsets stay deferred to
  [https://github.com/danbri/factoidal/issues/581](https://github.com/danbri/factoidal/issues/581).

---

## 3. What the programme found

The proof work produced defect findings in code that was already
shipping and already green. Each item below states what it cost and how
it was found.

### 3.1 The D-semantics divergence, and the wrong first attribution

[https://github.com/danbri/factoidal/issues/602](https://github.com/danbri/factoidal/issues/602),
hazard #33 in
[`skills/workflow-gotchas-debugging/SKILL.md`](../../skills/workflow-gotchas-debugging/SKILL.md).

**Found by:** attempting the decided corollary of `unified_adequate_d`.
The corollary was false, and the theorem `dEntailsMt_tt_gap` plus a
`#guard` pinned the disagreeing pair: on
`:a :p <<( :a :q "yes"^^xsd:boolean )>>`, the executable D-regime
answered inconsistent (so entails everything) and the model theory
answered satisfiable.

**The first attribution was wrong.** The issue blamed the executable
collector. The spec anchor decides against that reading: RDF 1.2
Semantics Working Draft (7 April 2026,
[https://www.w3.org/TR/rdf12-semantics/](https://www.w3.org/TR/rdf12-semantics/))
§5's compositional triple-term denotation `I(E) = IT(I(E.s), I(E.p),
I(E.o))` composed with §7.1, and the W3C rdf12 `malformed-literal`
test's own manifest comment, "Malformed literals are allowed in triple
terms, but cause inconsistency". The defective layer was the totalized
model theory, whose exclusion clause was top-level only.

**Cost:** a wrong fix direction stood in an open issue with owner
visibility; the model-theory defect was pinned in-source as a theorem
whose name blamed the executable; one session-day of repair had to
begin by re-deciding the spec anchor.

**Repair:** `RDF.DInterpCond` clause 2 and `dExclusionSchema` now
exclude every term with an ill-typed MENTION, interiors included;
`dEntailsMt_tt_gap` was removed and its content preserved truthfully as
`topLevel_exclusion_insufficient_for_tt` over the superseded bundle;
the flipped pin `dEntailsMt_tt_illtyped` failed before the repair and
passes after it. Canonical collectors `Term.assertedLiterals` /
`Term.mentionedLiterals` landed with no catch-all `_` arms, each citing
its WD clause.

**The systemic cause, as the post-mortem states it:** the tree
implements one term type for two specifications. The term type is RDF
1.2-shaped; the semantics modules cited RDF 1.1 Semantics §7, which has
no triple-term clause. Every fold over the term type that feeds a
verdict therefore contained a decision its cited spec could not answer,
and each fold decided independently — within one module, across
modules, and across the two engine trees.

### 3.2 A suite that had never loaded

[https://github.com/danbri/factoidal/issues/605](https://github.com/danbri/factoidal/issues/605).

**Found by:** the 602 repair, which had to restore test pressure before
it could choose a spec anchor. The rdf12 `rdf-semantics` manifest had
never loaded in the Lean harness: an upstream commit added an entry
using an undeclared `test:` prefix, `Harness/Manifest.lean` parsed
strictly, and every umbrella run reported **0 pass, 0 fail (out of 0)**
with `no_manifest=1`. That diagnostic printed for two months and
nothing escalated it.

**First run after the lenient-with-report parse: 19 pass, 11 fail,
0 skip, 17 unsupported (out of 47).** It exposed 9 engine gaps never
exercised before (`literal-type`, the opaque-literal family,
`annotation` and `annotation-unfolded`, `triple-terms-propositions`,
`reifies-range`) and 17 unsupported tests refused by name
(xsd:float/xsd:double/rdf:JSON value models). It also surfaced 2
apparent upstream contradictions in w3c/rdf-tests:
`malformed-literal-no-spurious` and `malformed-literal-bnode-neg` are
NegativeEntailmentTests whose premise the same suite declares
D-inconsistent — under classical entailment an inconsistent premise
entails everything.

**Cost:** three days of unexercised quote-polarity choices in two
engines; and, counted the other way, a permanent 0-of-0 line in every
umbrella score that no reader could distinguish from "nothing to run".

### 3.3 The F\* engine's opposite-polarity defect

[https://github.com/danbri/factoidal/issues/604](https://github.com/danbri/factoidal/issues/604).

**Found by:** the 602 post-mortem's differential check across both
trees. The F\* engine has the opposite defect from Lean's: its rdf12
runner skips the `mf:result false` inconsistency tests entirely
(re-measured 2026-08-25: **41 pass, 3 fail, 3 skip (out of 47)**), so
it renders no D-inconsistency verdict on rdf12 inputs at all; and its
rdf11 ill-typed scan is top-level only through a catch-all `_` arm.

**Cost:** the two engines currently disagree with each other on the
interior question, and neither had ever been tested on it. Open.

### 3.4 The §18.3.1 blank-node divergence

[https://github.com/danbri/factoidal/issues/607](https://github.com/danbri/factoidal/issues/607).

**Found by:** stage 6 reconnaissance during the stage 5 landing.
`SPARQL/Algebra.lean`'s `tryBindSubject` / `tryBindTerm` match a
pattern blank node only against a graph blank node with the same label
— a constant. SPARQL 1.1 §18.3.1 defines BGP matching through a pattern
instance mapping, in which a pattern blank node is a non-distinguished
variable that may match any RDF term.

**Cost:** the engine returns fewer solutions than the specification
licenses on any pattern with a blank node, and the narrowing was not
flagged anywhere in `Algebra.lean` — no comment, no test. For the
programme it cost a delimitation: stage 6's rows are adequate to the
ENGINE on such patterns, with `unified_adequate_bgp_bnodeFree` as the
corollary that is a claim about SPARQL 1.1.

### 3.5 A false `decide`, caught in the stage 2 salvage

**Found by:** verifying an interrupted agent's draft under
trust-nothing rules before landing it. The draft carried a `decide`
claiming all 40 rows of the engine's RDFS seed table appear in the
38-row spec table. Two rows are genuinely absent from RDF 1.1 Semantics
§9.3 — `rdf:XMLLiteral rdf:type rdfs:Datatype` and
`rdf:XMLLiteral rdfs:subClassOf rdfs:Literal` — because the spec's own
note says RDF-D interpretations MAY fail to recognize
`rdf:XMLLiteral`/`rdf:HTML`.

**Cost:** nothing shipped, because the salvage caught it. **Repair:**
an explicit `rdf:XMLLiteral ∈ D` hypothesis on
`unified_rdfs_closure_sound`, recorded as correction note 10b, with
`#guard`s pinning the seed-table/spec-table mismatch. The weakening is
in the theorem statement.

### 3.6 The range-clash value-space overclaim

Item 1 of
[https://github.com/danbri/factoidal/issues/605](https://github.com/danbri/factoidal/issues/605).

**Found by:** the first rdf-semantics run, confirming an interrupted
agent's unfiled finding. Witness:
`p rdfs:range xsd:integer . :a p "1"^^xsd:int`. The value 1 IS in
`xsd:integer`'s value space, so the graph is satisfiable per RDF 1.2
Semantics §7. The harness detector `regimeInconsistent .rdfs` answers
consistent (it is value-space aware); the spec-side
`rdfsDInconsistent` answers inconsistent from a bare datatype
mismatch; and stage 2's `DRangeCond` matches the bare-mismatch
reading, so `RdfsDEntailsMt` declares the graph unsatisfiable and
entails everything.

**Cost:** `RdfsDEntailsMt`, `rangeClashSchema` and
`hasRangeDatatypeClash` overclaim on the numeric chain
(`xsd:int` ⊂ `xsd:integer` ⊂ `xsd:decimal`), and the regime evaluator
can never be proven complete against `RdfsDEntailsMt` as it stands.
Open; the fix direction is a `valueInSpace`-shaped carve-out in
`DRangeCond`, `rangeClashAx` and `existsRangeLiteralMismatch`, with the
adequacy theorems reproved.

---

## 4. What is NOT claimed

This list collects claims a reader might reasonably infer from the
results table and that no theorem here supports. Section 2 carries the
per-stage gap rows.

1. **No multiplicity or bag result, and none available downstream.**
   `Answers` is a `Prop` and the evaluator side is membership.
   `SPARQL/AlgebraSpec.lean` keeps the SPARQL 1.1 §18.5 set layer and
   the cardinality layer apart, and the F\* bag-refinement proof is not
   ported, so no downstream theorem ties `evalBgp`'s bag to the
   specification's.
2. **The OWL 2 correspondence theorem is unproved.** RDF-Based
   Semantics §7.2 relates Direct Semantics and RDF-Based Semantics on
   mapped ontologies. This programme hosts both routes over one
   `CL.Interp` and proves nothing relating them. Within the tree they
   meet only through test agreement.
3. **Tableau completeness is open.** `refuted_unified_unsat` is
   soundness. A "consistent" verdict from the calculus is not a proof
   of satisfiability in OWL 2 DL, and "unknown" claims nothing.
4. **RDFS has no executable characterisation.** Finding C-1 blocks it;
   `unified_adequate_rdfs` is model-theoretic. The engine's full
   closure is related to the schema by soundness only.
5. **SPARQL adequacy is to the ENGINE outside the blank-node-free
   fragment.** See §2.7 delimitation 1 and
   [https://github.com/danbri/factoidal/issues/607](https://github.com/danbri/factoidal/issues/607).
6. **RIF Core was never dispatched.** The §4.7 machinery has been in
   place since stage 3; `unified_adequate_rifCore` does not exist.
7. **Finite-slice-suffices is unproved.** Nothing landed consumes it,
   and it would be needed only for a decided full-RDFS corollary that
   Finding C-1 independently blocks.
8. **The D decided corollary has only its sound half.**
9. **OWL 2 RL ground completeness is condition-bundle form, on a narrow
   fragment**, and does not reach graphs declaring object properties.
10. **Nothing here is a performance claim.** The unified layer is
    `Prop`-level and fuel-free: it states relations, and every decision
    procedure stays on the native side. Speed stays measured where it
    is measured.

---

## 5. What this buys next

Candidates, not commitments. Each is stated at the level the landed
theorems support.

1. **A wider proved-safe optimisation space.** An implementation change
   inside a fragment whose gate theorem is a full iff can be checked
   against the model theory rather than against a test score. Today
   that covers simple entailment, D-entailment, RDF, RDFS, RDFS+D, ρdf,
   the Datalog class, and OWL DL satisfiability on the tableau
   fragment.
2. **Fragment-completeness licences.** `datalog_lfp_iff_entails` plus
   an exhibit makes a closure engine the decider for the ground-atomic
   consequences of its schema. ρdf has that end to end. The RDFS-Plus
   and RL-core tiers would need per-row diagonal specification
   relations and a closedness predicate to reach it.
3. **One semantic foundation under the parser and streaming theorems**
   ([https://github.com/danbri/factoidal/issues/576](https://github.com/danbri/factoidal/issues/576)).
   The round-trip theorems currently bottom out at graph equality or
   isomorphism; composing them with `unified_adequate_simple` would
   make a parse-serialize cycle provably meaning-preserving in one model
   theory rather than per format. Blocked today: the native round-trip
   theorem covers only the empty graph.
4. **Interop containment questions, asked as theorems.** Two were
   raised alongside this programme and reached stage 7 through its
   brief: whether a JSON Schema's accepted instance set stands in a
   containment relation to what a framed JSON-LD document plus a SHACL
   shape accepts; and where the Murata–Lee–Mani hierarchy of XML schema
   languages (regular / local / single-type tree grammars) sits against
   the same picture. (Provenance note: no verbatim statement of either
   question is recorded in this tree, so this document attributes no
   rationale for them — they are listed as candidates, and the wording
   is the writer's.) Both are containment claims between acceptance
   relations. The unified layer supplies the shape of an answer — one
   interpretation class, two schemas, and either a proof or a
   separating model — but no work has started, and neither language has
   a translation in this tree today.

---

## References

* LBase: R. V. Guha, P. Hayes, *LBase: Semantics for Languages of the
  Semantic Web*, W3C Working Group Note, 10 October 2003 —
  [https://www.w3.org/TR/lbase/](https://www.w3.org/TR/lbase/).
* IKL guide (Hayes and Menzel) —
  [https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html);
  ISO/IEC 24707, Common Logic.
* RDF 1.1 Semantics, W3C Recommendation, 25 February 2014 —
  [https://www.w3.org/TR/rdf11-mt/](https://www.w3.org/TR/rdf11-mt/).
* RDF 1.2 Semantics, W3C Working Draft, 7 April 2026 (a WD, not a
  Recommendation) —
  [https://www.w3.org/TR/rdf12-semantics/](https://www.w3.org/TR/rdf12-semantics/).
* SPARQL 1.1 Query (§18.3.1, §18.5) —
  [https://www.w3.org/TR/sparql11-query/](https://www.w3.org/TR/sparql11-query/);
  SPARQL 1.1 Entailment Regimes —
  [https://www.w3.org/TR/sparql11-entailment/](https://www.w3.org/TR/sparql11-entailment/).
* OWL 2 Direct Semantics —
  [https://www.w3.org/TR/owl2-direct-semantics/](https://www.w3.org/TR/owl2-direct-semantics/);
  OWL 2 RDF-Based Semantics —
  [https://www.w3.org/TR/owl2-rdf-based-semantics/](https://www.w3.org/TR/owl2-rdf-based-semantics/);
  OWL 2 Profiles (RL rule tables) —
  [https://www.w3.org/TR/owl2-profiles/](https://www.w3.org/TR/owl2-profiles/).
* ρdf: S. Muñoz, J. Pérez, C. Gutierrez, *Simple and Efficient Minimal
  RDFS*, Journal of Web Semantics 7(3), 2009.
* Design document and its 32 correction notes:
  [`docs/designissues/2026-08-25-unified-semantics-lean.md`](2026-08-25-unified-semantics-lean.md).
  Registry rows: [`docs/theorem-registry.md`](../theorem-registry.md)
  section 9.
* Issues:
  [https://github.com/danbri/factoidal/issues/598](https://github.com/danbri/factoidal/issues/598)
  (this programme),
  [https://github.com/danbri/factoidal/issues/602](https://github.com/danbri/factoidal/issues/602)
  (D-semantics divergence, closed),
  [https://github.com/danbri/factoidal/issues/604](https://github.com/danbri/factoidal/issues/604)
  (F\* opposite polarity),
  [https://github.com/danbri/factoidal/issues/605](https://github.com/danbri/factoidal/issues/605)
  (range-clash overclaim, 9 engine gaps),
  [https://github.com/danbri/factoidal/issues/607](https://github.com/danbri/factoidal/issues/607)
  (§18.3.1 blank nodes),
  [https://github.com/danbri/factoidal/issues/576](https://github.com/danbri/factoidal/issues/576)
  (parser/streaming theorems),
  [https://github.com/danbri/factoidal/issues/581](https://github.com/danbri/factoidal/issues/581)
  (x-ikl regimes),
  [https://github.com/danbri/factoidal/issues/586](https://github.com/danbri/factoidal/issues/586)
  (tableau verdicts).
