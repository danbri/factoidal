/-
L4Factoidal.Unified.OwlRlSchema — the OWL 2 RL/RDF rule table as an
axiom SCHEMA of the unified LBase/IKL theory, and the bridge from
schema satisfaction to `OWL/RLSemantics.lean`'s `RlCond*` bundle.

Stage 4 of https://github.com/danbri/factoidal/issues/598, design
document `docs/designissues/2026-08-25-unified-semantics-lean.md` §4.4.

## Row families and the mechanism each uses

The table is built ROW-FAMILY-WISE, not as one monolith:

* **Plain Horn rows** — a `DRule` each (`Unified/Datalog.lean`'s n-ary
  `DAtom`), read as a universally closed implication by
  `DRule.sentence`, and turned into an `RlCond*` by ONE generic lemma
  (`hornRow`) plus a per-row valuation. The `RlRowId` enumeration
  indexes them, so schema membership for a named row is `⟨row, rfl⟩` —
  O(1), no list search.
* **Guarded and table-indexed families** — one `DRule` per instance of
  a decidable side condition (eq-ref at a non-reserved predicate,
  cax-adc-dw at a distinct IRI pair, the three Table 7 datatype rows).
* **List-valued rows** — prp-spo2 and prp-key quantify over a
  collection; each becomes a sentence FAMILY, one Horn sentence per
  list length `n`, with the `rdf:first`/`rdf:rest` walk and the chain
  or shared-value premises flattened into `n`-many body atoms. The
  seven other collection rows (cls-int1/2, cls-uni, cls-oo, scm-int,
  scm-uni, cax-adc-dw) go through the reserved `urn:cl:def:listMember`
  and `urn:cl:def:typedAllMembers` helper predicates that
  `RLSemantics.lean` introduces, whose two Horn axioms each replace
  the per-length family.
* **Clash rows** — falsity-headed, so NOT `DRule`s (a `DatalogProgram`
  is definite by construction). Each is a universally closed negated
  conjunction, in the `dExclusionSchema` / `rangeClashSchema` pattern
  of `Unified/DSchema.lean` and `Unified/RdfsSchema.lean`.
* **Cardinality-literal rows** — cls-maxc2 (Horn) and cls-maxc1,
  cls-maxqc1, cls-maxqc2 (clash) relate a term to a cardinality
  LITERAL. `Unified/Datalog.lean` carries `DTerm.lit`, whose CL form is
  `embedTerm (.literal l)` and whose value is the denotation
  `restrictInterp` gives `iLit`, so these are ordinary rows of the two
  families above. (Before 2026-08-26 they were in `OwlRlInterpCond`,
  because a literal embedded as a `funapp` and `DTerm` had no literal
  constructor.)
* **Comprehension rows** — cax-dw-comp, cls-maxqc1-comp and minc1-comp
  have EXISTENTIAL heads, excluded by `DRule.definiteB`. They stay in
  `OwlRlInterpCond`; the section header below costs the alternative.

## Direction of the bridge

`owlRlSchema_conditions` goes schema → `RlCond*`. That is the
direction soundness needs, and it is the EASY direction: a `DRule`
quantifies its predicate position over the whole domain, where the
`RlCond*` row quantifies over IRIs, so the sentence is strictly
stronger than the condition. The converse (every row true in the
enriched Herbrand model) is what `Unified/OwlRlAdequacy.lean` needs for
completeness and is proved there against `OWL/RLHerbrand.lean`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.Datalog
import L4Factoidal.OWL.RLHerbrand

namespace L4Factoidal.Unified

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-! ## Atom builders -/

/-- A constant `DTerm` naming an IRI. -/
def dk (w : RDF.WfIri) : DTerm := .c w.val

/-- A constant `DTerm` denoting a LITERAL — the term the four
cardinality rows need in object position. Its CL form is
`embedTerm (.literal l)` and its value is the same denotation
`restrictInterp` gives `iLit`, so a body obligation whose premise is
`i.iext _ x (i.iLit l)` closes by `assumption` exactly as an IRI
premise does. -/
def dlit (l : RDF.WfLiteral) : DTerm := .lit l

theorem dlit_val (i : CL.Interp) (f : String → i.dom) (l : RDF.WfLiteral) :
    (dlit l).val i f = (restrictInterp i).iLit l := rfl

/-- A binary predication: the property term in operator position. -/
def dbin (p x y : DTerm) : DAtom := ⟨p, [x, y]⟩

/-- An `rdf:type` predication (the object-language form of `icext`). -/
def dtyp (x cc : DTerm) : DAtom := dbin (dk rdfType) x cc

/-- The binary reading of a `DAtom` at a restricted interpretation is
definitional: `DAtom.Holds` is `i.rel p [x, y]` and
`restrictInterp i |>.iext` is the same expression. -/
theorem holds_dbin (i : CL.Interp) (f : String → i.dom) (p x y : DTerm) :
    (dbin p x y).Holds i f ↔
      (restrictInterp i).iext (p.val i f) (x.val i f) (y.val i f) :=
  Iff.rfl

theorem dk_val (i : CL.Interp) (f : String → i.dom) (w : RDF.WfIri) :
    (dk w).val i f = (restrictInterp i).iIri w := rfl

/-- A valuation built from an association list; unlisted names take the
domain witness. -/
def vals (i : CL.Interp) : List (String × i.dom) → String → i.dom
  | [], _ => i.domWit
  | (k, v) :: r, n => if n = k then v else vals i r n

/-- Apply one schema row, given schema satisfaction. -/
theorem rlRowFires {i : CL.Interp} {S : Schema} (hS : SatisfiesSchema i S)
    {r : DRule} (hmem : S r.sentence) (hwf : r.wfB = true)
    (f : String → i.dom) (hb : ∀ a ∈ r.body, a.Holds i f) :
    r.head.Holds i f :=
  (satisfies_ruleSentence_iff i hwf).mp (hS _ hmem) f hb

/-! ## The plain Horn rows -/

/-- One identifier per plain Horn row of the OWL 2 RL/RDF tables
(https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules,
Tables 4-9), plus the `[ext]` rows `RLRules.lean` adds and the two
reserved helper-predicate axioms of `RLSemantics.lean`. -/
inductive RlRowId where
  | eqRefS | eqRefO | eqSym | eqTrans | eqRepS | eqRepP | eqRepO
  | prpDom | prpRng | prpFp | prpIfp | prpSymp | prpTrp
  | prpSpo1 | prpEqp1 | prpEqp2 | prpInv1 | prpInv2
  | clsThing | clsNothing1 | clsInt1
  | typedAllBase | typedAllStep | listMemBase | listMemStep
  | clsInt2 | clsUni | clsSvf1 | clsSvf2 | clsAvf | clsHv1 | clsHv2
  | clsMaxc2
  | clsOo | caxSco | caxEqc1 | caxEqc2
  | scmClsSelf | scmClsEqc | scmClsThing | scmClsNothing
  | scmSco | scmEqc1a | scmEqc1b | scmEqc2
  | scmSpo | scmEqp1a | scmEqp1b | scmEqp2
  | scmDom1 | scmDom2 | scmRng1 | scmRng2 | scmInt | scmUni
  | eqDiffSym | pdwToDiff | caxDwToDiff | fpDiffToDiff | ifpDiffToDiff
  | chainToTrans | prpRflS | prpRflO
  | invFlipDomRng | invFlipRngDom | invFlipDomRngRev | invFlipRngDomRev
  deriving DecidableEq, Repr

/-- The `DRule` of each plain row. Variable names are colon-free and
constants are IRIs (colon-carrying) — the `DRule.wfB` discipline of
`Unified/Datalog.lean`. -/
def rlRowRule : RlRowId → DRule
  | .eqRefS => ⟨dbin (dk owlSameAs) (.v "x") (.v "x"),
      [dbin (.v "p") (.v "x") (.v "y")]⟩
  | .eqRefO => ⟨dbin (dk owlSameAs) (.v "y") (.v "y"),
      [dbin (.v "p") (.v "x") (.v "y")]⟩
  | .eqSym => ⟨dbin (dk owlSameAs) (.v "y") (.v "x"),
      [dbin (dk owlSameAs) (.v "x") (.v "y")]⟩
  | .eqTrans => ⟨dbin (dk owlSameAs) (.v "x") (.v "z"),
      [dbin (dk owlSameAs) (.v "x") (.v "y"),
       dbin (dk owlSameAs) (.v "y") (.v "z")]⟩
  | .eqRepS => ⟨dbin (.v "p") (.v "t") (.v "o"),
      [dbin (dk owlSameAs) (.v "s") (.v "t"),
       dbin (.v "p") (.v "s") (.v "o")]⟩
  | .eqRepP => ⟨dbin (.v "q") (.v "x") (.v "y"),
      [dbin (dk owlSameAs) (.v "p") (.v "q"),
       dbin (.v "p") (.v "x") (.v "y")]⟩
  | .eqRepO => ⟨dbin (.v "p") (.v "s") (.v "w"),
      [dbin (dk owlSameAs) (.v "o") (.v "w"),
       dbin (.v "p") (.v "s") (.v "o")]⟩
  | .prpDom => ⟨dtyp (.v "x") (.v "c"),
      [dbin (dk rdfsDomain) (.v "p") (.v "c"),
       dbin (.v "p") (.v "x") (.v "y")]⟩
  | .prpRng => ⟨dtyp (.v "y") (.v "c"),
      [dbin (dk rdfsRange) (.v "p") (.v "c"),
       dbin (.v "p") (.v "x") (.v "y")]⟩
  | .prpFp => ⟨dbin (dk owlSameAs) (.v "y") (.v "z"),
      [dtyp (.v "p") (dk owlFunctionalProperty),
       dbin (.v "p") (.v "x") (.v "y"),
       dbin (.v "p") (.v "x") (.v "z")]⟩
  | .prpIfp => ⟨dbin (dk owlSameAs) (.v "x") (.v "z"),
      [dtyp (.v "p") (dk owlInverseFunctionalProperty),
       dbin (.v "p") (.v "x") (.v "y"),
       dbin (.v "p") (.v "z") (.v "y")]⟩
  | .prpSymp => ⟨dbin (.v "p") (.v "y") (.v "x"),
      [dtyp (.v "p") (dk owlSymmetricProperty),
       dbin (.v "p") (.v "x") (.v "y")]⟩
  | .prpTrp => ⟨dbin (.v "p") (.v "x") (.v "z"),
      [dtyp (.v "p") (dk owlTransitiveProperty),
       dbin (.v "p") (.v "x") (.v "y"),
       dbin (.v "p") (.v "y") (.v "z")]⟩
  | .prpSpo1 => ⟨dbin (.v "q") (.v "x") (.v "y"),
      [dbin (dk rdfsSubPropertyOf) (.v "p") (.v "q"),
       dbin (.v "p") (.v "x") (.v "y")]⟩
  | .prpEqp1 => ⟨dbin (.v "q") (.v "x") (.v "y"),
      [dbin (dk owlEquivalentProperty) (.v "p") (.v "q"),
       dbin (.v "p") (.v "x") (.v "y")]⟩
  | .prpEqp2 => ⟨dbin (.v "p") (.v "x") (.v "y"),
      [dbin (dk owlEquivalentProperty) (.v "p") (.v "q"),
       dbin (.v "q") (.v "x") (.v "y")]⟩
  | .prpInv1 => ⟨dbin (.v "q") (.v "y") (.v "x"),
      [dbin (dk owlInverseOf) (.v "p") (.v "q"),
       dbin (.v "p") (.v "x") (.v "y")]⟩
  | .prpInv2 => ⟨dbin (.v "p") (.v "y") (.v "x"),
      [dbin (dk owlInverseOf) (.v "p") (.v "q"),
       dbin (.v "q") (.v "x") (.v "y")]⟩
  | .clsThing => ⟨dtyp (dk owlThing) (dk owlClass), []⟩
  | .clsNothing1 => ⟨dtyp (dk owlNothing) (dk owlClass), []⟩
  | .clsInt1 => ⟨dtyp (.v "y") (.v "c"),
      [dbin (dk owlIntersectionOf) (.v "c") (.v "l"),
       dbin (dk uTypedAll) (.v "y") (.v "l")]⟩
  | .typedAllBase => ⟨dbin (dk uTypedAll) (.v "y") (.v "l"),
      [dbin (dk rdfFirst) (.v "l") (.v "e"),
       dbin (dk rdfRest) (.v "l") (dk rdfNil),
       dtyp (.v "y") (.v "e")]⟩
  | .typedAllStep => ⟨dbin (dk uTypedAll) (.v "y") (.v "l"),
      [dbin (dk rdfFirst) (.v "l") (.v "e"),
       dbin (dk rdfRest) (.v "l") (.v "m"),
       dtyp (.v "y") (.v "e"),
       dbin (dk uTypedAll) (.v "y") (.v "m")]⟩
  | .listMemBase => ⟨dbin (dk uListMem) (.v "l") (.v "e"),
      [dbin (dk rdfFirst) (.v "l") (.v "e")]⟩
  | .listMemStep => ⟨dbin (dk uListMem) (.v "l") (.v "e"),
      [dbin (dk rdfRest) (.v "l") (.v "m"),
       dbin (dk uListMem) (.v "m") (.v "e")]⟩
  | .clsInt2 => ⟨dtyp (.v "y") (.v "d"),
      [dbin (dk owlIntersectionOf) (.v "c") (.v "l"),
       dbin (dk uListMem) (.v "l") (.v "d"),
       dtyp (.v "y") (.v "c")]⟩
  | .clsUni => ⟨dtyp (.v "y") (.v "c"),
      [dbin (dk owlUnionOf) (.v "c") (.v "l"),
       dbin (dk uListMem) (.v "l") (.v "d"),
       dtyp (.v "y") (.v "d")]⟩
  | .clsSvf1 => ⟨dtyp (.v "u") (.v "x"),
      [dbin (dk owlSomeValuesFrom) (.v "x") (.v "z"),
       dbin (dk owlOnProperty) (.v "x") (.v "p"),
       dbin (.v "p") (.v "u") (.v "v"),
       dtyp (.v "v") (.v "z")]⟩
  | .clsSvf2 => ⟨dtyp (.v "u") (.v "x"),
      [dbin (dk owlSomeValuesFrom) (.v "x") (dk owlThing),
       dbin (dk owlOnProperty) (.v "x") (.v "p"),
       dbin (.v "p") (.v "u") (.v "v")]⟩
  | .clsAvf => ⟨dtyp (.v "v") (.v "z"),
      [dbin (dk owlAllValuesFrom) (.v "x") (.v "z"),
       dbin (dk owlOnProperty) (.v "x") (.v "p"),
       dtyp (.v "u") (.v "x"),
       dbin (.v "p") (.v "u") (.v "v")]⟩
  | .clsHv1 => ⟨dbin (.v "p") (.v "u") (.v "y"),
      [dbin (dk owlHasValue) (.v "x") (.v "y"),
       dbin (dk owlOnProperty) (.v "x") (.v "p"),
       dtyp (.v "u") (.v "x")]⟩
  | .clsHv2 => ⟨dtyp (.v "u") (.v "x"),
      [dbin (dk owlHasValue) (.v "x") (.v "y"),
       dbin (dk owlOnProperty) (.v "x") (.v "p"),
       dbin (.v "p") (.v "u") (.v "y")]⟩
  | .clsOo => ⟨dtyp (.v "y") (.v "c"),
      [dbin (dk owlOneOf) (.v "c") (.v "l"),
       dbin (dk uListMem) (.v "l") (.v "y")]⟩
  | .caxSco => ⟨dtyp (.v "x") (.v "d"),
      [dbin (dk rdfsSubClassOf) (.v "c") (.v "d"),
       dtyp (.v "x") (.v "c")]⟩
  | .caxEqc1 => ⟨dtyp (.v "x") (.v "d"),
      [dbin (dk owlEquivalentClass) (.v "c") (.v "d"),
       dtyp (.v "x") (.v "c")]⟩
  | .caxEqc2 => ⟨dtyp (.v "x") (.v "c"),
      [dbin (dk owlEquivalentClass) (.v "c") (.v "d"),
       dtyp (.v "x") (.v "d")]⟩
  | .scmClsSelf => ⟨dbin (dk rdfsSubClassOf) (.v "c") (.v "c"),
      [dtyp (.v "c") (dk owlClass)]⟩
  | .scmClsEqc => ⟨dbin (dk owlEquivalentClass) (.v "c") (.v "c"),
      [dtyp (.v "c") (dk owlClass)]⟩
  | .scmClsThing => ⟨dbin (dk rdfsSubClassOf) (.v "c") (dk owlThing),
      [dtyp (.v "c") (dk owlClass)]⟩
  | .scmClsNothing => ⟨dbin (dk rdfsSubClassOf) (dk owlNothing) (.v "c"),
      [dtyp (.v "c") (dk owlClass)]⟩
  | .scmSco => ⟨dbin (dk rdfsSubClassOf) (.v "c") (.v "e"),
      [dbin (dk rdfsSubClassOf) (.v "c") (.v "d"),
       dbin (dk rdfsSubClassOf) (.v "d") (.v "e")]⟩
  | .scmEqc1a => ⟨dbin (dk rdfsSubClassOf) (.v "c") (.v "d"),
      [dbin (dk owlEquivalentClass) (.v "c") (.v "d")]⟩
  | .scmEqc1b => ⟨dbin (dk rdfsSubClassOf) (.v "d") (.v "c"),
      [dbin (dk owlEquivalentClass) (.v "c") (.v "d")]⟩
  | .scmEqc2 => ⟨dbin (dk owlEquivalentClass) (.v "c") (.v "d"),
      [dbin (dk rdfsSubClassOf) (.v "c") (.v "d"),
       dbin (dk rdfsSubClassOf) (.v "d") (.v "c")]⟩
  | .scmSpo => ⟨dbin (dk rdfsSubPropertyOf) (.v "p") (.v "r"),
      [dbin (dk rdfsSubPropertyOf) (.v "p") (.v "q"),
       dbin (dk rdfsSubPropertyOf) (.v "q") (.v "r")]⟩
  | .scmEqp1a => ⟨dbin (dk rdfsSubPropertyOf) (.v "p") (.v "q"),
      [dbin (dk owlEquivalentProperty) (.v "p") (.v "q")]⟩
  | .scmEqp1b => ⟨dbin (dk rdfsSubPropertyOf) (.v "q") (.v "p"),
      [dbin (dk owlEquivalentProperty) (.v "p") (.v "q")]⟩
  | .scmEqp2 => ⟨dbin (dk owlEquivalentProperty) (.v "p") (.v "q"),
      [dbin (dk rdfsSubPropertyOf) (.v "p") (.v "q"),
       dbin (dk rdfsSubPropertyOf) (.v "q") (.v "p")]⟩
  | .scmDom1 => ⟨dbin (dk rdfsDomain) (.v "p") (.v "d"),
      [dbin (dk rdfsDomain) (.v "p") (.v "c"),
       dbin (dk rdfsSubClassOf) (.v "c") (.v "d")]⟩
  | .scmDom2 => ⟨dbin (dk rdfsDomain) (.v "p") (.v "c"),
      [dbin (dk rdfsDomain) (.v "q") (.v "c"),
       dbin (dk rdfsSubPropertyOf) (.v "p") (.v "q")]⟩
  | .scmRng1 => ⟨dbin (dk rdfsRange) (.v "p") (.v "d"),
      [dbin (dk rdfsRange) (.v "p") (.v "c"),
       dbin (dk rdfsSubClassOf) (.v "c") (.v "d")]⟩
  | .scmRng2 => ⟨dbin (dk rdfsRange) (.v "p") (.v "c"),
      [dbin (dk rdfsRange) (.v "q") (.v "c"),
       dbin (dk rdfsSubPropertyOf) (.v "p") (.v "q")]⟩
  | .scmInt => ⟨dbin (dk rdfsSubClassOf) (.v "c") (.v "d"),
      [dbin (dk owlIntersectionOf) (.v "c") (.v "l"),
       dbin (dk uListMem) (.v "l") (.v "d")]⟩
  | .scmUni => ⟨dbin (dk rdfsSubClassOf) (.v "d") (.v "c"),
      [dbin (dk owlUnionOf) (.v "c") (.v "l"),
       dbin (dk uListMem) (.v "l") (.v "d")]⟩
  | .eqDiffSym => ⟨dbin (dk owlDifferentFrom) (.v "y") (.v "x"),
      [dbin (dk owlDifferentFrom) (.v "x") (.v "y")]⟩
  | .pdwToDiff => ⟨dbin (dk owlDifferentFrom) (.v "a") (.v "b"),
      [dbin (dk owlPropertyDisjointWith) (.v "p") (.v "q"),
       dbin (.v "p") (.v "x") (.v "a"),
       dbin (.v "q") (.v "x") (.v "b")]⟩
  | .caxDwToDiff => ⟨dbin (dk owlDifferentFrom) (.v "x") (.v "y"),
      [dbin (dk owlDisjointWith) (.v "c") (.v "d"),
       dtyp (.v "x") (.v "c"),
       dtyp (.v "y") (.v "d")]⟩
  | .fpDiffToDiff => ⟨dbin (dk owlDifferentFrom) (.v "y") (.v "z"),
      [dtyp (.v "p") (dk owlFunctionalProperty),
       dbin (.v "p") (.v "y") (.v "a"),
       dbin (.v "p") (.v "z") (.v "b"),
       dbin (dk owlDifferentFrom) (.v "a") (.v "b")]⟩
  | .ifpDiffToDiff => ⟨dbin (dk owlDifferentFrom) (.v "a") (.v "b"),
      [dtyp (.v "p") (dk owlInverseFunctionalProperty),
       dbin (.v "p") (.v "x") (.v "a"),
       dbin (.v "p") (.v "y") (.v "b"),
       dbin (dk owlDifferentFrom) (.v "x") (.v "y")]⟩
  | .chainToTrans => ⟨dtyp (.v "p") (dk owlTransitiveProperty),
      [dbin (dk owlPropertyChainAxiom) (.v "p") (.v "l"),
       dbin (dk rdfFirst) (.v "l") (.v "p"),
       dbin (dk rdfRest) (.v "l") (.v "m"),
       dbin (dk rdfFirst) (.v "m") (.v "p"),
       dbin (dk rdfRest) (.v "m") (dk rdfNil)]⟩
  | .prpRflS => ⟨dbin (.v "p") (.v "j") (.v "j"),
      [dtyp (.v "p") (dk owlReflexiveProperty),
       dbin (.v "q") (.v "j") (.v "y")]⟩
  | .prpRflO => ⟨dbin (.v "p") (.v "j") (.v "j"),
      [dtyp (.v "p") (dk owlReflexiveProperty),
       dbin (.v "q") (.v "x") (.v "j")]⟩
  | .invFlipDomRng => ⟨dbin (dk rdfsRange) (.v "q") (.v "c"),
      [dbin (dk owlInverseOf) (.v "p") (.v "q"),
       dbin (dk rdfsDomain) (.v "p") (.v "c")]⟩
  | .invFlipRngDom => ⟨dbin (dk rdfsDomain) (.v "q") (.v "c"),
      [dbin (dk owlInverseOf) (.v "p") (.v "q"),
       dbin (dk rdfsRange) (.v "p") (.v "c")]⟩
  | .invFlipDomRngRev => ⟨dbin (dk rdfsRange) (.v "p") (.v "c"),
      [dbin (dk owlInverseOf) (.v "p") (.v "q"),
       dbin (dk rdfsDomain) (.v "q") (.v "c")]⟩
  | .invFlipRngDomRev => ⟨dbin (dk rdfsDomain) (.v "p") (.v "c"),
      [dbin (dk owlInverseOf) (.v "p") (.v "q"),
       dbin (dk rdfsRange) (.v "q") (.v "c")]⟩

  | .clsMaxc2 => ⟨dbin (dk owlSameAs) (.v "y") (.v "z"),
      [dbin (dk owlMaxCardinality) (.v "x") (dlit litNni1),
       dbin (dk owlOnProperty) (.v "x") (.v "p"),
       dtyp (.v "u") (.v "x"),
       dbin (.v "p") (.v "u") (.v "y"),
       dbin (.v "p") (.v "u") (.v "z")]⟩

theorem rlRowRule_wf (row : RlRowId) : (rlRowRule row).wfB = true := by
  cases row <;> rfl

/-- The plain-Horn part of the schema. -/
def owlRlHornSchema : Schema := fun s => ∃ row : RlRowId, s = (rlRowRule row).sentence

theorem hornSchema_mem (row : RlRowId) : owlRlHornSchema (rlRowRule row).sentence :=
  ⟨row, rfl⟩

/-- Fire a named plain row at a valuation. -/
theorem rlRowAt {i : CL.Interp} (hS : SatisfiesSchema i owlRlHornSchema)
    (row : RlRowId) (f : String → i.dom)
    (hb : ∀ a ∈ (rlRowRule row).body, a.Holds i f) :
    (rlRowRule row).head.Holds i f :=
  rlRowFires hS (hornSchema_mem row) (rlRowRule_wf row) f hb


/-! ## From schema satisfaction to the plain `RlCond*` rows

Each lemma instantiates the row's universally closed implication at a
valuation that sends the rule's variables to the condition's
parameters. `DAtom.Holds` at `restrictInterp i` and
`RDF.Interp.iext` are the SAME expression (`holds_dbin`), so every body
obligation closes by `assumption` and the head is the conclusion. -/

section RowConditions

variable {i : CL.Interp} (hS : SatisfiesSchema i owlRlHornSchema)
include hS

theorem cond_eqRefS : RlCondEqRefS (restrictInterp i) := by
  intro p x y h1
  refine rlRowAt hS .eqRefS (vals i [("p", (restrictInterp i).iIri p), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_eqRefO : RlCondEqRefO (restrictInterp i) := by
  intro p x y h1
  refine rlRowAt hS .eqRefO (vals i [("p", (restrictInterp i).iIri p), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_eqSym : RlCondEqSym (restrictInterp i) := by
  intro x y h1
  refine rlRowAt hS .eqSym (vals i [("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_eqTrans : RlCondEqTrans (restrictInterp i) := by
  intro x y z h1 h2
  refine rlRowAt hS .eqTrans (vals i [("x", x), ("y", y), ("z", z)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_eqRepS : RlCondEqRepS (restrictInterp i) := by
  intro p s s' o h1 h2
  refine rlRowAt hS .eqRepS (vals i [("s", s), ("t", s'), ("o", o), ("p", (restrictInterp i).iIri p)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_eqRepP : RlCondEqRepP (restrictInterp i) := by
  intro p p' x y h1 h2
  refine rlRowAt hS .eqRepP (vals i [("p", (restrictInterp i).iIri p), ("q", (restrictInterp i).iIri p'), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_eqRepO : RlCondEqRepO (restrictInterp i) := by
  intro p s o o' h1 h2
  refine rlRowAt hS .eqRepO (vals i [("p", (restrictInterp i).iIri p), ("s", s), ("o", o), ("w", o')]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_prpDom : RlCondPrpDom (restrictInterp i) := by
  intro p cc x y h1 h2
  refine rlRowAt hS .prpDom (vals i [("p", (restrictInterp i).iIri p), ("c", cc), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_prpRng : RlCondPrpRng (restrictInterp i) := by
  intro p cc x y h1 h2
  refine rlRowAt hS .prpRng (vals i [("p", (restrictInterp i).iIri p), ("c", cc), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_prpFp : RlCondPrpFp (restrictInterp i) := by
  intro p x y1 y2 h1 h2 h3
  refine rlRowAt hS .prpFp (vals i [("p", (restrictInterp i).iIri p), ("x", x), ("y", y1), ("z", y2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem cond_prpIfp : RlCondPrpIfp (restrictInterp i) := by
  intro p x1 x2 y h1 h2 h3
  refine rlRowAt hS .prpIfp (vals i [("p", (restrictInterp i).iIri p), ("x", x1), ("y", y), ("z", x2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem cond_prpSymp : RlCondPrpSymp (restrictInterp i) := by
  intro p x y h1 h2
  refine rlRowAt hS .prpSymp (vals i [("p", (restrictInterp i).iIri p), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_prpTrp : RlCondPrpTrp (restrictInterp i) := by
  intro p x y z h1 h2 h3
  refine rlRowAt hS .prpTrp (vals i [("p", (restrictInterp i).iIri p), ("x", x), ("y", y), ("z", z)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem cond_prpSpo1 : RlCondPrpSpo1 (restrictInterp i) := by
  intro p1 p2 x y h1 h2
  refine rlRowAt hS .prpSpo1 (vals i [("p", (restrictInterp i).iIri p1), ("q", (restrictInterp i).iIri p2), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_prpEqp1 : RlCondPrpEqp1 (restrictInterp i) := by
  intro p1 p2 x y h1 h2
  refine rlRowAt hS .prpEqp1 (vals i [("p", (restrictInterp i).iIri p1), ("q", (restrictInterp i).iIri p2), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_prpEqp2 : RlCondPrpEqp2 (restrictInterp i) := by
  intro p1 p2 x y h1 h2
  refine rlRowAt hS .prpEqp2 (vals i [("p", (restrictInterp i).iIri p1), ("q", (restrictInterp i).iIri p2), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_prpInv1 : RlCondPrpInv1 (restrictInterp i) := by
  intro p1 p2 x y h1 h2
  refine rlRowAt hS .prpInv1 (vals i [("p", (restrictInterp i).iIri p1), ("q", (restrictInterp i).iIri p2), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_prpInv2 : RlCondPrpInv2 (restrictInterp i) := by
  intro p1 p2 x y h1 h2
  refine rlRowAt hS .prpInv2 (vals i [("p", (restrictInterp i).iIri p1), ("q", (restrictInterp i).iIri p2), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_clsThing : RlCondClsThing (restrictInterp i) := by
  refine rlRowAt hS .clsThing (vals i []) ?_
  intro a ha
  simp only [rlRowRule, List.not_mem_nil] at ha

theorem cond_clsNothing1 : RlCondClsNothing1 (restrictInterp i) := by
  refine rlRowAt hS .clsNothing1 (vals i []) ?_
  intro a ha
  simp only [rlRowRule, List.not_mem_nil] at ha

theorem cond_clsInt1 : RlCondClsInt1 (restrictInterp i) := by
  intro cc y l h1 h2
  refine rlRowAt hS .clsInt1 (vals i [("c", cc), ("y", y), ("l", l)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_typedAllBase : RlCondTypedAllBase (restrictInterp i) := by
  intro y l e h1 h2 h3
  refine rlRowAt hS .typedAllBase (vals i [("y", y), ("l", l), ("e", e)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem cond_typedAllStep : RlCondTypedAllStep (restrictInterp i) := by
  intro y l l' e h1 h2 h3 h4
  refine rlRowAt hS .typedAllStep (vals i [("y", y), ("l", l), ("e", e), ("m", l')]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem cond_listMemBase : RlCondListMemBase (restrictInterp i) := by
  intro l e h1
  refine rlRowAt hS .listMemBase (vals i [("l", l), ("e", e)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_listMemStep : RlCondListMemStep (restrictInterp i) := by
  intro l l' e h1 h2
  refine rlRowAt hS .listMemStep (vals i [("l", l), ("m", l'), ("e", e)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_clsInt2 : RlCondClsInt2 (restrictInterp i) := by
  intro cc y l ci h1 h2 h3
  refine rlRowAt hS .clsInt2 (vals i [("c", cc), ("l", l), ("d", ci), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem cond_clsUni : RlCondClsUni (restrictInterp i) := by
  intro cc y l ci h1 h2 h3
  refine rlRowAt hS .clsUni (vals i [("c", cc), ("l", l), ("d", ci), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem cond_clsSvf1 : RlCondClsSvf1 (restrictInterp i) := by
  intro p x u v yc h1 h2 h3 h4
  refine rlRowAt hS .clsSvf1 (vals i [("x", x), ("z", yc), ("p", (restrictInterp i).iIri p), ("u", u), ("v", v)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem cond_clsSvf2 : RlCondClsSvf2 (restrictInterp i) := by
  intro p x u v h1 h2 h3
  refine rlRowAt hS .clsSvf2 (vals i [("x", x), ("p", (restrictInterp i).iIri p), ("u", u), ("v", v)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem cond_clsAvf : RlCondClsAvf (restrictInterp i) := by
  intro p x u v yc h1 h2 h3 h4
  refine rlRowAt hS .clsAvf (vals i [("x", x), ("z", yc), ("p", (restrictInterp i).iIri p), ("u", u), ("v", v)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem cond_clsHv1 : RlCondClsHv1 (restrictInterp i) := by
  intro p x u yv h1 h2 h3
  refine rlRowAt hS .clsHv1 (vals i [("x", x), ("y", yv), ("p", (restrictInterp i).iIri p), ("u", u)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem cond_clsHv2 : RlCondClsHv2 (restrictInterp i) := by
  intro p x u yv h1 h2 h3
  refine rlRowAt hS .clsHv2 (vals i [("x", x), ("y", yv), ("p", (restrictInterp i).iIri p), ("u", u)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

/-- **cls-maxc2**, now an ordinary Horn row: the `owl:maxCardinality`
premise carries the cardinality literal as `dlit litNni1`, whose
denotation IS `iLit litNni1`. -/
theorem cond_clsMaxc2 : RlCondClsMaxc2 (restrictInterp i) := by
  intro p x u y1 y2 h1 h2 h3 h4 h5
  refine rlRowAt hS .clsMaxc2
    (vals i [("x", x), ("p", (restrictInterp i).iIri p), ("u", u),
             ("y", y1), ("z", y2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem cond_clsOo : RlCondClsOo (restrictInterp i) := by
  intro cc l yi h1 h2
  refine rlRowAt hS .clsOo (vals i [("c", cc), ("l", l), ("y", yi)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_caxSco : RlCondCaxSco (restrictInterp i) := by
  intro c1 c2 x h1 h2
  refine rlRowAt hS .caxSco (vals i [("c", c1), ("d", c2), ("x", x)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_caxEqc1 : RlCondCaxEqc1 (restrictInterp i) := by
  intro c1 c2 x h1 h2
  refine rlRowAt hS .caxEqc1 (vals i [("c", c1), ("d", c2), ("x", x)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_caxEqc2 : RlCondCaxEqc2 (restrictInterp i) := by
  intro c1 c2 x h1 h2
  refine rlRowAt hS .caxEqc2 (vals i [("c", c1), ("d", c2), ("x", x)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_scmClsSelf : RlCondScmClsSelf (restrictInterp i) := by
  intro cc h1
  refine rlRowAt hS .scmClsSelf (vals i [("c", cc)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_scmClsEqc : RlCondScmClsEqc (restrictInterp i) := by
  intro cc h1
  refine rlRowAt hS .scmClsEqc (vals i [("c", cc)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_scmClsThing : RlCondScmClsThing (restrictInterp i) := by
  intro cc h1
  refine rlRowAt hS .scmClsThing (vals i [("c", cc)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_scmClsNothing : RlCondScmClsNothing (restrictInterp i) := by
  intro cc h1
  refine rlRowAt hS .scmClsNothing (vals i [("c", cc)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_scmSco : RlCondScmSco (restrictInterp i) := by
  intro c1 c2 c3 h1 h2
  refine rlRowAt hS .scmSco (vals i [("c", c1), ("d", c2), ("e", c3)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_scmEqc1a : RlCondScmEqc1a (restrictInterp i) := by
  intro c1 c2 h1
  refine rlRowAt hS .scmEqc1a (vals i [("c", c1), ("d", c2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_scmEqc1b : RlCondScmEqc1b (restrictInterp i) := by
  intro c1 c2 h1
  refine rlRowAt hS .scmEqc1b (vals i [("c", c1), ("d", c2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_scmEqc2 : RlCondScmEqc2 (restrictInterp i) := by
  intro c1 c2 h1 h2
  refine rlRowAt hS .scmEqc2 (vals i [("c", c1), ("d", c2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_scmSpo : RlCondScmSpo (restrictInterp i) := by
  intro p1 p2 p3 h1 h2
  refine rlRowAt hS .scmSpo (vals i [("p", p1), ("q", p2), ("r", p3)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_scmEqp1a : RlCondScmEqp1a (restrictInterp i) := by
  intro p1 p2 h1
  refine rlRowAt hS .scmEqp1a (vals i [("p", p1), ("q", p2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_scmEqp1b : RlCondScmEqp1b (restrictInterp i) := by
  intro p1 p2 h1
  refine rlRowAt hS .scmEqp1b (vals i [("p", p1), ("q", p2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_scmEqp2 : RlCondScmEqp2 (restrictInterp i) := by
  intro p1 p2 h1 h2
  refine rlRowAt hS .scmEqp2 (vals i [("p", p1), ("q", p2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_scmDom1 : RlCondScmDom1 (restrictInterp i) := by
  intro pd c1 c2 h1 h2
  refine rlRowAt hS .scmDom1 (vals i [("p", pd), ("c", c1), ("d", c2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_scmDom2 : RlCondScmDom2 (restrictInterp i) := by
  intro p1 p2 cc h1 h2
  refine rlRowAt hS .scmDom2 (vals i [("p", p1), ("q", p2), ("c", cc)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_scmRng1 : RlCondScmRng1 (restrictInterp i) := by
  intro pd c1 c2 h1 h2
  refine rlRowAt hS .scmRng1 (vals i [("p", pd), ("c", c1), ("d", c2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_scmRng2 : RlCondScmRng2 (restrictInterp i) := by
  intro p1 p2 cc h1 h2
  refine rlRowAt hS .scmRng2 (vals i [("p", p1), ("q", p2), ("c", cc)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_scmInt : RlCondScmInt (restrictInterp i) := by
  intro cc l ci h1 h2
  refine rlRowAt hS .scmInt (vals i [("c", cc), ("l", l), ("d", ci)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_scmUni : RlCondScmUni (restrictInterp i) := by
  intro cc l ci h1 h2
  refine rlRowAt hS .scmUni (vals i [("c", cc), ("l", l), ("d", ci)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_eqDiffSym : RlCondEqDiffSym (restrictInterp i) := by
  intro x y h1
  refine rlRowAt hS .eqDiffSym (vals i [("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_pdwToDiff : RlCondPdwToDiff (restrictInterp i) := by
  intro p1 p2 x o1 o2 h1 h2 h3
  refine rlRowAt hS .pdwToDiff (vals i [("p", (restrictInterp i).iIri p1), ("q", (restrictInterp i).iIri p2), ("x", x), ("a", o1), ("b", o2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem cond_caxDwToDiff : RlCondCaxDwToDiff (restrictInterp i) := by
  intro c1 c2 x y h1 h2 h3
  refine rlRowAt hS .caxDwToDiff (vals i [("c", (restrictInterp i).iIri c1), ("d", (restrictInterp i).iIri c2), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem cond_fpDiffToDiff : RlCondFpDiffToDiff (restrictInterp i) := by
  intro p y1 y2 x1 x2 h1 h2 h3 h4
  refine rlRowAt hS .fpDiffToDiff (vals i [("p", (restrictInterp i).iIri p), ("y", y1), ("a", x1), ("z", y2), ("b", x2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem cond_ifpDiffToDiff : RlCondIfpDiffToDiff (restrictInterp i) := by
  intro p x1 x2 y1 y2 h1 h2 h3 h4
  refine rlRowAt hS .ifpDiffToDiff (vals i [("p", (restrictInterp i).iIri p), ("x", x1), ("a", y1), ("y", x2), ("b", y2)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem cond_chainToTrans : RlCondChainToTrans (restrictInterp i) := by
  intro p l l' h1 h2 h3 h4 h5
  refine rlRowAt hS .chainToTrans (vals i [("p", (restrictInterp i).iIri p), ("l", l), ("m", l')]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem cond_prpRflS : RlCondPrpRflS (restrictInterp i) := by
  intro p j q y h1 h2
  refine rlRowAt hS .prpRflS (vals i [("p", (restrictInterp i).iIri p), ("q", q), ("j", (restrictInterp i).iIri j), ("y", y)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_prpRflO : RlCondPrpRflO (restrictInterp i) := by
  intro p j q x h1 h2
  refine rlRowAt hS .prpRflO (vals i [("p", (restrictInterp i).iIri p), ("q", q), ("x", x), ("j", (restrictInterp i).iIri j)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_invFlipDomRng : RlCondInvFlipDomRng (restrictInterp i) := by
  intro p q cc h1 h2
  refine rlRowAt hS .invFlipDomRng (vals i [("p", (restrictInterp i).iIri p), ("q", (restrictInterp i).iIri q), ("c", (restrictInterp i).iIri cc)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_invFlipRngDom : RlCondInvFlipRngDom (restrictInterp i) := by
  intro p q cc h1 h2
  refine rlRowAt hS .invFlipRngDom (vals i [("p", (restrictInterp i).iIri p), ("q", (restrictInterp i).iIri q), ("c", (restrictInterp i).iIri cc)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_invFlipDomRngRev : RlCondInvFlipDomRngRev (restrictInterp i) := by
  intro p q cc h1 h2
  refine rlRowAt hS .invFlipDomRngRev (vals i [("p", (restrictInterp i).iIri p), ("q", (restrictInterp i).iIri q), ("c", (restrictInterp i).iIri cc)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_invFlipRngDomRev : RlCondInvFlipRngDomRev (restrictInterp i) := by
  intro p q cc h1 h2
  refine rlRowAt hS .invFlipRngDomRev (vals i [("p", (restrictInterp i).iIri p), ("q", (restrictInterp i).iIri q), ("c", (restrictInterp i).iIri cc)]) ?_
  intro a ha
  simp only [rlRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2
end RowConditions


/-! ## Guarded and table-indexed families

Five rows carry a decidable side condition or range over a fixed table.
Each becomes one `DRule` per instance, and the family is the set of
those rule sentences. -/

theorem dk_wf (w : RDF.WfIri) : (dk w).wfB = true := by
  simp only [dk, DTerm.wfB]
  exact List.contains_iff_mem.mpr (isIri_has_colon w.property)

/-- **eq-ref**, predicate conclusion, at a NON-RESERVED predicate (the
guard `RLSemantics.lean` states on the row). -/
def ruleEqRefP (p : RDF.WfIri) : DRule :=
  ⟨dbin (dk owlSameAs) (dk p) (dk p), [dbin (dk p) (.v "x") (.v "y")]⟩

/-- **cax-adc-dw**, at a distinct pair of member IRIs. -/
def ruleCaxAdcToDw (ci cj : RDF.WfIri) : DRule :=
  ⟨dbin (dk owlDisjointWith) (dk ci) (dk cj),
   [dtyp (.v "y") (dk owlAllDisjointClasses),
    dbin (dk owlMembers) (.v "y") (.v "l"),
    dbin (dk uListMem) (.v "l") (dk ci),
    dbin (dk uListMem) (.v "l") (dk cj)]⟩

/-- **dt-type1**, one premise-free rule per builtin datatype axiom. -/
def ruleDtType1 (a pr b : RDF.WfIri) : DRule := ⟨dbin (dk pr) (dk a) (dk b), []⟩

/-- **dt-rng-intersect**, one rule per licensed datatype triple. -/
def ruleDtRangeIntersect (d1 d2 d3 : RDF.WfIri) : DRule :=
  ⟨dbin (dk rdfsRange) (.v "p") (dk d3),
   [dbin (dk rdfsRange) (.v "p") (dk d1),
    dbin (dk rdfsRange) (.v "p") (dk d2)]⟩

/-- **xsd-axioms**, one rule per (datatype-position predicate, XSD IRI,
XSD tower triple). -/
def ruleXsdAxiom (p w a pr b : RDF.WfIri) : DRule :=
  ⟨dbin (dk pr) (dk a) (dk b), [dbin (dk p) (.v "x") (dk w)]⟩

theorem dv_wf (n : String) (h : n.toList.contains ':' = false) :
    (DTerm.v n).wfB = true := by
  simp only [DTerm.wfB, h, Bool.not_false]

theorem dbin_wf {p x y : DTerm} (hp : p.wfB = true) (hx : x.wfB = true)
    (hy : y.wfB = true) : (dbin p x y).wfB = true := by
  simp only [dbin, DAtom.wfB, List.all_cons, List.all_nil, hp, hx, hy,
             Bool.and_true, Bool.true_and]

theorem dtyp_wf {x cc : DTerm} (hx : x.wfB = true) (hc : cc.wfB = true) :
    (dtyp x cc).wfB = true :=
  dbin_wf (dk_wf rdfType) hx hc

theorem drule_wf_of {r : DRule} (hh : r.head.wfB = true)
    (hb : r.body.all DAtom.wfB = true) (hd : r.definiteB = true) :
    r.wfB = true := by
  simp only [DRule.wfB, hh, hb, hd, Bool.and_true, Bool.true_and]

theorem ruleEqRefP_wf (p : RDF.WfIri) : (ruleEqRefP p).wfB = true :=
  drule_wf_of (dbin_wf (dk_wf owlSameAs) (dk_wf p) (dk_wf p))
    (by simp only [ruleEqRefP, List.all_cons, List.all_nil,
          dbin_wf (dk_wf p) (dv_wf "x" (by decide)) (dv_wf "y" (by decide)), Bool.and_true])
    rfl

theorem ruleCaxAdcToDw_wf (ci cj : RDF.WfIri) :
    (ruleCaxAdcToDw ci cj).wfB = true :=
  drule_wf_of (dbin_wf (dk_wf owlDisjointWith) (dk_wf ci) (dk_wf cj))
    (by simp only [ruleCaxAdcToDw, List.all_cons, List.all_nil,
          dtyp_wf (dv_wf "y" (by decide)) (dk_wf owlAllDisjointClasses),
          dbin_wf (dk_wf owlMembers) (dv_wf "y" (by decide)) (dv_wf "l" (by decide)),
          dbin_wf (dk_wf uListMem) (dv_wf "l" (by decide)) (dk_wf ci),
          dbin_wf (dk_wf uListMem) (dv_wf "l" (by decide)) (dk_wf cj),
          Bool.and_true])
    rfl

theorem ruleDtType1_wf (a pr b : RDF.WfIri) : (ruleDtType1 a pr b).wfB = true :=
  drule_wf_of (dbin_wf (dk_wf pr) (dk_wf a) (dk_wf b)) rfl rfl

theorem ruleDtRangeIntersect_wf (d1 d2 d3 : RDF.WfIri) :
    (ruleDtRangeIntersect d1 d2 d3).wfB = true :=
  drule_wf_of (dbin_wf (dk_wf rdfsRange) (dv_wf "p" (by decide)) (dk_wf d3))
    (by simp only [ruleDtRangeIntersect, List.all_cons, List.all_nil,
          dbin_wf (dk_wf rdfsRange) (dv_wf "p" (by decide)) (dk_wf d1),
          dbin_wf (dk_wf rdfsRange) (dv_wf "p" (by decide)) (dk_wf d2),
          Bool.and_true])
    rfl

theorem ruleXsdAxiom_wf (p w a pr b : RDF.WfIri) :
    (ruleXsdAxiom p w a pr b).wfB = true :=
  drule_wf_of (dbin_wf (dk_wf pr) (dk_wf a) (dk_wf b))
    (by simp only [ruleXsdAxiom, List.all_cons, List.all_nil,
          dbin_wf (dk_wf p) (dv_wf "x" (by decide)) (dk_wf w), Bool.and_true])
    rfl

/-- The five guarded / table-indexed families. -/
def owlRlFamilySchema : Schema := fun s =>
  (∃ p : RDF.WfIri, rlReservedIri p = false ∧ s = (ruleEqRefP p).sentence) ∨
  (∃ ci cj : RDF.WfIri, ci ≠ cj ∧ s = (ruleCaxAdcToDw ci cj).sentence) ∨
  (∃ a pr b : RDF.WfIri,
      (⟨Subject.iri a, pr, Term.iri b⟩ : Triple) ∈ builtinDatatypeAxioms ∧
      s = (ruleDtType1 a pr b).sentence) ∨
  (∃ d1 d2 d3 : RDF.WfIri, rangeIntersectLicenses d1 d2 d3 = true ∧
      s = (ruleDtRangeIntersect d1 d2 d3).sentence) ∨
  (∃ p w a pr b : RDF.WfIri, p ∈ datatypePositionPredicates ∧
      iriInXsdNs w = true ∧
      (⟨Subject.iri a, pr, Term.iri b⟩ : Triple) ∈ xsdAxiomTriples ∧
      s = (ruleXsdAxiom p w a pr b).sentence)

section FamilyConditions

variable {i : CL.Interp} (hF : SatisfiesSchema i owlRlFamilySchema)
include hF

theorem cond_eqRefP : RlCondEqRefP (restrictInterp i) := by
  intro p hp x y h1
  refine rlRowFires hF (Or.inl ⟨p, hp, rfl⟩) (ruleEqRefP_wf p)
    (vals i [("x", x), ("y", y)]) ?_
  intro a ha
  simp only [ruleEqRefP, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem cond_caxAdcToDw : RlCondCaxAdcToDw (restrictInterp i) := by
  intro ci cj hne y l h1 h2 h3 h4
  refine rlRowFires hF (Or.inr (Or.inl ⟨ci, cj, hne, rfl⟩))
    (ruleCaxAdcToDw_wf ci cj) (vals i [("y", y), ("l", l)]) ?_
  intro a ha
  simp only [ruleCaxAdcToDw, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem cond_dtType1Builtin : RlCondDtType1Builtin (restrictInterp i) := by
  intro a pr b hm
  refine rlRowFires hF (Or.inr (Or.inr (Or.inl ⟨a, pr, b, hm, rfl⟩)))
    (ruleDtType1_wf a pr b) (vals i []) ?_
  intro u hu
  simp only [ruleDtType1, List.not_mem_nil] at hu

theorem cond_dtRangeIntersect : RlCondDtRangeIntersect (restrictInterp i) := by
  intro d1 d2 d3 hlic pd h1 h2
  refine rlRowFires hF (Or.inr (Or.inr (Or.inr (Or.inl ⟨d1, d2, d3, hlic, rfl⟩))))
    (ruleDtRangeIntersect_wf d1 d2 d3) (vals i [("p", pd)]) ?_
  intro a ha
  simp only [ruleDtRangeIntersect, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem cond_xsdAxioms : RlCondXsdAxioms (restrictInterp i) := by
  intro p hp w hw a pr b hm x h1
  refine rlRowFires hF
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, w, a, pr, b, hp, hw, hm, rfl⟩))))
    (ruleXsdAxiom_wf p w a pr b) (vals i [("x", x)]) ?_
  intro u hu
  simp only [ruleXsdAxiom, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl
  exact h1

end FamilyConditions



/-! ## The list-valued rows: prp-spo2 and prp-key as sentence FAMILIES

These two rows quantify over a collection, so neither is a single
sentence. Each becomes one Horn rule per collection length: the
`rdf:first` / `rdf:rest` walk and the chain (or shared-value) premises
flattened into `n`-many body atoms.

The variable names are GENERATED, and the generation scheme is chosen
so that a valuation never has to parse a numeral: `nmAt c k` is the
character `c` followed by `k` copies of `'x'`, so `seqVal` reads the
index off the tail's LENGTH. That removes the injectivity burden a
decimal spelling would carry. -/

/-- A generated variable name: `c` then `k` copies of `'x'`. -/
def nmAt (c : Char) (k : Nat) : String :=
  String.ofList (c :: List.replicate k 'x')

/-- Cell names (the `rdf:first`/`rdf:rest` walk). -/
def nmL (k : Nat) : String := nmAt 'l' k
/-- Collection-member names: the properties of a chain (prp-spo2) or
the key properties (prp-key). -/
def nmQ (k : Nat) : String := nmAt 'q' k
/-- Chain-intermediate names (prp-spo2) / shared-value names
(prp-key). -/
def nmV (k : Nat) : String := nmAt 'v' k
/-- prp-spo2's head property, and prp-key's class and two
individuals. -/
def nmP : String := String.ofList ['p']
def nmC : String := String.ofList ['c']
def nmX : String := String.ofList ['s']
def nmY : String := String.ofList ['t']

theorem nmAt_toList (c : Char) (k : Nat) :
    (nmAt c k).toList = c :: List.replicate k 'x' := String.toList_ofList

theorem nmAt_no_colon {c : Char} (hc : c ≠ ':') (k : Nat) :
    (nmAt c k).toList.contains ':' = false := by
  rw [nmAt_toList]
  simp [List.mem_replicate, Ne.symm hc]

theorem nmL_no_colon (k : Nat) : (nmL k).toList.contains ':' = false :=
  nmAt_no_colon (by decide) k
theorem nmQ_no_colon (k : Nat) : (nmQ k).toList.contains ':' = false :=
  nmAt_no_colon (by decide) k
theorem nmV_no_colon (k : Nat) : (nmV k).toList.contains ':' = false :=
  nmAt_no_colon (by decide) k

/-- A valuation for the generated names: the leading character selects
the family and the tail's LENGTH is the index. Polymorphic in the
domain so it applies at `i.dom` and at `(restrictInterp i).idom`
without transport. -/
def seqVal {d : Type} (wit : d) (cells props vs : Nat → d)
    (a b c : d) : String → d :=
  fun s => match s.toList with
    | 'l' :: r => cells r.length
    | 'q' :: r => props r.length
    | 'v' :: r => vs r.length
    | 'p' :: [] => a
    | 'c' :: [] => a
    | 's' :: [] => b
    | 't' :: [] => c
    | _ => wit

section SeqValLookup
variable {d : Type} (wit : d) (cells props vs : Nat → d) (a b c : d)

@[simp] theorem seqVal_L (k : Nat) :
    seqVal wit cells props vs a b c (nmL k) = cells k := by
  simp [seqVal, nmL, nmAt]

@[simp] theorem seqVal_Q (k : Nat) :
    seqVal wit cells props vs a b c (nmQ k) = props k := by
  simp [seqVal, nmQ, nmAt]

@[simp] theorem seqVal_V (k : Nat) :
    seqVal wit cells props vs a b c (nmV k) = vs k := by
  simp [seqVal, nmV, nmAt]

@[simp] theorem seqVal_P : seqVal wit cells props vs a b c nmP = a := by
  simp [seqVal, nmP]
@[simp] theorem seqVal_C : seqVal wit cells props vs a b c nmC = a := by
  simp [seqVal, nmC]
@[simp] theorem seqVal_X : seqVal wit cells props vs a b c nmX = b := by
  simp [seqVal, nmX]
@[simp] theorem seqVal_Y : seqVal wit cells props vs a b c nmY = c := by
  simp [seqVal, nmY]

end SeqValLookup

/-! ### Reading a collection off `SeqIs`, and a chain off `SemChain`

`SeqIs` and `SemChain` are existential chains. The rule family needs
the witnesses as INDEXED functions, so each is turned into one by
induction on the member list. `List.getD … i.idomWit` names the k-th
member without a bounds proof. -/

/-- The walk of a `SeqIs` collection as indexed functions: `cells k`
is the k-th cons cell (`cells 0` the head, `cells n` `rdf:nil`) and
`props k` the k-th member. Stated at `restrictInterp i`, with every
function at `i.dom`, so the bridge lemmas need no transport. -/
theorem seqIs_walk {i : CL.Interp} :
    ∀ (qs : List i.dom) (l : i.dom), OWL.SeqIs (restrictInterp i) l qs →
      ∃ cells props : Nat → i.dom,
        cells 0 = l ∧ cells qs.length = (restrictInterp i).iIri rdfNil ∧
        (∀ k, k < qs.length → props k = qs.getD k i.domWit) ∧
        (∀ k, k < qs.length →
          (restrictInterp i).iext ((restrictInterp i).iIri rdfFirst)
            (cells k) (props k)) ∧
        (∀ k, k < qs.length →
          (restrictInterp i).iext ((restrictInterp i).iIri rdfRest)
            (cells k) (cells (k + 1)))
  | [], l, h => by
      refine ⟨fun _ => (restrictInterp i).iIri rdfNil, fun _ => i.domWit,
              ?_, rfl, ?_, ?_, ?_⟩
      · exact h.symm
      all_goals (intro k hk; simp at hk)
  | x :: rest, l, h => by
      obtain ⟨l', hf, hr, hs⟩ := h
      obtain ⟨cells', props', h0', hnil', hp', hfst', hrst'⟩ :=
        seqIs_walk rest l' hs
      refine ⟨fun k => Nat.rec l (fun j _ => cells' j) k,
              fun k => Nat.rec x (fun j _ => props' j) k, rfl, hnil', ?_, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero => rfl
        | succ j => exact hp' j (Nat.lt_of_succ_lt_succ hk)
      · intro k hk
        cases k with
        | zero => exact hf
        | succ j => exact hfst' j (Nat.lt_of_succ_lt_succ hk)
      · intro k hk
        cases k with
        | zero =>
            show (restrictInterp i).iext ((restrictInterp i).iIri rdfRest) l
              (cells' 0)
            rw [h0']; exact hr
        | succ j => exact hrst' j (Nat.lt_of_succ_lt_succ hk)

/-- prp-spo2's chain as an indexed function: `vs 0 = u`, `vs n = w`,
and step `k` runs along the k-th property. -/
theorem semChain_vals {i : CL.Interp} :
    ∀ (qs : List i.dom) (u w : i.dom), SemChain (restrictInterp i) u qs w →
      ∃ vs : Nat → i.dom, vs 0 = u ∧ vs qs.length = w ∧
        (∀ k, k < qs.length →
          (restrictInterp i).iext (qs.getD k i.domWit) (vs k) (vs (k + 1)))
  | [], u, w, h => by
      refine ⟨fun _ => u, rfl, h, ?_⟩
      intro k hk; simp at hk
  | x :: rest, u, w, h => by
      obtain ⟨v, hxv, hrest⟩ := h
      obtain ⟨vs', h0', hn', hst'⟩ := semChain_vals rest v w hrest
      refine ⟨fun k => Nat.rec u (fun j _ => vs' j) k, rfl, hn', ?_⟩
      intro k hk
      cases k with
      | zero =>
          show (restrictInterp i).iext ((x :: rest).getD 0 i.domWit) u (vs' 0)
          rw [h0']
          simpa using hxv
      | succ j => exact hst' j (Nat.lt_of_succ_lt_succ hk)

/-- prp-key's shared values as an indexed function. -/
theorem semShares_vals {i : CL.Interp} (x y : i.dom) :
    ∀ (qs : List i.dom), SemShares (restrictInterp i) x y qs →
      ∃ vs : Nat → i.dom, ∀ k, k < qs.length →
        (restrictInterp i).iext (qs.getD k i.domWit) x (vs k) ∧
        (restrictInterp i).iext (qs.getD k i.domWit) y (vs k)
  | [], _ => by
      refine ⟨fun _ => i.domWit, ?_⟩
      intro k hk; simp at hk
  | q :: rest, h => by
      obtain ⟨v, hxv, hyv⟩ := h q (List.mem_cons_self ..)
      obtain ⟨vs', hst'⟩ :=
        semShares_vals x y rest (fun u hu => h u (List.mem_cons_of_mem _ hu))
      refine ⟨fun k => Nat.rec v (fun j _ => vs' j) k, ?_⟩
      intro k hk
      cases k with
      | zero => exact ⟨hxv, hyv⟩
      | succ j => exact hst' j (Nat.lt_of_succ_lt_succ hk)

@[simp] theorem dv_val (i : CL.Interp) (f : String → i.dom) (n : String) :
    (DTerm.v n).val i f = f n := rfl

/-! ### The two rule families -/

/-- **prp-spo2** at chain length `m + 1`. The chain axiom names cell
`l0`; cells `l0..lm` walk the collection and `lm` rests at `rdf:nil`;
`qk` is the k-th property and `vk` the k-th chain point, so the head
runs `p` from `v0` to `v(m+1)`. -/
def spo2Rule (m : Nat) : DRule :=
  ⟨dbin (.v nmP) (.v (nmV 0)) (.v (nmV (m + 1))),
   dbin (dk owlPropertyChainAxiom) (.v nmP) (.v (nmL 0)) ::
   dbin (dk rdfRest) (.v (nmL m)) (dk rdfNil) ::
   ((List.range (m + 1)).flatMap (fun k =>
      [dbin (dk rdfFirst) (.v (nmL k)) (.v (nmQ k)),
       dbin (.v (nmQ k)) (.v (nmV k)) (.v (nmV (k + 1)))]) ++
    (List.range m).map (fun k =>
      dbin (dk rdfRest) (.v (nmL k)) (.v (nmL (k + 1)))))⟩

/-- **prp-key** at key length `m + 1`. Same walk; `s` and `t` are the
two individuals, both typed into `c`, and `vk` is the value they share
on the k-th key property. -/
def keyRule (m : Nat) : DRule :=
  ⟨dbin (dk owlSameAs) (.v nmX) (.v nmY),
   dbin (dk owlHasKey) (.v nmC) (.v (nmL 0)) ::
   dbin (dk rdfRest) (.v (nmL m)) (dk rdfNil) ::
   dtyp (.v nmX) (.v nmC) ::
   dtyp (.v nmY) (.v nmC) ::
   ((List.range (m + 1)).flatMap (fun k =>
      [dbin (dk rdfFirst) (.v (nmL k)) (.v (nmQ k)),
       dbin (.v (nmQ k)) (.v nmX) (.v (nmV k)),
       dbin (.v (nmQ k)) (.v nmY) (.v (nmV k))]) ++
    (List.range m).map (fun k =>
      dbin (dk rdfRest) (.v (nmL k)) (.v (nmL (k + 1)))))⟩

theorem nmP_wf : (DTerm.v nmP).wfB = true := dv_wf _ (by decide)
theorem nmC_wf : (DTerm.v nmC).wfB = true := dv_wf _ (by decide)
theorem nmX_wf : (DTerm.v nmX).wfB = true := dv_wf _ (by decide)
theorem nmY_wf : (DTerm.v nmY).wfB = true := dv_wf _ (by decide)
theorem nmL_wf (k : Nat) : (DTerm.v (nmL k)).wfB = true := dv_wf _ (nmL_no_colon k)
theorem nmQ_wf (k : Nat) : (DTerm.v (nmQ k)).wfB = true := dv_wf _ (nmQ_no_colon k)
theorem nmV_wf (k : Nat) : (DTerm.v (nmV k)).wfB = true := dv_wf _ (nmV_no_colon k)

/-- Membership in a rule's binder list, from membership in one of its
body atoms' variable lists. -/
theorem mem_bodyVars {r : DRule} {a : DAtom} (ha : a ∈ r.body)
    {n : String} (hn : n ∈ a.varList) : n ∈ r.bodyVars :=
  List.mem_flatMap.mpr ⟨a, ha, hn⟩

theorem spo2Rule_wf (m : Nat) : (spo2Rule m).wfB = true := by
  refine drule_wf_of (dbin_wf nmP_wf (nmV_wf 0) (nmV_wf (m + 1))) ?_ ?_
  · rw [List.all_eq_true]
    intro a ha
    simp only [spo2Rule, List.mem_cons, List.mem_append, List.mem_flatMap,
               List.mem_map, List.mem_range] at ha
    rcases ha with rfl | rfl | ⟨⟨k, _, hk⟩ | ⟨k, _, rfl⟩⟩
    · exact dbin_wf (dk_wf owlPropertyChainAxiom) nmP_wf (nmL_wf 0)
    · exact dbin_wf (dk_wf rdfRest) (nmL_wf m) (dk_wf rdfNil)
    · rcases hk with rfl | rfl | hk3
      · exact dbin_wf (dk_wf rdfFirst) (nmL_wf k) (nmQ_wf k)
      · exact dbin_wf (nmQ_wf k) (nmV_wf k) (nmV_wf (k + 1))
      · cases hk3
    · exact dbin_wf (dk_wf rdfRest) (nmL_wf k) (nmL_wf (k + 1))
  · rw [DRule.definiteB, List.all_eq_true]
    intro n hn
    refine List.contains_iff_mem.mpr ?_
    simp only [spo2Rule, dbin, DAtom.varList, DTerm.varList,
               List.flatMap_cons, List.flatMap_nil, List.append_nil,
               List.nil_append, List.mem_append, List.mem_cons,
               List.not_mem_nil, or_false, List.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact mem_bodyVars (r := spo2Rule m)
        (a := dbin (dk owlPropertyChainAxiom) (.v nmP) (.v (nmL 0)))
        (by simp [spo2Rule]) (by simp [dbin, DAtom.varList, DTerm.varList, dk])
    · exact mem_bodyVars (r := spo2Rule m)
        (a := dbin (.v (nmQ 0)) (.v (nmV 0)) (.v (nmV 1)))
        (by
          simp only [spo2Rule, List.mem_cons, List.mem_append, List.mem_flatMap,
                     List.mem_map, List.mem_range]
          exact Or.inr (Or.inr (Or.inl ⟨0, Nat.succ_pos m, by simp⟩)))
        (by simp [dbin, DAtom.varList, DTerm.varList])
    · exact mem_bodyVars (r := spo2Rule m)
        (a := dbin (.v (nmQ m)) (.v (nmV m)) (.v (nmV (m + 1))))
        (by
          simp only [spo2Rule, List.mem_cons, List.mem_append, List.mem_flatMap,
                     List.mem_map, List.mem_range]
          exact Or.inr (Or.inr (Or.inl ⟨m, Nat.lt_succ_self m, by simp⟩)))
        (by simp [dbin, DAtom.varList, DTerm.varList])

theorem keyRule_wf (m : Nat) : (keyRule m).wfB = true := by
  refine drule_wf_of (dbin_wf (dk_wf owlSameAs) nmX_wf nmY_wf) ?_ ?_
  · rw [List.all_eq_true]
    intro a ha
    simp only [keyRule, List.mem_cons, List.mem_append, List.mem_flatMap,
               List.mem_map, List.mem_range] at ha
    rcases ha with rfl | rfl | rfl | rfl | ⟨⟨k, _, hk⟩ | ⟨k, _, rfl⟩⟩
    · exact dbin_wf (dk_wf owlHasKey) nmC_wf (nmL_wf 0)
    · exact dbin_wf (dk_wf rdfRest) (nmL_wf m) (dk_wf rdfNil)
    · exact dtyp_wf nmX_wf nmC_wf
    · exact dtyp_wf nmY_wf nmC_wf
    · rcases hk with rfl | rfl | rfl | hk4
      · exact dbin_wf (dk_wf rdfFirst) (nmL_wf k) (nmQ_wf k)
      · exact dbin_wf (nmQ_wf k) nmX_wf (nmV_wf k)
      · exact dbin_wf (nmQ_wf k) nmY_wf (nmV_wf k)
      · cases hk4
    · exact dbin_wf (dk_wf rdfRest) (nmL_wf k) (nmL_wf (k + 1))
  · rw [DRule.definiteB, List.all_eq_true]
    intro n hn
    refine List.contains_iff_mem.mpr ?_
    simp only [keyRule, dbin, DAtom.varList, DTerm.varList,
               List.flatMap_cons, List.flatMap_nil, List.append_nil,
               List.nil_append, List.mem_append, List.mem_cons,
               List.not_mem_nil, or_false, List.mem_singleton, dk] at hn
    rcases hn with rfl | rfl
    · exact mem_bodyVars (r := keyRule m) (a := dtyp (.v nmX) (.v nmC))
        (by simp [keyRule]) (by simp [dtyp, dbin, DAtom.varList, DTerm.varList, dk])
    · exact mem_bodyVars (r := keyRule m) (a := dtyp (.v nmY) (.v nmC))
        (by simp [keyRule]) (by simp [dtyp, dbin, DAtom.varList, DTerm.varList, dk])

/-- The two list-valued families as a schema. -/
def owlRlSeqSchema : Schema := fun s =>
  (∃ m : Nat, s = (spo2Rule m).sentence) ∨ (∃ m : Nat, s = (keyRule m).sentence)

section SeqConditions

variable {i : CL.Interp} (hS : SatisfiesSchema i owlRlSeqSchema)
include hS

/-- **prp-spo2** from the family: the collection has some length
`m + 1`, and the `m`-th member of the family is the row at that
length. -/
theorem cond_prpSpo2 : RlCondPrpSpo2 (restrictInterp i) := by
  show ∀ (p : RDF.WfIri) (l u w : i.dom) (qs : List i.dom), qs ≠ [] →
    (restrictInterp i).iext ((restrictInterp i).iIri owlPropertyChainAxiom)
      ((restrictInterp i).iIri p) l →
    OWL.SeqIs (restrictInterp i) l qs →
    SemChain (restrictInterp i) u qs w →
    (restrictInterp i).iext ((restrictInterp i).iIri p) u w
  intro p l u w qs hne h1 h2 h3
  obtain ⟨m, hm⟩ : ∃ m, qs.length = m + 1 := by
    cases qs with
    | nil => exact absurd rfl hne
    | cons a r => exact ⟨r.length, rfl⟩
  obtain ⟨cells, props, hc0, hcn, hpk, hfst, hrst⟩ := seqIs_walk qs l h2
  obtain ⟨vs, hv0, hvn, hstep⟩ := semChain_vals qs u w h3
  rw [hm] at hcn hpk hfst hrst hvn hstep
  have hb : ∀ a ∈ (spo2Rule m).body,
      a.Holds i (seqVal (d := i.dom) i.domWit cells props vs
        ((restrictInterp i).iIri p) i.domWit i.domWit) := by
    intro a ha
    simp only [spo2Rule, List.mem_cons, List.mem_append, List.mem_flatMap,
               List.mem_map, List.mem_range, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | ⟨⟨k, hk, (rfl | rfl)⟩ | ⟨k, hk, rfl⟩⟩
    · rw [holds_dbin]
      simp only [dv_val, dk_val]
      erw [seqVal_P, seqVal_L, hc0]
      exact h1
    · rw [holds_dbin]
      simp only [dv_val, dk_val]
      erw [seqVal_L]
      rw [← hcn]
      exact hrst m (Nat.lt_succ_self m)
    · rw [holds_dbin]
      simp only [dv_val, dk_val]
      erw [seqVal_L, seqVal_Q]
      exact hfst k hk
    · rw [holds_dbin]
      simp only [dv_val]
      erw [seqVal_Q, seqVal_V, seqVal_V]
      rw [hpk k hk]
      exact hstep k hk
    · rw [holds_dbin]
      simp only [dv_val, dk_val]
      erw [seqVal_L, seqVal_L]
      exact hrst k (Nat.lt_succ_of_lt hk)
  have h4 := rlRowFires hS (Or.inl ⟨m, rfl⟩) (spo2Rule_wf m) _ hb
  rw [show (spo2Rule m).head
        = dbin (.v nmP) (.v (nmV 0)) (.v (nmV (m + 1))) from rfl,
      holds_dbin] at h4
  simp only [dv_val] at h4
  erw [seqVal_P, seqVal_V, seqVal_V, hv0, hvn] at h4
  exact h4

/-- **prp-key** from the family. -/
theorem cond_prpKey : RlCondPrpKey (restrictInterp i) := by
  show ∀ (c l x y : i.dom) (qs : List i.dom), qs ≠ [] →
    (restrictInterp i).iext ((restrictInterp i).iIri owlHasKey) c l →
    OWL.SeqIs (restrictInterp i) l qs →
    icext (restrictInterp i) x c → icext (restrictInterp i) y c →
    SemShares (restrictInterp i) x y qs →
    (restrictInterp i).iext ((restrictInterp i).iIri owlSameAs) x y
  intro c l x y qs hne h1 h2 h3 h4 h5
  obtain ⟨m, hm⟩ : ∃ m, qs.length = m + 1 := by
    cases qs with
    | nil => exact absurd rfl hne
    | cons a r => exact ⟨r.length, rfl⟩
  obtain ⟨cells, props, hc0, hcn, hpk, hfst, hrst⟩ := seqIs_walk qs l h2
  obtain ⟨vs, hsh⟩ := semShares_vals x y qs h5
  rw [hm] at hcn hpk hfst hrst hsh
  have hb : ∀ a ∈ (keyRule m).body,
      a.Holds i (seqVal (d := i.dom) i.domWit cells props vs c x y) := by
    intro a ha
    simp only [keyRule, List.mem_cons, List.mem_append, List.mem_flatMap,
               List.mem_map, List.mem_range, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl |
      ⟨⟨k, hk, (rfl | rfl | rfl)⟩ | ⟨k, hk, rfl⟩⟩
    · rw [holds_dbin]
      simp only [dv_val, dk_val]
      erw [seqVal_C, seqVal_L, hc0]
      exact h1
    · rw [holds_dbin]
      simp only [dv_val, dk_val]
      erw [seqVal_L]
      rw [← hcn]
      exact hrst m (Nat.lt_succ_self m)
    · simp only [dtyp]
      rw [holds_dbin]
      simp only [dv_val, dk_val]
      erw [seqVal_X, seqVal_C]
      exact h3
    · simp only [dtyp]
      rw [holds_dbin]
      simp only [dv_val, dk_val]
      erw [seqVal_Y, seqVal_C]
      exact h4
    · rw [holds_dbin]
      simp only [dv_val, dk_val]
      erw [seqVal_L, seqVal_Q]
      exact hfst k hk
    · rw [holds_dbin]
      simp only [dv_val]
      erw [seqVal_Q, seqVal_X, seqVal_V]
      rw [hpk k hk]
      exact (hsh k hk).1
    · rw [holds_dbin]
      simp only [dv_val]
      erw [seqVal_Q, seqVal_Y, seqVal_V]
      rw [hpk k hk]
      exact (hsh k hk).2
    · rw [holds_dbin]
      simp only [dv_val, dk_val]
      erw [seqVal_L, seqVal_L]
      exact hrst k (Nat.lt_succ_of_lt hk)
  have h6 := rlRowFires hS (Or.inr ⟨m, rfl⟩) (keyRule_wf m) _ hb
  rw [show (keyRule m).head = dbin (dk owlSameAs) (.v nmX) (.v nmY) from rfl,
      holds_dbin] at h6
  simp only [dv_val, dk_val] at h6
  erw [seqVal_X, seqVal_Y] at h6
  exact h6

end SeqConditions

/-! ## The clash rows

A clash row is falsity-headed, so it is not a `DRule` (a
`DatalogProgram` is definite by construction). `DNeg` carries the
premise list alone and reads as the universal closure of the NEGATED
conjunction — the `dExclusionSchema` / `rangeClashSchema` shape of
`Unified/DSchema.lean` and `Unified/RdfsSchema.lean`. -/

/-- A falsity-headed row: its premise atoms. -/
structure DNeg where
  atoms : List DAtom
  deriving DecidableEq, Repr

def DNeg.vars (r : DNeg) : List String := r.atoms.flatMap DAtom.varList

def DNeg.wfB (r : DNeg) : Bool := r.atoms.all DAtom.wfB

/-- The universally closed negated conjunction. -/
def DNeg.sentence (r : DNeg) : CL.Sentence :=
  .all (r.vars.map .plain) (.neg (.conj (r.atoms.map DAtom.sentence)))

theorem DNeg.wf_atom {r : DNeg} (h : r.wfB = true) :
    ∀ a ∈ r.atoms, a.wfB = true :=
  fun a ha => List.all_eq_true.mp h a ha

theorem DNeg.atom_scoped (r : DNeg) :
    ∀ a ∈ r.atoms, ∀ n ∈ a.varList, n ∈ r.vars :=
  fun a ha _ hn => List.mem_flatMap.mpr ⟨a, ha, hn⟩

theorem DNeg.vars_no_colon {r : DNeg} (h : r.wfB = true) :
    ∀ n ∈ r.vars, ':' ∉ n.toList := by
  intro n hn
  obtain ⟨a, ha, hna⟩ := List.mem_flatMap.mp hn
  exact DAtom.varList_no_colon (DNeg.wf_atom h a ha) n hna

/-- **The satisfaction lemma of the falsity-headed rows**: the sentence
is satisfied exactly when no valuation makes every premise true. -/
theorem satisfies_negSentence_iff (i : CL.Interp) {r : DNeg}
    (hwf : r.wfB = true) :
    CL.Satisfies i r.sentence ↔
      ∀ f : String → i.dom, ¬ (∀ a ∈ r.atoms, a.Holds i f) := by
  have hvars := DNeg.vars_no_colon hwf
  unfold CL.Satisfies DNeg.sentence
  simp only [CL.Sat]
  rw [satForall_plains]
  constructor
  · intro h f hb
    have hn := h f
    simp only [CL.Sat] at hn
    refine hn ?_
    rw [satAll_forall]
    intro u hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
    exact (sat_datom i hvars f _ (DNeg.wf_atom hwf a ha)
      (r.atom_scoped a ha)).mpr (hb a ha)
  · intro h f
    simp only [CL.Sat]
    intro hs
    refine h f ?_
    intro a ha
    rw [satAll_forall] at hs
    exact (sat_datom i hvars f _ (DNeg.wf_atom hwf a ha)
      (r.atom_scoped a ha)).mp (hs _ (List.mem_map.mpr ⟨a, ha, rfl⟩))

theorem dneg_wf_of {r : DNeg} (h : r.atoms.all DAtom.wfB = true) : r.wfB = true := h

/-- Fire a falsity-headed row: no valuation satisfies its premises. -/
theorem negRowFires {i : CL.Interp} {S : Schema} (hS : SatisfiesSchema i S)
    {r : DNeg} (hmem : S r.sentence) (hwf : r.wfB = true)
    (f : String → i.dom) (hb : ∀ a ∈ r.atoms, a.Holds i f) : False :=
  (satisfies_negSentence_iff i hwf).mp (hS _ hmem) f hb

/-- The twelve clash rows whose premises are all binary predications
over IRI constants, cardinality literals and variables. The three
max-cardinality rows (cls-maxc1, cls-maxqc1, cls-maxqc2) relate a term
to a cardinality LITERAL; since `Unified/Datalog.lean` carries
`DTerm.lit`, that is an ordinary `DAtom` argument and the rows are
here rather than in `OwlRlInterpCond`. -/
inductive RlNegRowId where
  | eqDiff1 | prpIrp | prpAsyp | prpPdw | prpNpa1 | prpNpa2
  | clsNothing2 | clsCom | caxDw
  | clsMaxc1 | clsMaxqc1 | clsMaxqc2
  deriving DecidableEq, Repr

def rlNegRowRule : RlNegRowId → DNeg
  | .eqDiff1 => ⟨[dbin (dk owlSameAs) (.v "x") (.v "y"),
      dbin (dk owlDifferentFrom) (.v "x") (.v "y")]⟩
  | .prpIrp => ⟨[dtyp (.v "p") (dk owlIrreflexiveProperty),
      dbin (.v "p") (.v "x") (.v "x")]⟩
  | .prpAsyp => ⟨[dtyp (.v "p") (dk owlAsymmetricProperty),
      dbin (.v "p") (.v "x") (.v "y"),
      dbin (.v "p") (.v "y") (.v "x")]⟩
  | .prpPdw => ⟨[dbin (dk owlPropertyDisjointWith) (.v "p") (.v "q"),
      dbin (.v "p") (.v "x") (.v "y"),
      dbin (.v "q") (.v "x") (.v "y")]⟩
  | .prpNpa1 => ⟨[dbin (dk owlSourceIndividual) (.v "w") (.v "x"),
      dbin (dk owlAssertionProperty) (.v "w") (.v "p"),
      dbin (dk owlTargetIndividual) (.v "w") (.v "y"),
      dbin (.v "p") (.v "x") (.v "y")]⟩
  | .prpNpa2 => ⟨[dbin (dk owlSourceIndividual) (.v "w") (.v "x"),
      dbin (dk owlAssertionProperty) (.v "w") (.v "p"),
      dbin (dk owlTargetValue) (.v "w") (.v "y"),
      dbin (.v "p") (.v "x") (.v "y")]⟩
  | .clsNothing2 => ⟨[dtyp (.v "x") (dk owlNothing)]⟩
  | .clsCom => ⟨[dbin (dk owlComplementOf) (.v "c") (.v "d"),
      dtyp (.v "x") (.v "c"), dtyp (.v "x") (.v "d")]⟩
  | .caxDw => ⟨[dbin (dk owlDisjointWith) (.v "c") (.v "d"),
      dtyp (.v "x") (.v "c"), dtyp (.v "x") (.v "d")]⟩
  | .clsMaxc1 => ⟨[dbin (dk owlMaxCardinality) (.v "x") (dlit litNni0),
      dbin (dk owlOnProperty) (.v "x") (.v "p"),
      dtyp (.v "u") (.v "x"),
      dbin (.v "p") (.v "u") (.v "y")]⟩
  | .clsMaxqc1 =>
      ⟨[dbin (dk owlMaxQualifiedCardinality) (.v "x") (dlit litNni0),
        dbin (dk owlOnProperty) (.v "x") (.v "p"),
        dbin (dk owlOnClass) (.v "x") (.v "c"),
        dtyp (.v "u") (.v "x"),
        dbin (.v "p") (.v "u") (.v "y"),
        dtyp (.v "y") (.v "c")]⟩
  | .clsMaxqc2 =>
      ⟨[dbin (dk owlMaxQualifiedCardinality) (.v "x") (dlit litNni0),
        dbin (dk owlOnProperty) (.v "x") (.v "p"),
        dbin (dk owlOnClass) (.v "x") (dk owlThing),
        dtyp (.v "u") (.v "x"),
        dbin (.v "p") (.v "u") (.v "y")]⟩

theorem rlNegRowRule_wf (row : RlNegRowId) : (rlNegRowRule row).wfB = true := by
  cases row <;> rfl

/-- **cax-adc**, at a distinct pair of member IRIs (the `RlNCondCaxAdc`
narrowing `RLSemantics.lean` records). -/
def negCaxAdc (c1 c2 : RDF.WfIri) : DNeg :=
  ⟨[dtyp (.v "y") (dk owlAllDisjointClasses),
    dbin (dk owlMembers) (.v "y") (.v "l"),
    dbin (dk uListMem) (.v "l") (dk c1),
    dbin (dk uListMem) (.v "l") (dk c2),
    dtyp (.v "z") (dk c1),
    dtyp (.v "z") (dk c2)]⟩

theorem negCaxAdc_wf (c1 c2 : RDF.WfIri) : (negCaxAdc c1 c2).wfB = true :=
  dneg_wf_of (by
    simp only [negCaxAdc, List.all_cons, List.all_nil,
      dtyp_wf (dv_wf "y" (by decide)) (dk_wf owlAllDisjointClasses),
      dbin_wf (dk_wf owlMembers) (dv_wf "y" (by decide)) (dv_wf "l" (by decide)),
      dbin_wf (dk_wf uListMem) (dv_wf "l" (by decide)) (dk_wf c1),
      dbin_wf (dk_wf uListMem) (dv_wf "l" (by decide)) (dk_wf c2),
      dtyp_wf (dv_wf "z" (by decide)) (dk_wf c1),
      dtyp_wf (dv_wf "z" (by decide)) (dk_wf c2), Bool.and_true])

/-- The clash part of the schema. -/
def owlRlClashSchema : Schema := fun s =>
  (∃ row : RlNegRowId, s = (rlNegRowRule row).sentence) ∨
  (∃ c1 c2 : RDF.WfIri, c1 ≠ c2 ∧ s = (negCaxAdc c1 c2).sentence)

section ClashConditions

variable {i : CL.Interp} (hN : SatisfiesSchema i owlRlClashSchema)
include hN

theorem ncond_eqDiff1 : RlNCondEqDiff1 (restrictInterp i) := by
  rintro x y ⟨h1, h2⟩
  refine negRowFires hN (Or.inl ⟨.eqDiff1, rfl⟩) (rlNegRowRule_wf .eqDiff1)
    (vals i [("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem ncond_prpIrp : RlNCondPrpIrp (restrictInterp i) := by
  rintro p x ⟨h1, h2⟩
  refine negRowFires hN (Or.inl ⟨.prpIrp, rfl⟩) (rlNegRowRule_wf .prpIrp)
    (vals i [("p", (restrictInterp i).iIri p), ("x", x)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

theorem ncond_prpAsyp : RlNCondPrpAsyp (restrictInterp i) := by
  rintro p x y ⟨h1, h2, h3⟩
  refine negRowFires hN (Or.inl ⟨.prpAsyp, rfl⟩) (rlNegRowRule_wf .prpAsyp)
    (vals i [("p", (restrictInterp i).iIri p), ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem ncond_prpPdw : RlNCondPrpPdw (restrictInterp i) := by
  rintro p1 p2 x y ⟨h1, h2, h3⟩
  refine negRowFires hN (Or.inl ⟨.prpPdw, rfl⟩) (rlNegRowRule_wf .prpPdw)
    (vals i [("p", (restrictInterp i).iIri p1), ("q", (restrictInterp i).iIri p2),
             ("x", x), ("y", y)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem ncond_prpNpa1 : RlNCondPrpNpa1 (restrictInterp i) := by
  rintro p w x y ⟨h1, h2, h3, h4⟩
  refine negRowFires hN (Or.inl ⟨.prpNpa1, rfl⟩) (rlNegRowRule_wf .prpNpa1)
    (vals i [("w", w), ("x", x), ("y", y),
             ("p", (restrictInterp i).iIri p)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem ncond_prpNpa2 : RlNCondPrpNpa2 (restrictInterp i) := by
  rintro p w x y ⟨h1, h2, h3, h4⟩
  refine negRowFires hN (Or.inl ⟨.prpNpa2, rfl⟩) (rlNegRowRule_wf .prpNpa2)
    (vals i [("w", w), ("x", x), ("y", y),
             ("p", (restrictInterp i).iIri p)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem ncond_clsNothing2 : RlNCondClsNothing2 (restrictInterp i) := by
  intro x h1
  refine negRowFires hN (Or.inl ⟨.clsNothing2, rfl⟩) (rlNegRowRule_wf .clsNothing2)
    (vals i [("x", x)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  exact h1

theorem ncond_clsCom : RlNCondClsCom (restrictInterp i) := by
  rintro c1 c2 x ⟨h1, h2, h3⟩
  refine negRowFires hN (Or.inl ⟨.clsCom, rfl⟩) (rlNegRowRule_wf .clsCom)
    (vals i [("c", c1), ("d", c2), ("x", x)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

/-- **cls-maxc1** — the `owl:maxCardinality 0` premise as `dlit
litNni0`. -/
theorem ncond_clsMaxc1 : RlNCondClsMaxc1 (restrictInterp i) := by
  rintro p x u y ⟨h1, h2, h3, h4⟩
  refine negRowFires hN (Or.inl ⟨.clsMaxc1, rfl⟩) (rlNegRowRule_wf .clsMaxc1)
    (vals i [("x", x), ("p", (restrictInterp i).iIri p), ("u", u),
             ("y", y)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- **cls-maxqc1**. -/
theorem ncond_clsMaxqc1 : RlNCondClsMaxqc1 (restrictInterp i) := by
  rintro p x u y c ⟨h1, h2, h3, h4, h5, h6⟩
  refine negRowFires hN (Or.inl ⟨.clsMaxqc1, rfl⟩)
    (rlNegRowRule_wf .clsMaxqc1)
    (vals i [("x", x), ("p", (restrictInterp i).iIri p), ("c", c),
             ("u", u), ("y", y)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-- **cls-maxqc2**. -/
theorem ncond_clsMaxqc2 : RlNCondClsMaxqc2 (restrictInterp i) := by
  rintro p x u y ⟨h1, h2, h3, h4, h5⟩
  refine negRowFires hN (Or.inl ⟨.clsMaxqc2, rfl⟩)
    (rlNegRowRule_wf .clsMaxqc2)
    (vals i [("x", x), ("p", (restrictInterp i).iIri p), ("u", u),
             ("y", y)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem ncond_caxDw : RlNCondCaxDw (restrictInterp i) := by
  rintro c1 c2 x ⟨h1, h2, h3⟩
  refine negRowFires hN (Or.inl ⟨.caxDw, rfl⟩) (rlNegRowRule_wf .caxDw)
    (vals i [("c", c1), ("d", c2), ("x", x)]) ?_
  intro a ha
  simp only [rlNegRowRule, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem ncond_caxAdc : RlNCondCaxAdc (restrictInterp i) := by
  rintro c1 c2 hne y l z ⟨h1, h2, h3, h4, h5, h6⟩
  refine negRowFires hN (Or.inr ⟨c1, c2, hne, rfl⟩) (negCaxAdc_wf c1 c2)
    (vals i [("y", y), ("l", l), ("z", z)]) ?_
  intro a ha
  simp only [negCaxAdc, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

end ClashConditions


/-! ## The schema, and the conditions it delivers

### What the schema does NOT carry, and why

FIVE of the 91 rows are not object-language sentences here (nine
before 2026-08-26). They are carried by the interpretation-class
condition bundle `OwlRlInterpCond` instead — the `EntailsSchema`
parameter the design document §2.2 calls the extension mechanism, and
the same device `RdfsDInterpCond` uses in
`Unified/RdfsSchema.lean`. Each has a structural reason:

* **prp-spo2, prp-key** quantify over a COLLECTION. Each needs a
  sentence family indexed by list length: the `rdf:first`/`rdf:rest`
  walk plus the chain or shared-value premises flattened into `n`-many
  body atoms, over generated variable names `l0..ln`, `q0..q(n-1)`,
  `v0..v(n-1)`.

  A reserved HELPER predicate would avoid the family, as it does for
  the other seven collection rows. The relation to encode is ternary
  (cell, subject, object) and `DAtom` is n-ary, so a ternary helper
  atom is legal — the earlier claim here that "a helper predicate
  cannot name it" was wrong; `RDF.Interp.iext` is binary, but the
  helper never has to appear in `restrictInterp i`. The reason not to
  take that route is `Unified/RdfTransport.lean`'s `liftInterp`, which
  reads `rel p args` as `False` at every arity other than 2. A schema
  row with a ternary head is therefore FALSE at `liftInterp r` for
  every RDF interpretation `r`, which is exactly the class of models
  schema-relative completeness needs
  (https://github.com/danbri/factoidal/issues/613 item 2). The
  per-length family keeps every row binary and costs no model.
* **cax-dw-comp, cls-maxqc1-comp, minc1-comp** have EXISTENTIAL heads
  (they mint a comprehension witness), which `DRule.definiteB`
  excludes. A `Schema` is a predicate on `CL.Sentence`, so nothing
  stops an existentially headed sentence from BEING in one; the
  question is whether it should be. Two costs decide it. (i) The head
  of `RlCondCompDw` is not a conjunction of atoms — `CompProps`
  carries two universally quantified implications and a five-variable
  one — so each row is a bespoke CL sentence with a bespoke
  satisfaction lemma, an instance of no family here. (ii) An
  existential head removes the least-model property the completeness
  direction of the stage-3 class rests on (`datalog_lfp_complete`, and
  the `rdfD1Shape_not_wf` exclusion `Unified/DatalogClosures.lean`
  pins). The recorded decision is to keep `owlRlSchema` definite and
  leave these three in the condition bundle. If they are ever
  admitted it should be as a SEPARATE sub-schema, so that the definite
  schema stays available for the completeness work.

The statement of `unified_owlRl_sound` names `OwlRlInterpCond`
explicitly, so the boundary is visible in the theorem, not only in
prose; `owlRlSchema_cardinality_rows` below pins the four rows that
left the bundle. -/

/-- **The OWL 2 RL schema**: the plain Horn rows, the guarded and
table-indexed families, and the clash rows.

Deviation from the design document §4.4: the schema takes no datatype
set `D`. The RL datatype rows (Table 7) range over the FIXED tables
`builtinDatatypeAxioms`, `xsdAxiomTriples` and `rangeIntersectLicenses`
of `OWL/RLRules.lean`, not over a recognised-datatype parameter. -/
def owlRlSchema : Schema :=
  schemaUnion owlRlHornSchema
    (schemaUnion owlRlFamilySchema
      (schemaUnion owlRlSeqSchema owlRlClashSchema))

/-- The nine rows the schema does not carry, as an interpretation-class
condition (see the section header for why each one is here). -/
def OwlRlInterpCond (i : CL.Interp) : Prop :=
  RlCondCompDw (restrictInterp i) ∧
  RlCondCompMqc (restrictInterp i) ∧
  RlCondMinc1 (restrictInterp i)

theorem satisfiesSchema_owlRl_parts {i : CL.Interp}
    (hS : SatisfiesSchema i owlRlSchema) :
    SatisfiesSchema i owlRlHornSchema ∧ SatisfiesSchema i owlRlFamilySchema ∧
      SatisfiesSchema i owlRlSeqSchema ∧ SatisfiesSchema i owlRlClashSchema := by
  rw [owlRlSchema, satisfiesSchema_union_iff, satisfiesSchema_union_iff,
      satisfiesSchema_union_iff] at hS
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2⟩

/-- **The four cardinality rows are carried by the SCHEMA**, with no
appeal to `OwlRlInterpCond`. This is the shrinkage of the condition
bundle stated as a theorem rather than left in the definition of
`OwlRlInterpCond`: before 2026-08-26 each of these four was a
hypothesis on the interpretation. -/
theorem owlRlSchema_cardinality_rows {i : CL.Interp}
    (hS : SatisfiesSchema i owlRlSchema) :
    RlCondClsMaxc2 (restrictInterp i) ∧
    RlNCondClsMaxc1 (restrictInterp i) ∧
    RlNCondClsMaxqc1 (restrictInterp i) ∧
    RlNCondClsMaxqc2 (restrictInterp i) := by
  obtain ⟨hH, -, -, hN⟩ := satisfiesSchema_owlRl_parts hS
  exact ⟨cond_clsMaxc2 hH, ncond_clsMaxc1 hN, ncond_clsMaxqc1 hN,
         ncond_clsMaxqc2 hN⟩

/-- **The two list-valued rows are carried by the SCHEMA**, through
the per-length sentence families, with no appeal to `OwlRlInterpCond`.
Before 2026-08-26 both were hypotheses on the interpretation. -/
theorem owlRlSchema_seq_rows {i : CL.Interp}
    (hS : SatisfiesSchema i owlRlSchema) :
    RlCondPrpSpo2 (restrictInterp i) ∧ RlCondPrpKey (restrictInterp i) := by
  obtain ⟨-, -, hQ, -⟩ := satisfiesSchema_owlRl_parts hS
  exact ⟨cond_prpSpo2 hQ, cond_prpKey hQ⟩

/-- **The bridge**: schema satisfaction plus the three bundled rows give
the full `RlConditions` / `RlClashConditions` pair over the restricted
interpretation. -/
theorem owlRlSchema_conditions {i : CL.Interp}
    (hS : SatisfiesSchema i owlRlSchema) (hc : OwlRlInterpCond i) :
    RlConditions (restrictInterp i) ∧ RlClashConditions (restrictInterp i) := by
  obtain ⟨hH, hF, hQ, hN⟩ := satisfiesSchema_owlRl_parts hS
  obtain ⟨kCompDw, kCompMqc, kMinc1⟩ := hc
  refine ⟨?_, ?_⟩
  · exact
    { eqRefS := cond_eqRefS hH
      eqRefP := cond_eqRefP hF
      eqRefO := cond_eqRefO hH
      eqSym := cond_eqSym hH
      eqTrans := cond_eqTrans hH
      eqRepS := cond_eqRepS hH
      eqRepP := cond_eqRepP hH
      eqRepO := cond_eqRepO hH
      prpDom := cond_prpDom hH
      prpRng := cond_prpRng hH
      prpFp := cond_prpFp hH
      prpIfp := cond_prpIfp hH
      prpSymp := cond_prpSymp hH
      prpTrp := cond_prpTrp hH
      prpSpo1 := cond_prpSpo1 hH
      prpSpo2 := cond_prpSpo2 hQ
      prpEqp1 := cond_prpEqp1 hH
      prpEqp2 := cond_prpEqp2 hH
      prpInv1 := cond_prpInv1 hH
      prpInv2 := cond_prpInv2 hH
      prpKey := cond_prpKey hQ
      clsThing := cond_clsThing hH
      clsNothing1 := cond_clsNothing1 hH
      clsInt1 := cond_clsInt1 hH
      typedAllBase := cond_typedAllBase hH
      typedAllStep := cond_typedAllStep hH
      listMemBase := cond_listMemBase hH
      listMemStep := cond_listMemStep hH
      clsInt2 := cond_clsInt2 hH
      clsUni := cond_clsUni hH
      clsSvf1 := cond_clsSvf1 hH
      clsSvf2 := cond_clsSvf2 hH
      clsAvf := cond_clsAvf hH
      clsHv1 := cond_clsHv1 hH
      clsHv2 := cond_clsHv2 hH
      clsMaxc2 := cond_clsMaxc2 hH
      clsOo := cond_clsOo hH
      caxSco := cond_caxSco hH
      caxEqc1 := cond_caxEqc1 hH
      caxEqc2 := cond_caxEqc2 hH
      scmClsSelf := cond_scmClsSelf hH
      scmClsEqc := cond_scmClsEqc hH
      scmClsThing := cond_scmClsThing hH
      scmClsNothing := cond_scmClsNothing hH
      scmSco := cond_scmSco hH
      scmEqc1a := cond_scmEqc1a hH
      scmEqc1b := cond_scmEqc1b hH
      scmEqc2 := cond_scmEqc2 hH
      scmSpo := cond_scmSpo hH
      scmEqp1a := cond_scmEqp1a hH
      scmEqp1b := cond_scmEqp1b hH
      scmEqp2 := cond_scmEqp2 hH
      scmDom1 := cond_scmDom1 hH
      scmDom2 := cond_scmDom2 hH
      scmRng1 := cond_scmRng1 hH
      scmRng2 := cond_scmRng2 hH
      scmInt := cond_scmInt hH
      scmUni := cond_scmUni hH
      eqDiffSym := cond_eqDiffSym hH
      pdwToDiff := cond_pdwToDiff hH
      caxDwToDiff := cond_caxDwToDiff hH
      fpDiffToDiff := cond_fpDiffToDiff hH
      ifpDiffToDiff := cond_ifpDiffToDiff hH
      chainToTrans := cond_chainToTrans hH
      prpRflS := cond_prpRflS hH
      prpRflO := cond_prpRflO hH
      xsdAxioms := cond_xsdAxioms hF
      dtRangeIntersect := cond_dtRangeIntersect hF
      dtType1Builtin := cond_dtType1Builtin hF
      caxAdcToDw := cond_caxAdcToDw hF
      invFlipDomRng := cond_invFlipDomRng hH
      invFlipRngDom := cond_invFlipRngDom hH
      invFlipDomRngRev := cond_invFlipDomRngRev hH
      invFlipRngDomRev := cond_invFlipRngDomRev hH
      compDw := kCompDw
      compMqc := kCompMqc
      minc1 := kMinc1 }
  · exact
    { eqDiff1 := ncond_eqDiff1 hN
      prpIrp := ncond_prpIrp hN
      prpAsyp := ncond_prpAsyp hN
      prpPdw := ncond_prpPdw hN
      prpNpa1 := ncond_prpNpa1 hN
      prpNpa2 := ncond_prpNpa2 hN
      clsNothing2 := ncond_clsNothing2 hN
      clsCom := ncond_clsCom hN
      clsMaxc1 := ncond_clsMaxc1 hN
      clsMaxqc1 := ncond_clsMaxqc1 hN
      clsMaxqc2 := ncond_clsMaxqc2 hN
      caxDw := ncond_caxDw hN
      caxAdc := ncond_caxAdc hN }

end L4Factoidal.Unified
