/-
L4Factoidal.OWL.RLRules — the SPECIFICATION of the OWL 2 RL/RDF
rule-based entailment layer: the table rows as an inductive derivation
relation, and the no-consequent (clash) rows as a separate inductive
proposition.

Ports the rule transcription of `formal/fstar/OWL.RL.Spec.fst` — that
module writes each row of

  OWL 2 Web Ontology Language Profiles (2nd ed.), §4.3
  "Reasoning in OWL 2 RL and RDF Graphs using Rules"
  https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules

as an F* `prop` (`eq_ref_derives`, `prp_trp_derives`, ...); this module
writes the same rows as constructors of one inductive relation. Every
constructor cites its table id.

`RLClosure.lean` is the executable closure; the two are tied together
by `RLTheorems.lean` (T2 soundness: every triple the closure computes
is derivable here — this is the per-row LICENSING theorem the F*
`OWL.RL.Refinement.fst` states and `docs/theorem-registry.md` §1
tracks; T4: everything derivable here is in a saturated closure).

## Which rows are here

FIFTY rows, in the table order of the Recommendation:

* Table 4, equality — eq-ref (three conclusions, three constructors),
  eq-sym, eq-trans, eq-rep-s, eq-rep-p, eq-rep-o.
* Table 4, properties — prp-dom, prp-rng, prp-fp, prp-ifp, prp-symp,
  prp-trp, prp-spo1, prp-spo2, prp-eqp1, prp-eqp2, prp-inv1, prp-inv2,
  prp-key.
* Table 5, classes — cls-thing, cls-nothing1, cls-int1, cls-int2,
  cls-uni, cls-svf1, cls-svf2, cls-avf, cls-hv1, cls-hv2, cls-maxc2,
  cls-oo.
* Table 6, class axioms — cax-sco, cax-eqc1, cax-eqc2.
* Table 8, schema vocabulary — scm-cls (four conclusions), scm-sco,
  scm-eqc1 (two), scm-eqc2, scm-spo, scm-eqp1 (two), scm-eqp2,
  scm-dom1, scm-dom2, scm-rng1, scm-rng2, scm-int, scm-uni.

The clash rows are `Clash`: eq-diff1, prp-irp, prp-asyp, prp-pdw,
prp-npa1, prp-npa2, cls-nothing2, cls-com, cls-maxc1, cls-maxqc1,
cls-maxqc2, cax-dw, cax-adc.

## Which rows are NOT here, and why

* **Table 7 (dt-type1, dt-type2, dt-eq, dt-diff, dt-not-type).** These
  rows quantify over DATA VALUES ("for each literal lt in the value
  space of datatype dt"), and a value space is a property of the
  DATATYPE MAP, not of the graph. `OWL.RL.Spec.fst` states them
  PARAMETRICALLY for exactly that reason — each F* row takes the
  value-level relation as an argument and the module fixes no datatype
  map. This port fixes no datatype map either, so the rows have
  nothing to instantiate; they are left out rather than baked to one
  interpretation. (`dt-not-type` was on this port's wish list; this is
  why it is absent.)
* **eq-diff2, eq-diff3, prp-adp, cax-adp** — the owl:AllDifferent /
  owl:AllDisjointProperties clash rows over LIST[...]. Same shape as
  cax-adc, which IS ported; omitted only for size.
* **cls-maxc1 is a clash, cls-maxqc3/cls-maxqc4 are not ported** —
  the qualified-cardinality DERIVING rows need the onClass premise
  threaded through two typed witnesses; the two qualified CLASH rows
  (cls-maxqc1, cls-maxqc2) are ported.
* **scm-op, scm-dp, scm-hv, scm-svf1, scm-svf2, scm-avf1, scm-avf2.**
  Five-premise Table 8 restriction-comparison rows. The F* engine
  ledger in `OWL.RL.Spec.fst` (landing 4) lists no `owl_rule_*`
  function for any of them either, so nothing is lost against the F*
  engine's own row coverage.
* **The comprehension-witness `[ext]` layer** —
  `svf2_existential_witness`, `minc1_bridge`, `cls_hasself1/2`,
  `cls_svf_thing_*`, and the `#236` `cls_maxqc_comp` anchor machinery.
  Every one of them MINTS A BLANK NODE, so porting them means picking a
  skolem-naming scheme and proving the fixpoint still terminates under
  it. Not attempted here; named, not hidden.
* **`[mode]` rules** — `named_equivClass_to_sameAs_mode` and the
  RDF-Based full meta axioms fire only under a catalog semantics mode.
  There are no semantics modes on the Lean side.

## The `[ext]` rows that ARE here

TEN rows in a section of their own at the end of `Derives`, each
carrying the OWL 2 RDF-Based Semantics condition that makes it
truth-preserving instead of a W3C table id, and each naming the F*
rule it ports:

* differentFrom synthesis — `eqDiffSym`, `pdwToDiff`, `caxDwToDiff`,
  `fpDiffToDiff`, `ifpDiffToDiff`.
* `chainToTrans` — a self-chain axiom is transitivity.
* `prpRfl` — `owl:ReflexiveProperty` over the graph's IRIs.
* `xsdAxioms`, `dtRangeIntersect` — Table 7's datatype rows over the
  XSD datatype map.
* `premiseFreeAxiom` — the triples that hold with no premise at all:
  Table 7's dt-type1 over the two builtin datatypes, and the
  annotation-property axiomatic triples of OWL 2 RDF-Based Semantics
  Section 6 (Tables 6.2 and 6.5).

Two of them carry an ASSUMPTION beyond the graph: `xsdAxioms` and
`dtRangeIntersect` assume the interpretation's datatype map recognises
the XSD datatypes with the XSD 1.1 §3.4 value spaces. That assumption
is written out as `XsdValueSpaceSubset` and the tables list exactly
which containments are relied on; `xsdIntegerDecimal_subset` and
`xsdIntInteger_subset` discharge the two edges the Lean datatype map of
`RDF/Datatypes.lean` actually models. The rest is assumed, and marked
as assumed, rather than asserted silently.

Table 7's dt-eq, dt-diff and dt-type2 rows are STRUCTURALLY
UNREACHABLE in this tree and it is worth saying why: their conclusions
put a LITERAL in subject position (`T(lt1, owl:sameAs, lt2)`), and
`RDF/Core.lean`'s `Subject` is an IRI or a blank node with no literal
case — RDF 1.1 Concepts §3.1, which the OWL 2 RL rule table steps
outside of by writing generalised triples. Porting them means widening
`Subject` across the whole tree. Not a gap in this module's coverage of
the table; a consequence of the term algebra underneath it.

## Faithful-port notes

1. **Premises are `Derives`, not graph membership.** The F* rows read
   their premises with `memP u g` — each row is one step. Here a row's
   triple premises are themselves `Derives g`, so the relation is the
   closure of the one-step rules ("derivable in any number of steps"),
   which is what the fixpoint computes. Same choice as
   `L4Factoidal/RDFS/RdfsCore.lean`.

2. **`subj_term` joins are written with `Subject.toTerm`, not a
   `toSubject?` side condition.** Where the F* row writes
   `subj_term ys == u.o` (its "delta GR" — an object position feeding
   a conclusion's subject position), this port writes the premise's
   object slot as `ys.toTerm` directly. The two are equivalent
   (`toSubject?_eq_some_iff` below: `t.toSubject? = some s ↔ t =
   s.toTerm`) and the second needs no hypothesis, which keeps the
   constructors readable and the proofs one step shorter.

3. **The LIST[...] premise becomes two relations.** `ListMember g head
   t` — "t is a member of the rdf:first/rdf:rest collection headed by
   `head`" — is what the rows needing SOME member use (cls-int2,
   cls-uni, cls-oo, scm-int, scm-uni, cax-adc). `ListDenotes g head
   elems` — "the collection headed by `head` is exactly `elems`" — is
   what the rows needing the WHOLE sequence use (cls-int1, prp-spo2,
   prp-key). Both read premises from `g` directly, as the F*
   `owl_list_denotes` does; only triple premises are lifted to
   `Derives`.

4. **cax-adc: distinct TERMS, not distinct POSITIONS.** The F*
   `two_distinct_members` says ci and cj occur at different INDICES of
   the list, which fires the clash on a single `x rdf:type C` when C is
   listed twice. This port requires `ci ≠ cj`. That is strictly weaker
   (it detects fewer clashes) and it is the reading that matches the
   row's intent, so the deviation is recorded rather than inherited.

Model theory (`OWL.Semantics.fst`, `OWL.Semantics.Soundness.fst`) is
NOT ported — see the header of `RLTheorems.lean` for the statement
shape and what is and is not claimed.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.RDF.Datatypes
import L4Factoidal.OWL.Vocabulary

namespace L4Factoidal.OWL.RL

open L4Factoidal.RDF

/-! ## A term is a subject exactly when it is some subject's term form

The bridge between the two ways of writing the table's `subj_term`
joins. Used by the engine proofs, which compute with `toSubject?`,
against the rules below, which are written with `Subject.toTerm`. -/

theorem toSubject?_toTerm (s : Subject) : s.toTerm.toSubject? = some s := by
  cases s <;> rfl

theorem toSubject?_eq_some_iff {t : Term} {s : Subject} :
    t.toSubject? = some s ↔ t = s.toTerm := by
  constructor
  · intro h
    cases t <;> simp only [Term.toSubject?] at h <;>
      (first
        | cases h; rfl
        | exact absurd h (by simp))
  · intro h; subst h; exact toSubject?_toTerm s

/-! ## RDF collections — the table's `LIST[?x, ?e1, ..., ?en]` premise

RDF 1.1 Schema §5.1: a collection is an rdf:first/rdf:rest chain
terminated by rdf:nil. -/

/-- `ListMember g head e` — `e` is a member of the collection headed by
`head`. The relation the rows needing SOME list member read. A cyclic
chain still has members; only `ListDenotes` insists on termination. -/
inductive ListMember (g : Graph) : Term → Term → Prop where
  /-- The head cell's own `rdf:first` value is a member. -/
  | here {node : Subject} {e : Term}
      (hf : (⟨node, rdfFirst, e⟩ : Triple) ∈ g) :
      ListMember g node.toTerm e
  /-- Anything the tail holds, the head holds. -/
  | there {node : Subject} {tail e : Term}
      (hr : (⟨node, rdfRest, tail⟩ : Triple) ∈ g)
      (h : ListMember g tail e) :
      ListMember g node.toTerm e

/-- `ListDenotes g head elems` — the collection headed by `head` is
EXACTLY the sequence `elems`. Port of the F* `owl_list_denotes`: a
cyclic or rdf:nil-less chain denotes nothing.

The `hnil` side condition on `cons` says a non-empty collection is not
headed by `rdf:nil`. RDF Schema §5.1 gives `rdf:nil` one meaning — the
empty list — so a graph that also hangs an `rdf:first` off it is
malformed, and reading it as a non-empty collection is not a reading
worth having. The F* `owl_list_denotes` omits the guard and so admits
both readings of such a graph; this port takes the one the executable
walk takes, which is what makes spec and engine agree in BOTH
directions (`listSeqs_sound` and `exists_fuel_listSeqs`). -/
inductive ListDenotes (g : Graph) : Term → List Term → Prop where
  | nil : ListDenotes g (Term.iri rdfNil) []
  | cons {node : Subject} {e tail : Term} {rest : List Term}
      (hnil : node.toTerm ≠ Term.iri rdfNil)
      (hf : (⟨node, rdfFirst, e⟩ : Triple) ∈ g)
      (hr : (⟨node, rdfRest, tail⟩ : Triple) ∈ g)
      (ht : ListDenotes g tail rest) :
      ListDenotes g node.toTerm (e :: rest)

/-- cls-int1's batched premise: `T(?y, rdf:type, ?ci)` for every member
of the list. Port of the F* `types_all`. -/
inductive TypesAll (g : Graph) (y : Subject) : List Term → Prop where
  | nil : TypesAll g y []
  | cons {c : Term} {rest : List Term}
      (h : (⟨y, rdfType, c⟩ : Triple) ∈ g)
      (hr : TypesAll g y rest) :
      TypesAll g y (c :: rest)

/-- prp-spo2's chain of data triples: consecutive links meet at a
shared node (one's object is the next's subject), predicates drawn in
order from the property-chain list. Port of the F* `chain_holds`. -/
inductive ChainHolds (g : Graph) : Subject → List WfIri → Term → Prop where
  /-- An empty chain reaches its own start. -/
  | nil {s : Subject} : ChainHolds g s [] s.toTerm
  /-- The last link's object is the chain's end — no subject
  eligibility is needed there. -/
  | last {s : Subject} {p : WfIri} {o : Term}
      (h : (⟨s, p, o⟩ : Triple) ∈ g) :
      ChainHolds g s [p] o
  /-- An interior link: its object must be usable as the next link's
  subject. -/
  | step {s mid : Subject} {p : WfIri} {rest : List WfIri} {fin : Term}
      (h : (⟨s, p, mid.toTerm⟩ : Triple) ∈ g)
      (hr : ChainHolds g mid rest fin) :
      ChainHolds g s (p :: rest) fin

/-- prp-key's paired premises: for each key property, the two
individuals carry SOME shared value. Port of the F*
`shares_key_values`. -/
inductive SharesKeyValues (g : Graph) (x y : Subject) : List WfIri → Prop where
  | nil : SharesKeyValues g x y []
  | cons {p : WfIri} {o : Term} {rest : List WfIri}
      (hx : (⟨x, p, o⟩ : Triple) ∈ g)
      (hy : (⟨y, p, o⟩ : Triple) ∈ g)
      (hr : SharesKeyValues g x y rest) :
      SharesKeyValues g x y (p :: rest)

/-! ## The `[ext]` layer — tables and guards

Everything in this section serves a row of the `[ext]` block at the end
of `Derives`. None of it transcribes a W3C table row; each item's
justification is the OWL 2 RDF-Based Semantics condition quoted in the
row that uses it.

  OWL 2 Web Ontology Language RDF-Based Semantics (2nd ed.), §5
  https://www.w3.org/TR/owl2-rdf-based-semantics/#Semantic_Conditions

-/

/-- The IRIs mentioned by a triple in an IRI POSITION — subject,
predicate, or object. A literal's datatype IRI is NOT a mention: the
datatype is part of the literal's value, not a term of the graph, which
is the same reading the F* `triple_mentions_xsd` takes. -/
def tripleIris (t : Triple) : List WfIri :=
  (match t.s with | .iri i => [i] | _ => []) ++ [t.p] ++
  (match t.o with | .iri i => [i] | _ => [])

/-- Does this triple mention an IRI in the XSD namespace? Half of the
guard on the `xsdAxioms` row: a graph that never names an XSD datatype
gets no XSD tower, so the tower cannot pollute an unrelated closure. -/
def mentionsXsd (t : Triple) : Bool := (tripleIris t).any iriInXsdNs

/-- The XSD numeric subtype tower, as (subtype, supertype) pairs.

**Justification.** Each edge asserts `sub rdfs:subClassOf sup`. Under
RDF 1.1 Semantics §7 a recognised datatype IRI `d` denotes a datatype
with `ICEXT(I(d))` its value space, so the triple is true in every
D-interpretation whose `D` recognises both IRIs and whose value spaces
satisfy `valueSpace(sub) ⊆ valueSpace(sup)`. XSD 1.1 §3.4 states each
containment below ("the value space of byte is a subset of that of
short", and so on up the tower). `XsdValueSpaceSubset` names that
assumption; `xsdIntegerDecimal_subset` discharges the one edge the
Lean datatype map of `RDF/Datatypes.lean` actually models. The rest is
carried as an assumption, marked `[ext]`, not silently asserted. -/
def xsdHierarchyEdges : List (WfIri × WfIri) :=
  [ (xsdByte, xsdShort), (xsdShort, xsdIntIri), (xsdIntIri, xsdLong),
    (xsdLong, xsdInteger),
    (xsdPositiveInteger, xsdNonNegativeInteger),
    (xsdUnsignedByte, xsdUnsignedShort),
    (xsdUnsignedShort, xsdUnsignedInt),
    (xsdUnsignedInt, xsdUnsignedLong),
    (xsdUnsignedLong, xsdNonNegativeInteger),
    (xsdNonNegativeInteger, xsdInteger),
    (xsdNegativeInteger, xsdNonPositiveInteger),
    (xsdNonPositiveInteger, xsdInteger),
    (xsdInteger, xsdDecimal),
    (xsdDecimal, xsdDouble) ]

/-- Every XSD datatype of the tower, each of which is an
`rdfs:Datatype` (RDF 1.1 Semantics §7: a recognised datatype IRI is of
type `rdfs:Datatype` in every D-interpretation that recognises it). -/
def xsdAllDatatypes : List WfIri :=
  [ xsdString, xsdBoolean, xsdDouble, xsdDecimal, xsdInteger,
    xsdLong, xsdIntIri, xsdShort, xsdByte,
    xsdNonNegativeInteger, xsdPositiveInteger,
    xsdUnsignedLong, xsdUnsignedInt, xsdUnsignedShort, xsdUnsignedByte,
    xsdNonPositiveInteger, xsdNegativeInteger ]

/-- The triples the `xsdAxioms` row emits: the tower as `rdfs:subClassOf`
edges, plus an `rdf:type rdfs:Datatype` for every member of it. -/
def xsdAxiomTriples : List Triple :=
  xsdHierarchyEdges.map
    (fun e => (⟨Subject.iri e.1, rdfsSubClassOf, Term.iri e.2⟩ : Triple)) ++
  xsdAllDatatypes.map
    (fun i => (⟨Subject.iri i, rdfType, Term.iri rdfsDatatype⟩ : Triple))

/-- The datatype-range intersection table of the `dtRangeIntersect` row.

**Justification.** `rdfs:range` is not exclusive: two range axioms on
one property constrain its values to the INTERSECTION of the two value
spaces (RDF 1.1 Semantics §9, rdfs3 applies for each range
independently). Each entry `(d1, d2, outs)` names a `d3 ∈ outs` whose
value space CONTAINS `valueSpace(d1) ∩ valueSpace(d2)`, so asserting
`p rdfs:range d3` adds no constraint that was not already implied:

* `short` caps at 32767 and `unsignedInt`/`unsignedLong` are
  non-negative, so the intersection lies inside `unsignedShort`;
* `byte` caps at 127 and `unsignedInt` is non-negative, so the
  intersection lies inside `unsignedByte`;
* `nonNegativeInteger ∩ nonPositiveInteger = {0}`, which lies inside
  both `byte` and `unsignedByte`.

Those are XSD 1.1 §3.4 facts about the value spaces, not graph facts;
they are the assumption this `[ext]` row carries. The table is
test-backed rather than the full datatype product, exactly as the F*
`xsd_range_intersections` banner records. -/
def xsdRangeIntersections : List (WfIri × WfIri × List WfIri) :=
  [ (xsdShort, xsdUnsignedInt, [xsdUnsignedShort]),
    (xsdShort, xsdUnsignedLong, [xsdUnsignedShort]),
    (xsdByte, xsdUnsignedInt, [xsdUnsignedByte]),
    (xsdNonNegativeInteger, xsdNonPositiveInteger, [xsdByte, xsdUnsignedByte]) ]

/-- Does the table license `d3` as a range for a property already ranged
over both `d1` and `d2`? Symmetric in `d1`/`d2`, as the two range
axioms are. -/
def rangeIntersectLicenses (d1 d2 d3 : WfIri) : Bool :=
  xsdRangeIntersections.any (fun e =>
    ((e.1 == d1 && e.2.1 == d2) || (e.1 == d2 && e.2.1 == d1)) &&
    e.2.2.contains d3)

/-- The two `rdfs:Datatype` typings every D-interpretation supports with
no premise. RDF 1.1 Semantics §7 makes `xsd:string` recognised by every
D-interpretation; OWL 2 Syntax §4.1 puts `xsd:integer` in the datatype
map every OWL 2 ontology has. Table 7's dt-type1 then types each of
them `rdfs:Datatype`. -/
def builtinDatatypeAxioms : List Triple :=
  [ ⟨Subject.iri xsdInteger, rdfType, Term.iri rdfsDatatype⟩,
    ⟨Subject.iri xsdString, rdfType, Term.iri rdfsDatatype⟩ ]

/-- **The annotation-property axiomatic triples of OWL 2 RDF-Based
Semantics Section 6**, transcribed.

Section 6 "Axiomatic Triples" states triples that are true in every
OWL 2 RDF-Based interpretation, so a graph entails each of them with no
premise. Five come from Table 6.2 "Axiomatic Triples for the Properties
of the OWL 2 RDF-Based Vocabulary":

    owl:versionInfo rdf:type owl:AnnotationProperty .
    owl:deprecated rdf:type owl:AnnotationProperty .
    owl:priorVersion rdf:type owl:AnnotationProperty .
    owl:backwardCompatibleWith rdf:type owl:AnnotationProperty .
    owl:incompatibleWith rdf:type owl:AnnotationProperty .

and four from Table 6.5 "Additional Axiomatic Triples for Classes and
Properties of the RDFS Vocabulary":

    rdfs:comment rdf:type owl:AnnotationProperty .
    rdfs:label rdf:type owl:AnnotationProperty .
    rdfs:seeAlso rdf:type owl:AnnotationProperty .
    rdfs:isDefinedBy rdf:type owl:AnnotationProperty .

The model-theoretic ground is Table 5.3 "Semantic Conditions for the
Vocabulary Properties", which puts each of the nine IRIs in the part
IOAP, together with Table 5.2 "Semantic Conditions for the Vocabulary
Classes", which gives `ICEXT(I(owl:AnnotationProperty)) = IOAP`.

The nine `rdfbased-sem-prop-*-type` conformance cases ask exactly this:
their premise ontology is empty and their conclusion is one of these
triples.

Only the `owl:AnnotationProperty` typings are transcribed here. The
domain, range and `rdf:Property` rows of the same tables are a separate
landing, because every unconditional triple is also an eq-ref seed and
the cost of that feedback is measured per landing (see the
`drivesXsdAxioms` doc comment for the case that paid for the rule). -/
def vocabAnnotationPropertyAxioms : List Triple :=
  [ ⟨Subject.iri rdfsComment, rdfType, Term.iri owlAnnotationProperty⟩,
    ⟨Subject.iri rdfsLabel, rdfType, Term.iri owlAnnotationProperty⟩,
    ⟨Subject.iri rdfsSeeAlso, rdfType, Term.iri owlAnnotationProperty⟩,
    ⟨Subject.iri rdfsIsDefinedBy, rdfType, Term.iri owlAnnotationProperty⟩,
    ⟨Subject.iri owlVersionInfo, rdfType, Term.iri owlAnnotationProperty⟩,
    ⟨Subject.iri owlDeprecated, rdfType, Term.iri owlAnnotationProperty⟩,
    ⟨Subject.iri owlPriorVersion, rdfType, Term.iri owlAnnotationProperty⟩,
    ⟨Subject.iri owlBackwardCompatibleWith, rdfType,
     Term.iri owlAnnotationProperty⟩,
    ⟨Subject.iri owlIncompatibleWith, rdfType,
     Term.iri owlAnnotationProperty⟩ ]

/-- **The premise-free axiom triples.** Everything the `premiseFreeAxiom`
row asserts with no premise at all: the two builtin `rdfs:Datatype`
typings of Table 7's dt-type1, and the nine annotation-property typings
of OWL 2 RDF-Based Semantics Table 5.3. -/
def premiseFreeAxioms : List Triple :=
  builtinDatatypeAxioms ++ vocabAnnotationPropertyAxioms

/-- The predicates under which an XSD IRI in the OBJECT slot is being
used as a datatype rather than merely named. The `xsdAxioms` guard
reads this list. -/
def datatypePositionPredicates : List WfIri :=
  [ rdfsRange, rdfsDomain, rdfType, rdfsSubClassOf,
    owlEquivalentClass, owlDisjointWith, owlComplementOf,
    owlOnClass, owlSomeValuesFrom, owlAllValuesFrom ]

/-- The `xsdAxioms` guard: the driving triple USES an XSD IRI as a
datatype — an XSD object under one of the class/datatype predicates
above.

This is NARROWER than the F* `graph_mentions_xsd_iri`, which fires on
any XSD IRI in any position, and the narrowing is deliberate.
`premiseFreeAxiom` puts `xsd:integer rdf:type rdfs:Datatype` into EVERY
closure with no premise; eq-ref then derives `xsd:integer owl:sameAs
xsd:integer` from it, and under the "mentions" guard THAT triple drives
the whole XSD tower plus its `scm-sco` transitive closure into every
closure this engine ever computes. Measured on the OWL corpus,
2026-08-22: 116 triples and 6 rounds for a 3-triple `rdfs:subClassOf`
fixture that has nothing to do with datatypes, `type-consistency` up
from 6417 ms to 11622 ms, and the `RLTests` idempotence guards (which
assert saturation at a fixed fuel) red. Restricting to a datatype
POSITION cuts the feedback loop at its source: `owl:sameAs` is not a
datatype position, so eq-ref cannot re-seed the row. The rows that
motivate the tower — WebOnt-I5.8-006/008/009, premise `p rdfs:range
xsd:byte` — are all `rdfs:range`, so nothing they need is lost. -/
def drivesXsdAxioms (t : Triple) : Bool :=
  datatypePositionPredicates.contains t.p &&
  (match t.o with | .iri i => iriInXsdNs i | _ => false)

/-- The shape of the assumption the XSD tables carry: the value space
of `sub` is inside the value space of `sup`, as `RDF/Datatypes.lean`'s
modelled datatype map decides it. Stated over the modelled map so it is
a real, checkable claim rather than a placeholder; the tower edges over
datatypes that map does not model are assumed, and named as assumed. -/
def XsdValueSpaceSubset (sub sup : WfIri) : Prop :=
  ∀ l : Literal, l.datatype = sub → RDF.valueInSpace l sup = true

/-- The one tower edge the Lean datatype map models, discharged.
`RDF/Datatypes.lean`'s `valueInSpace` knows `int ⊂ integer ⊂ decimal`
and nothing else, so this is the whole of what can be proved here
rather than assumed. -/
theorem xsdIntegerDecimal_subset : XsdValueSpaceSubset xsdInteger xsdDecimal := by
  intro l h
  simp [RDF.valueInSpace, h]

/-- The second modelled edge: `xsd:int ⊂ xsd:integer`. -/
theorem xsdIntInteger_subset : XsdValueSpaceSubset RDF.xsdInt xsdInteger := by
  intro l h
  simp [RDF.valueInSpace, h]

/-! ### Comprehension witnesses

RDF-Based Semantics §5.14 ("Comprehension Conditions") asserts that
certain class expressions EXIST for every argument: for every class `c`
there is a class denoting its complement, and for every property `p`
and cardinality `n` there is a `minCardinality` restriction on `p`. A
rule engine states that existence by minting a blank node, which is
what an existential IS in RDF (RDF 1.1 Semantics §1.5).

The skolem name is a FUNCTION of the argument, not a counter. That is
what makes the emission idempotent, so the fixpoint loop's "length did
not change" stopping rule still fires: a second round over the same
graph mints the same node and `addOne` drops it. A counter would make
every round grow the graph and the loop would run to its fuel bound.
The `__rl_` prefix is the same convention the F* engine's
`canonical_*_bnode` functions use. -/

/-- The blank node denoting the complement class of `c`. -/
def complementWitness (c : WfIri) : Subject :=
  Subject.bnode ("__rl_comp__" ++ c.val)

/-- The comprehension pair for `c`'s complement: it is a class, and it
is the complement of `c`. -/
def complementWitnessPair (c : WfIri) : List Triple :=
  [ ⟨complementWitness c, rdfType, Term.iri owlClass⟩,
    ⟨complementWitness c, owlComplementOf, Term.iri c⟩ ]

/-- What `caxDwToComplement` emits from `c1 owl:disjointWith c2`: the
comprehension pair for each side, and the subclass edge that carries
the disjointness — `c1` is inside the complement of `c2`, and
symmetrically. -/
def complementWitnessTriples (c1 c2 : WfIri) : List Triple :=
  complementWitnessPair c2 ++ complementWitnessPair c1 ++
  [ ⟨Subject.iri c1, rdfsSubClassOf, (complementWitness c2).toTerm⟩,
    ⟨Subject.iri c2, rdfsSubClassOf, (complementWitness c1).toTerm⟩ ]

/-- What the max-qualified-cardinality contrapositive emits: the
comprehension pair for `c`, and the typing of `y` into it. -/
def complementTypeTriples (y : Subject) (c : WfIri) : List Triple :=
  complementWitnessPair c ++
  [ ⟨y, rdfType, (complementWitness c).toTerm⟩ ]

/-- The blank node denoting the `minCardinality 1` restriction on `p`. -/
def minCard1Witness (p : WfIri) : Subject :=
  Subject.bnode ("__rl_minc1__" ++ p.val)

/-- What `minCard1Comprehension` emits for `p`.

The cardinality is written TWICE, as `"1"^^xsd:nonNegativeInteger` and
as `"1"^^xsd:int`. §5.14's comprehension condition quantifies over the
VALUE `n`, not over a lexical form, and both literals denote the value
1 (RDF 1.1 Semantics §7, with `xsd:int ⊂ xsd:integer ⊂ xsd:decimal`);
the OWL 2 RDF mapping writes the first spelling and the OWL 1 mapping
the WebOnt conclusion documents use writes the second. Emitting one
spelling only would make the row's conclusion depend on which mapping
generated the document it is compared against, which is a property of
the comparison and not of the semantics. -/
def minCard1WitnessTriples (p : WfIri) : List Triple :=
  [ ⟨minCard1Witness p, rdfType, Term.iri owlRestriction⟩,
    ⟨minCard1Witness p, owlOnProperty, Term.iri p⟩,
    ⟨minCard1Witness p, owlMinCardinality, Term.literal litNni1⟩,
    ⟨minCard1Witness p, owlMinCardinality, Term.literal litInt1⟩ ]

/-- The IRIs occurring in `g` in a subject or object position — the
"named individuals" the `prpRfl` row quantifies over. Blank nodes are
excluded: under the OWL 2 RL reading a blank node is an existential,
not a name, and the F* `prp_rfl_individuals` makes the same exclusion.
The exclusion only makes the row FIRE LESS, so it costs nothing in
soundness. -/
def iriIndividuals (g : Graph) : List WfIri :=
  g.flatMap (fun t =>
    (match t.s with | .iri i => [i] | _ => []) ++
    (match t.o with | .iri i => [i] | _ => []))

/-! ## The derivation relation

`Derives g t` — "graph `g` OWL 2 RL/RDF-derives triple `t`". Base case
is LIST membership (`t ∈ g`), which is exact; the engine's coarser
`Triple.eqb` never enters a specification relation. -/

inductive Derives (g : Graph) : Triple → Prop where
  /-- Every asserted triple is derivable. -/
  | base {t : Triple} (h : t ∈ g) : Derives g t

  -- ===================================================================
  -- Table 4, family 1: the semantics of equality
  -- ===================================================================

  /-- **eq-ref** (subject conclusion) — `T(?s,?p,?o) |
  T(?s, owl:sameAs, ?s)`. -/
  | eqRefS {s : Subject} {p : WfIri} {o : Term}
      (h : Derives g ⟨s, p, o⟩) :
      Derives g ⟨s, owlSameAs, s.toTerm⟩
  /-- **eq-ref** (predicate conclusion) — `T(?p, owl:sameAs, ?p)`. The
  predicate slot of this tree's `Triple` is an IRI, which is the
  table's "delta GP" resolved structurally. -/
  | eqRefP {s : Subject} {p : WfIri} {o : Term}
      (h : Derives g ⟨s, p, o⟩) :
      Derives g ⟨Subject.iri p, owlSameAs, Term.iri p⟩
  /-- **eq-ref** (object conclusion) — `T(?o, owl:sameAs, ?o)`, for an
  object that can occupy a subject position. -/
  | eqRefO {s : Subject} {p : WfIri} {os : Subject}
      (h : Derives g ⟨s, p, os.toTerm⟩) :
      Derives g ⟨os, owlSameAs, os.toTerm⟩
  /-- **eq-sym** — `T(?x, owl:sameAs, ?y) | T(?y, owl:sameAs, ?x)`. -/
  | eqSym {x ys : Subject}
      (h : Derives g ⟨x, owlSameAs, ys.toTerm⟩) :
      Derives g ⟨ys, owlSameAs, x.toTerm⟩
  /-- **eq-trans** — `T(?x, owl:sameAs, ?y) T(?y, owl:sameAs, ?z) |
  T(?x, owl:sameAs, ?z)`. -/
  | eqTrans {x ys : Subject} {z : Term}
      (h1 : Derives g ⟨x, owlSameAs, ys.toTerm⟩)
      (h2 : Derives g ⟨ys, owlSameAs, z⟩) :
      Derives g ⟨x, owlSameAs, z⟩
  /-- **eq-rep-s** — `T(?s, owl:sameAs, ?s') T(?s,?p,?o) |
  T(?s',?p,?o)`. -/
  | eqRepS {s s' : Subject} {p : WfIri} {o : Term}
      (heq : Derives g ⟨s, owlSameAs, s'.toTerm⟩)
      (hd : Derives g ⟨s, p, o⟩) :
      Derives g ⟨s', p, o⟩
  /-- **eq-rep-p** — `T(?p, owl:sameAs, ?p') T(?s,?p,?o) |
  T(?s,?p',?o)`. Both property names occupy predicate position, so both
  are IRIs. -/
  | eqRepP {p p' : WfIri} {s : Subject} {o : Term}
      (heq : Derives g ⟨Subject.iri p, owlSameAs, Term.iri p'⟩)
      (hd : Derives g ⟨s, p, o⟩) :
      Derives g ⟨s, p', o⟩
  /-- **eq-rep-o** — `T(?o, owl:sameAs, ?o') T(?s,?p,?o) |
  T(?s,?p,?o')`. -/
  | eqRepO {os s : Subject} {o' : Term} {p : WfIri}
      (heq : Derives g ⟨os, owlSameAs, o'⟩)
      (hd : Derives g ⟨s, p, os.toTerm⟩) :
      Derives g ⟨s, p, o'⟩

  -- ===================================================================
  -- Table 4, family 2: the semantics of axioms about properties
  -- ===================================================================

  /-- **prp-dom** — `T(?p, rdfs:domain, ?c) T(?x,?p,?y) |
  T(?x, rdf:type, ?c)`. Same content as RDF 1.1 Semantics §9.2's
  rdfs2; restated under this table's own row name so the OWL-RL ledger
  is complete in one place. -/
  | prpDom {p : WfIri} {c : Term} {x : Subject} {y : Term}
      (hdecl : Derives g ⟨Subject.iri p, rdfsDomain, c⟩)
      (hd : Derives g ⟨x, p, y⟩) :
      Derives g ⟨x, rdfType, c⟩
  /-- **prp-rng** — `T(?p, rdfs:range, ?c) T(?x,?p,?y) |
  T(?y, rdf:type, ?c)`. The conclusion types the premise's OBJECT. -/
  | prpRng {p : WfIri} {c : Term} {x ys : Subject}
      (hdecl : Derives g ⟨Subject.iri p, rdfsRange, c⟩)
      (hd : Derives g ⟨x, p, ys.toTerm⟩) :
      Derives g ⟨ys, rdfType, c⟩
  /-- **prp-fp** — `T(?p, rdf:type, owl:FunctionalProperty)
  T(?x,?p,?y1) T(?x,?p,?y2) | T(?y1, owl:sameAs, ?y2)`. -/
  | prpFp {p : WfIri} {x y1s : Subject} {y2 : Term}
      (hdecl : Derives g ⟨Subject.iri p, rdfType,
        Term.iri owlFunctionalProperty⟩)
      (h1 : Derives g ⟨x, p, y1s.toTerm⟩)
      (h2 : Derives g ⟨x, p, y2⟩) :
      Derives g ⟨y1s, owlSameAs, y2⟩
  /-- **prp-ifp** — `T(?p, rdf:type, owl:InverseFunctionalProperty)
  T(?x1,?p,?y) T(?x2,?p,?y) | T(?x1, owl:sameAs, ?x2)`. -/
  | prpIfp {p : WfIri} {x1 x2 : Subject} {y : Term}
      (hdecl : Derives g ⟨Subject.iri p, rdfType,
        Term.iri owlInverseFunctionalProperty⟩)
      (h1 : Derives g ⟨x1, p, y⟩)
      (h2 : Derives g ⟨x2, p, y⟩) :
      Derives g ⟨x1, owlSameAs, x2.toTerm⟩
  /-- **prp-symp** — `T(?p, rdf:type, owl:SymmetricProperty)
  T(?x,?p,?y) | T(?y,?p,?x)`. -/
  | prpSymp {p : WfIri} {x ys : Subject}
      (hdecl : Derives g ⟨Subject.iri p, rdfType,
        Term.iri owlSymmetricProperty⟩)
      (hd : Derives g ⟨x, p, ys.toTerm⟩) :
      Derives g ⟨ys, p, x.toTerm⟩
  /-- **prp-trp** — `T(?p, rdf:type, owl:TransitiveProperty)
  T(?x,?p,?y) T(?y,?p,?z) | T(?x,?p,?z)`. -/
  | prpTrp {p : WfIri} {x ys : Subject} {z : Term}
      (hdecl : Derives g ⟨Subject.iri p, rdfType,
        Term.iri owlTransitiveProperty⟩)
      (h1 : Derives g ⟨x, p, ys.toTerm⟩)
      (h2 : Derives g ⟨ys, p, z⟩) :
      Derives g ⟨x, p, z⟩
  /-- **prp-spo1** — `T(?p1, rdfs:subPropertyOf, ?p2) T(?x,?p1,?y) |
  T(?x,?p2,?y)`. -/
  | prpSpo1 {p1 p2 : WfIri} {x : Subject} {y : Term}
      (hdecl : Derives g ⟨Subject.iri p1, rdfsSubPropertyOf,
        Term.iri p2⟩)
      (hd : Derives g ⟨x, p1, y⟩) :
      Derives g ⟨x, p2, y⟩
  /-- **prp-spo2** — `T(?p, owl:propertyChainAxiom, ?x)
  LIST[?x, ?p1, ..., ?pn] T(?u1,?p1,?u2) ... T(?un,?pn,?un+1) |
  T(?u1, ?p, ?un+1)`. Every chain element occupies a predicate
  position, hence the `Term.iri` image of the list. -/
  | prpSpo2 {p : WfIri} {lst : Term} {preds : List WfIri}
      {x1 : Subject} {xn : Term} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hdecl : Derives g ⟨Subject.iri p, owlPropertyChainAxiom, lst⟩)
      (hlist : ListDenotes gc lst (preds.map Term.iri))
      (hne : preds ≠ [])
      (hchain : ChainHolds gc x1 preds xn) :
      Derives g ⟨x1, p, xn⟩
  /-- **prp-eqp1** — `T(?p1, owl:equivalentProperty, ?p2)
  T(?x,?p1,?y) | T(?x,?p2,?y)`. -/
  | prpEqp1 {p1 p2 : WfIri} {x : Subject} {y : Term}
      (hdecl : Derives g ⟨Subject.iri p1, owlEquivalentProperty,
        Term.iri p2⟩)
      (hd : Derives g ⟨x, p1, y⟩) :
      Derives g ⟨x, p2, y⟩
  /-- **prp-eqp2** — the converse direction of prp-eqp1. -/
  | prpEqp2 {p1 p2 : WfIri} {x : Subject} {y : Term}
      (hdecl : Derives g ⟨Subject.iri p1, owlEquivalentProperty,
        Term.iri p2⟩)
      (hd : Derives g ⟨x, p2, y⟩) :
      Derives g ⟨x, p1, y⟩
  /-- **prp-inv1** — `T(?p1, owl:inverseOf, ?p2) T(?x,?p1,?y) |
  T(?y,?p2,?x)`. -/
  | prpInv1 {p1 p2 : WfIri} {x ys : Subject}
      (hdecl : Derives g ⟨Subject.iri p1, owlInverseOf, Term.iri p2⟩)
      (hd : Derives g ⟨x, p1, ys.toTerm⟩) :
      Derives g ⟨ys, p2, x.toTerm⟩
  /-- **prp-inv2** — `T(?p1, owl:inverseOf, ?p2) T(?x,?p2,?y) |
  T(?y,?p1,?x)`. -/
  | prpInv2 {p1 p2 : WfIri} {x ys : Subject}
      (hdecl : Derives g ⟨Subject.iri p1, owlInverseOf, Term.iri p2⟩)
      (hd : Derives g ⟨x, p2, ys.toTerm⟩) :
      Derives g ⟨ys, p1, x.toTerm⟩
  /-- **prp-key** — `T(?c, owl:hasKey, ?u) LIST[?u, ?p1, ..., ?pn]
  T(?x, rdf:type, ?c) T(?x,?p1,?z1) ... T(?y, rdf:type, ?c)
  T(?y,?p1,?z1) ... | T(?x, owl:sameAs, ?y)`. -/
  | prpKey {c x ys : Subject} {lst : Term} {preds : List WfIri} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hdecl : Derives g ⟨c, owlHasKey, lst⟩)
      (hlist : ListDenotes gc lst (preds.map Term.iri))
      (hne : preds ≠ [])
      (hx : Derives g ⟨x, rdfType, c.toTerm⟩)
      (hy : Derives g ⟨ys, rdfType, c.toTerm⟩)
      (hshare : SharesKeyValues gc x ys preds) :
      Derives g ⟨x, owlSameAs, ys.toTerm⟩

  -- ===================================================================
  -- Table 5: the semantics of classes
  -- ===================================================================

  /-- **cls-thing** — a premise-free row: `T(owl:Thing, rdf:type,
  owl:Class)`. -/
  | clsThing : Derives g ⟨Subject.iri owlThing, rdfType,
      Term.iri owlClass⟩
  /-- **cls-nothing1** — `T(owl:Nothing, rdf:type, owl:Class)`. -/
  | clsNothing1 : Derives g ⟨Subject.iri owlNothing, rdfType,
      Term.iri owlClass⟩
  /-- **cls-int1** — `T(?c, owl:intersectionOf, ?x)
  LIST[?x, ?c1, ..., ?cn] T(?y, rdf:type, ?c1) ... |
  T(?y, rdf:type, ?c)`. -/
  | clsInt1 {c y : Subject} {lst : Term} {cs : List Term} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hdecl : Derives g ⟨c, owlIntersectionOf, lst⟩)
      (hlist : ListDenotes gc lst cs)
      (hne : cs ≠ [])
      (htypes : TypesAll gc y cs) :
      Derives g ⟨y, rdfType, c.toTerm⟩
  /-- **cls-int2** — `T(?c, owl:intersectionOf, ?x)
  LIST[?x, ?c1, ..., ?cn] T(?y, rdf:type, ?c) |
  T(?y, rdf:type, ?c1) ... T(?y, rdf:type, ?cn)`. `t` is any one of
  the n conclusions, so its class is SOME list member. -/
  | clsInt2 {c y : Subject} {lst ci : Term} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hdecl : Derives g ⟨c, owlIntersectionOf, lst⟩)
      (hmem : ListMember gc lst ci)
      (hy : Derives g ⟨y, rdfType, c.toTerm⟩) :
      Derives g ⟨y, rdfType, ci⟩
  /-- **cls-uni** — `T(?c, owl:unionOf, ?x) LIST[?x, ?c1, ..., ?cn]
  T(?y, rdf:type, ?ci) | T(?y, rdf:type, ?c)`. -/
  | clsUni {c y : Subject} {lst ci : Term} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hdecl : Derives g ⟨c, owlUnionOf, lst⟩)
      (hmem : ListMember gc lst ci)
      (hy : Derives g ⟨y, rdfType, ci⟩) :
      Derives g ⟨y, rdfType, c.toTerm⟩
  /-- **cls-svf1** — `T(?x, owl:someValuesFrom, ?y)
  T(?x, owl:onProperty, ?p) T(?u,?p,?v) T(?v, rdf:type, ?y) |
  T(?u, rdf:type, ?x)`. -/
  | clsSvf1 {x u vs : Subject} {yc : Term} {p : WfIri}
      (hsvf : Derives g ⟨x, owlSomeValuesFrom, yc⟩)
      (honp : Derives g ⟨x, owlOnProperty, Term.iri p⟩)
      (hd : Derives g ⟨u, p, vs.toTerm⟩)
      (hty : Derives g ⟨vs, rdfType, yc⟩) :
      Derives g ⟨u, rdfType, x.toTerm⟩
  /-- **cls-svf2** — `T(?x, owl:someValuesFrom, owl:Thing)
  T(?x, owl:onProperty, ?p) T(?u,?p,?v) | T(?u, rdf:type, ?x)`. -/
  | clsSvf2 {x u : Subject} {v : Term} {p : WfIri}
      (hsvf : Derives g ⟨x, owlSomeValuesFrom, Term.iri owlThing⟩)
      (honp : Derives g ⟨x, owlOnProperty, Term.iri p⟩)
      (hd : Derives g ⟨u, p, v⟩) :
      Derives g ⟨u, rdfType, x.toTerm⟩
  /-- **cls-avf** — `T(?x, owl:allValuesFrom, ?y)
  T(?x, owl:onProperty, ?p) T(?u, rdf:type, ?x) T(?u,?p,?v) |
  T(?v, rdf:type, ?y)`. -/
  | clsAvf {x u vs : Subject} {yc : Term} {p : WfIri}
      (havf : Derives g ⟨x, owlAllValuesFrom, yc⟩)
      (honp : Derives g ⟨x, owlOnProperty, Term.iri p⟩)
      (hty : Derives g ⟨u, rdfType, x.toTerm⟩)
      (hd : Derives g ⟨u, p, vs.toTerm⟩) :
      Derives g ⟨vs, rdfType, yc⟩
  /-- **cls-hv1** — `T(?x, owl:hasValue, ?y) T(?x, owl:onProperty, ?p)
  T(?u, rdf:type, ?x) | T(?u,?p,?y)`. -/
  | clsHv1 {x u : Subject} {yv : Term} {p : WfIri}
      (hhv : Derives g ⟨x, owlHasValue, yv⟩)
      (honp : Derives g ⟨x, owlOnProperty, Term.iri p⟩)
      (hty : Derives g ⟨u, rdfType, x.toTerm⟩) :
      Derives g ⟨u, p, yv⟩
  /-- **cls-hv2** — `T(?x, owl:hasValue, ?y) T(?x, owl:onProperty, ?p)
  T(?u,?p,?y) | T(?u, rdf:type, ?x)`. -/
  | clsHv2 {x u : Subject} {yv : Term} {p : WfIri}
      (hhv : Derives g ⟨x, owlHasValue, yv⟩)
      (honp : Derives g ⟨x, owlOnProperty, Term.iri p⟩)
      (hd : Derives g ⟨u, p, yv⟩) :
      Derives g ⟨u, rdfType, x.toTerm⟩
  /-- **cls-hs1** — `T(?c, owl:hasSelf, "true"^^xsd:boolean)
  T(?c, owl:onProperty, ?p) T(?u, rdf:type, ?c) | T(?u,?p,?u)`. The
  `owl:hasSelf` object is matched LEXICALLY — see
  `Vocabulary.litTrueBoolean`. -/
  | clsHs1 {c u : Subject} {p : WfIri}
      (hhs : Derives g ⟨c, owlHasSelf, Term.literal litTrueBoolean⟩)
      (honp : Derives g ⟨c, owlOnProperty, Term.iri p⟩)
      (hty : Derives g ⟨u, rdfType, c.toTerm⟩) :
      Derives g ⟨u, p, u.toTerm⟩
  /-- **cls-hs2** — `T(?c, owl:hasSelf, "true"^^xsd:boolean)
  T(?c, owl:onProperty, ?p) T(?u,?p,?u) | T(?u, rdf:type, ?c)`. -/
  | clsHs2 {c u : Subject} {p : WfIri}
      (hhs : Derives g ⟨c, owlHasSelf, Term.literal litTrueBoolean⟩)
      (honp : Derives g ⟨c, owlOnProperty, Term.iri p⟩)
      (hd : Derives g ⟨u, p, u.toTerm⟩) :
      Derives g ⟨u, rdfType, c.toTerm⟩
  /-- **cls-maxc2** — `T(?x, owl:maxCardinality, "1"^^xsd:nnI)
  T(?x, owl:onProperty, ?p) T(?u, rdf:type, ?x) T(?u,?p,?y1)
  T(?u,?p,?y2) | T(?y1, owl:sameAs, ?y2)`. The cardinality literal is
  matched LEXICALLY — see `Vocabulary.litNni1`. -/
  | clsMaxc2 {x u y1s : Subject} {y2 : Term} {p : WfIri}
      (hmc : Derives g ⟨x, owlMaxCardinality, Term.literal litNni1⟩)
      (honp : Derives g ⟨x, owlOnProperty, Term.iri p⟩)
      (hty : Derives g ⟨u, rdfType, x.toTerm⟩)
      (h1 : Derives g ⟨u, p, y1s.toTerm⟩)
      (h2 : Derives g ⟨u, p, y2⟩) :
      Derives g ⟨y1s, owlSameAs, y2⟩
  /-- **cls-oo** — `T(?c, owl:oneOf, ?x) LIST[?x, ?y1, ..., ?yn] |
  T(?y1, rdf:type, ?c) ... T(?yn, rdf:type, ?c)`. -/
  | clsOo {c yis : Subject} {lst : Term} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hdecl : Derives g ⟨c, owlOneOf, lst⟩)
      (hmem : ListMember gc lst yis.toTerm) :
      Derives g ⟨yis, rdfType, c.toTerm⟩

  -- ===================================================================
  -- Table 6: the semantics of class axioms
  -- ===================================================================

  /-- **cax-sco** — `T(?c1, rdfs:subClassOf, ?c2) T(?x, rdf:type, ?c1) |
  T(?x, rdf:type, ?c2)`. -/
  | caxSco {c1 x : Subject} {c2 : Term}
      (hdecl : Derives g ⟨c1, rdfsSubClassOf, c2⟩)
      (hty : Derives g ⟨x, rdfType, c1.toTerm⟩) :
      Derives g ⟨x, rdfType, c2⟩
  /-- **cax-eqc1** — `T(?c1, owl:equivalentClass, ?c2)
  T(?x, rdf:type, ?c1) | T(?x, rdf:type, ?c2)`. -/
  | caxEqc1 {c1 x : Subject} {c2 : Term}
      (hdecl : Derives g ⟨c1, owlEquivalentClass, c2⟩)
      (hty : Derives g ⟨x, rdfType, c1.toTerm⟩) :
      Derives g ⟨x, rdfType, c2⟩
  /-- **cax-eqc2** — the converse direction of cax-eqc1. -/
  | caxEqc2 {c1 x : Subject} {c2 : Term}
      (hdecl : Derives g ⟨c1, owlEquivalentClass, c2⟩)
      (hty : Derives g ⟨x, rdfType, c2⟩) :
      Derives g ⟨x, rdfType, c1.toTerm⟩

  -- ===================================================================
  -- Table 8: the semantics of schema vocabulary
  -- ===================================================================

  /-- **scm-cls** (conclusion 1 of 4) — `T(?c, rdf:type, owl:Class) |
  T(?c, rdfs:subClassOf, ?c)`. -/
  | scmClsSelf {c : Subject}
      (h : Derives g ⟨c, rdfType, Term.iri owlClass⟩) :
      Derives g ⟨c, rdfsSubClassOf, c.toTerm⟩
  /-- **scm-cls** (conclusion 2 of 4) — `T(?c, owl:equivalentClass,
  ?c)`. -/
  | scmClsEqc {c : Subject}
      (h : Derives g ⟨c, rdfType, Term.iri owlClass⟩) :
      Derives g ⟨c, owlEquivalentClass, c.toTerm⟩
  /-- **scm-cls** (conclusion 3 of 4) — `T(?c, rdfs:subClassOf,
  owl:Thing)`. -/
  | scmClsThing {c : Subject}
      (h : Derives g ⟨c, rdfType, Term.iri owlClass⟩) :
      Derives g ⟨c, rdfsSubClassOf, Term.iri owlThing⟩
  /-- **scm-cls** (conclusion 4 of 4) — `T(owl:Nothing,
  rdfs:subClassOf, ?c)`. -/
  | scmClsNothing {c : Subject}
      (h : Derives g ⟨c, rdfType, Term.iri owlClass⟩) :
      Derives g ⟨Subject.iri owlNothing, rdfsSubClassOf, c.toTerm⟩
  /-- **scm-sco** — `T(?c1, rdfs:subClassOf, ?c2)
  T(?c2, rdfs:subClassOf, ?c3) | T(?c1, rdfs:subClassOf, ?c3)`
  (transitivity of the class hierarchy). -/
  | scmSco {c1 c2s : Subject} {c3 : Term}
      (h1 : Derives g ⟨c1, rdfsSubClassOf, c2s.toTerm⟩)
      (h2 : Derives g ⟨c2s, rdfsSubClassOf, c3⟩) :
      Derives g ⟨c1, rdfsSubClassOf, c3⟩
  /-- **scm-eqc1** (conclusion 1 of 2) — `T(?c1, owl:equivalentClass,
  ?c2) | T(?c1, rdfs:subClassOf, ?c2)`. -/
  | scmEqc1a {c1 : Subject} {c2 : Term}
      (h : Derives g ⟨c1, owlEquivalentClass, c2⟩) :
      Derives g ⟨c1, rdfsSubClassOf, c2⟩
  /-- **scm-eqc1** (conclusion 2 of 2) — `T(?c2, rdfs:subClassOf,
  ?c1)`. -/
  | scmEqc1b {c1 c2s : Subject}
      (h : Derives g ⟨c1, owlEquivalentClass, c2s.toTerm⟩) :
      Derives g ⟨c2s, rdfsSubClassOf, c1.toTerm⟩
  /-- **scm-eqc2** — `T(?c1, rdfs:subClassOf, ?c2)
  T(?c2, rdfs:subClassOf, ?c1) | T(?c1, owl:equivalentClass, ?c2)`. -/
  | scmEqc2 {c1 c2s : Subject}
      (h1 : Derives g ⟨c1, rdfsSubClassOf, c2s.toTerm⟩)
      (h2 : Derives g ⟨c2s, rdfsSubClassOf, c1.toTerm⟩) :
      Derives g ⟨c1, owlEquivalentClass, c2s.toTerm⟩
  /-- **scm-spo** — `T(?p1, rdfs:subPropertyOf, ?p2)
  T(?p2, rdfs:subPropertyOf, ?p3) | T(?p1, rdfs:subPropertyOf, ?p3)`
  (transitivity of the property hierarchy). -/
  | scmSpo {p1 p2s : Subject} {p3 : Term}
      (h1 : Derives g ⟨p1, rdfsSubPropertyOf, p2s.toTerm⟩)
      (h2 : Derives g ⟨p2s, rdfsSubPropertyOf, p3⟩) :
      Derives g ⟨p1, rdfsSubPropertyOf, p3⟩
  /-- **scm-eqp1** (conclusion 1 of 2) — the property mirror of
  scm-eqc1. -/
  | scmEqp1a {p1 : Subject} {p2 : Term}
      (h : Derives g ⟨p1, owlEquivalentProperty, p2⟩) :
      Derives g ⟨p1, rdfsSubPropertyOf, p2⟩
  /-- **scm-eqp1** (conclusion 2 of 2). -/
  | scmEqp1b {p1 p2s : Subject}
      (h : Derives g ⟨p1, owlEquivalentProperty, p2s.toTerm⟩) :
      Derives g ⟨p2s, rdfsSubPropertyOf, p1.toTerm⟩
  /-- **scm-eqp2** — the property mirror of scm-eqc2. -/
  | scmEqp2 {p1 p2s : Subject}
      (h1 : Derives g ⟨p1, rdfsSubPropertyOf, p2s.toTerm⟩)
      (h2 : Derives g ⟨p2s, rdfsSubPropertyOf, p1.toTerm⟩) :
      Derives g ⟨p1, owlEquivalentProperty, p2s.toTerm⟩
  /-- **scm-dom1** — `T(?p, rdfs:domain, ?c1)
  T(?c1, rdfs:subClassOf, ?c2) | T(?p, rdfs:domain, ?c2)`. -/
  | scmDom1 {p c1s : Subject} {c2 : Term}
      (hdom : Derives g ⟨p, rdfsDomain, c1s.toTerm⟩)
      (hsub : Derives g ⟨c1s, rdfsSubClassOf, c2⟩) :
      Derives g ⟨p, rdfsDomain, c2⟩
  /-- **scm-dom2** — `T(?p2, rdfs:domain, ?c)
  T(?p1, rdfs:subPropertyOf, ?p2) | T(?p1, rdfs:domain, ?c)`. -/
  | scmDom2 {p2 p1 : Subject} {c : Term}
      (hdom : Derives g ⟨p2, rdfsDomain, c⟩)
      (hsub : Derives g ⟨p1, rdfsSubPropertyOf, p2.toTerm⟩) :
      Derives g ⟨p1, rdfsDomain, c⟩
  /-- **scm-rng1** — the range mirror of scm-dom1. -/
  | scmRng1 {p c1s : Subject} {c2 : Term}
      (hrng : Derives g ⟨p, rdfsRange, c1s.toTerm⟩)
      (hsub : Derives g ⟨c1s, rdfsSubClassOf, c2⟩) :
      Derives g ⟨p, rdfsRange, c2⟩
  /-- **scm-rng2** — the range mirror of scm-dom2. -/
  | scmRng2 {p2 p1 : Subject} {c : Term}
      (hrng : Derives g ⟨p2, rdfsRange, c⟩)
      (hsub : Derives g ⟨p1, rdfsSubPropertyOf, p2.toTerm⟩) :
      Derives g ⟨p1, rdfsRange, c⟩
  /-- **scm-int** — `T(?c, owl:intersectionOf, ?x)
  LIST[?x, ?c1, ..., ?cn] | T(?c, rdfs:subClassOf, ?c1) ...`. -/
  | scmInt {c : Subject} {lst ci : Term} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hdecl : Derives g ⟨c, owlIntersectionOf, lst⟩)
      (hmem : ListMember gc lst ci) :
      Derives g ⟨c, rdfsSubClassOf, ci⟩
  /-- **scm-uni** — `T(?c, owl:unionOf, ?x) LIST[?x, ?c1, ..., ?cn] |
  T(?c1, rdfs:subClassOf, ?c) ...`. -/
  | scmUni {c cis : Subject} {lst : Term} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hdecl : Derives g ⟨c, owlUnionOf, lst⟩)
      (hmem : ListMember gc lst cis.toTerm) :
      Derives g ⟨cis, rdfsSubClassOf, c.toTerm⟩

  -- ===================================================================
  -- `[ext]` — sound extensions with no W3C table row
  --
  -- Each constructor below cites the OWL 2 RDF-Based Semantics
  -- condition that makes it truth-preserving, in place of a table id.
  -- The F* engine carries the same nine rules; the F* rule name is
  -- given so the two ledgers line up.
  -- ===================================================================

  /-- **eq-diff-sym** `[ext]` (F* `owl_rule_differentFrom_symmetry`) —
  `T(?x, owl:differentFrom, ?y) | T(?y, owl:differentFrom, ?x)`.

  RDF-Based Semantics §5.8: `IEXT(I(owl:differentFrom)) = { <x,y> ∈
  IR × IR : x ≠ y }`. Inequality is symmetric, so the conclusion holds
  in every interpretation the premise holds in. -/
  | eqDiffSym {x ys : Subject}
      (h : Derives g ⟨x, owlDifferentFrom, ys.toTerm⟩) :
      Derives g ⟨ys, owlDifferentFrom, x.toTerm⟩

  /-- **prp-pdw-diff** `[ext]` (F* `owl_rule_pdw_to_differentFrom`) —
  the Horn contrapositive of the prp-pdw clash row:
  `T(?p1, owl:propertyDisjointWith, ?p2) T(?x,?p1,?o1) T(?x,?p2,?o2)
  o1 ≠ o2 | T(?o1, owl:differentFrom, ?o2)`.

  RDF-Based Semantics §5.9: `<p1,p2> ∈ IEXT(I(owl:propertyDisjointWith))`
  iff `IEXT(p1) ∩ IEXT(p2) = ∅`. If `I(o1) = I(o2)` then the pair
  `<I(x), I(o1)>` sits in both extensions, which the condition forbids;
  hence `I(o1) ≠ I(o2)`, which is `owl:differentFrom`. The `o1 ≠ o2`
  side condition is SYNTACTIC and only stops the row emitting a
  self-inequality on an already-inconsistent graph — it makes the row
  fire less, never more. -/
  | pdwToDiff {p1 p2 : WfIri} {x o1s : Subject} {o2 : Term}
      (hdecl : Derives g ⟨Subject.iri p1, owlPropertyDisjointWith,
        Term.iri p2⟩)
      (h1 : Derives g ⟨x, p1, o1s.toTerm⟩)
      (h2 : Derives g ⟨x, p2, o2⟩)
      (hne : o1s.toTerm ≠ o2) :
      Derives g ⟨o1s, owlDifferentFrom, o2⟩

  /-- **cax-dw-diff** `[ext]` (F* `owl_rule_cax_dw_to_differentFrom`) —
  the class-side mirror of prp-pdw-diff:
  `T(?c1, owl:disjointWith, ?c2) T(?x, rdf:type, ?c1)
  T(?y, rdf:type, ?c2) x ≠ y | T(?x, owl:differentFrom, ?y)`.

  RDF-Based Semantics §5.7: `<c1,c2> ∈ IEXT(I(owl:disjointWith))` iff
  `ICEXT(c1) ∩ ICEXT(c2) = ∅`. If `I(x) = I(y)` that individual is in
  both class extensions, which the condition forbids. -/
  | caxDwToDiff {c1 c2 : WfIri} {x ys : Subject}
      (hdecl : Derives g ⟨Subject.iri c1, owlDisjointWith, Term.iri c2⟩)
      (h1 : Derives g ⟨x, rdfType, Term.iri c1⟩)
      (h2 : Derives g ⟨ys, rdfType, Term.iri c2⟩)
      (hne : x ≠ ys) :
      Derives g ⟨x, owlDifferentFrom, ys.toTerm⟩

  /-- **prp-fp-diff** `[ext]` (F* `owl_rule_fp_diff_to_diff`) — the
  Horn contrapositive of prp-fp:
  `T(?p, rdf:type, owl:FunctionalProperty) T(?y1,?p,?x1)
  T(?y2,?p,?x2) T(?x1, owl:differentFrom, ?x2) y1 ≠ y2 |
  T(?y1, owl:differentFrom, ?y2)`.

  RDF-Based Semantics §5.9: a functional property has at most one value
  per subject. If `I(y1) = I(y2)` then `I(x1) = I(x2)`, contradicting
  the `owl:differentFrom` premise. -/
  | fpDiffToDiff {p : WfIri} {y1 y2 x1s : Subject} {x2 : Term}
      (hdecl : Derives g ⟨Subject.iri p, rdfType,
        Term.iri owlFunctionalProperty⟩)
      (h1 : Derives g ⟨y1, p, x1s.toTerm⟩)
      (h2 : Derives g ⟨y2, p, x2⟩)
      (hdiff : Derives g ⟨x1s, owlDifferentFrom, x2⟩)
      (hne : y1 ≠ y2) :
      Derives g ⟨y1, owlDifferentFrom, y2.toTerm⟩

  /-- **prp-ifp-diff** `[ext]` (F* `owl_rule_ifp_diff_to_diff`) — the
  Horn contrapositive of prp-ifp:
  `T(?p, rdf:type, owl:InverseFunctionalProperty) T(?x1,?p,?y1)
  T(?x2,?p,?y2) T(?x1, owl:differentFrom, ?x2) y1 ≠ y2 |
  T(?y1, owl:differentFrom, ?y2)`.

  RDF-Based Semantics §5.9: an inverse-functional property has at most
  one subject per value. If `I(y1) = I(y2)` then `I(x1) = I(x2)`,
  contradicting the `owl:differentFrom` premise. -/
  | ifpDiffToDiff {p : WfIri} {x1 x2s y1s : Subject} {y2 : Term}
      (hdecl : Derives g ⟨Subject.iri p, rdfType,
        Term.iri owlInverseFunctionalProperty⟩)
      (h1 : Derives g ⟨x1, p, y1s.toTerm⟩)
      (h2 : Derives g ⟨x2s, p, y2⟩)
      (hdiff : Derives g ⟨x1, owlDifferentFrom, x2s.toTerm⟩)
      (hne : y1s.toTerm ≠ y2) :
      Derives g ⟨y1s, owlDifferentFrom, y2⟩

  /-- **scm-trans-from-chain** `[ext]` (F*
  `owl_rule_chain_to_transitive`) —
  `T(?p, owl:propertyChainAxiom, ?l) LIST[?l, ?p, ?p] |
  T(?p, rdf:type, owl:TransitiveProperty)`.

  RDF-Based Semantics §5.11 reads `<p, l> ∈
  IEXT(I(owl:propertyChainAxiom))` with `l` the sequence `<q1,…,qn>` as
  `IEXT(q1) ∘ … ∘ IEXT(qn) ⊆ IEXT(p)`. At `l = <p, p>` that is
  `IEXT(p) ∘ IEXT(p) ⊆ IEXT(p)`, which is §5.9's condition for
  `p ∈ ICEXT(I(owl:TransitiveProperty))` — the same statement, so the
  row is an equivalence read in one direction. -/
  | chainToTrans {p : WfIri} {lst : Term} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hdecl : Derives g ⟨Subject.iri p, owlPropertyChainAxiom, lst⟩)
      (hlist : ListDenotes gc lst [Term.iri p, Term.iri p]) :
      Derives g ⟨Subject.iri p, rdfType, Term.iri owlTransitiveProperty⟩

  /-- **prp-rfl** `[ext]` (F* `owl_rule_reflexive_property`) —
  `T(?p, rdf:type, owl:ReflexiveProperty) ?x an IRI of the graph |
  T(?x, ?p, ?x)`.

  RDF-Based Semantics §5.9: `ICEXT(I(owl:ReflexiveProperty)) = { p ∈ IP :
  IEXT(p) ⊇ { <y,y> : y ∈ IR } }`. Every IRI has a denotation in `IR`,
  so `<I(x), I(x)> ∈ IEXT(I(p))` for any IRI `x` whatever — the row
  restricts to IRIs OCCURRING in `g` only because a rule engine has to
  enumerate something finite, and restricting the quantifier makes the
  row fire less. Blank nodes are left out for the reason the F* banner
  gives: a blank node is an existential, and `_:b p _:b` would commit
  to identifying the witness of the subject slot with the witness of
  the object slot. -/
  | prpRfl {p i : WfIri} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hdecl : Derives g ⟨Subject.iri p, rdfType,
        Term.iri owlReflexiveProperty⟩)
      (hind : i ∈ iriIndividuals gc) :
      Derives g ⟨Subject.iri i, p, Term.iri i⟩

  /-- **xsd-axioms** `[ext]` (F* `owl_rule_xsd_datatype_axioms`) — a
  graph that names an XSD IRI gets the XSD numeric subtype tower and an
  `rdf:type rdfs:Datatype` for every datatype in it.

  ASSUMPTION CARRIED: the interpretation's datatype map recognises the
  XSD datatypes, with the XSD 1.1 §3.4 value spaces. `xsdHierarchyEdges`
  and `xsdAllDatatypes` state exactly which facts are assumed;
  `XsdValueSpaceSubset` below names the shape of the assumption and
  `xsdIntegerDecimal_subset` discharges the one edge the Lean datatype
  map models. The driving premise is any triple mentioning an XSD IRI,
  which is the F* `graph_mentions_xsd_iri` guard read per triple. -/
  | xsdAxioms {d t : Triple}
      (hd : Derives g d)
      (hx : drivesXsdAxioms d = true)
      (hax : t ∈ xsdAxiomTriples) :
      Derives g t

  /-- **dt-rng-intersect** `[ext]` (F* `owl_rule_dt_range_intersect`) —
  `T(?p, rdfs:range, ?d1) T(?p, rdfs:range, ?d2) | T(?p, rdfs:range, ?d3)`
  for every `d3` the `xsdRangeIntersections` table licenses from
  `(d1, d2)`.

  ASSUMPTION CARRIED: the XSD value-space containments the table's doc
  comment lists. Given them, every value of `?p` is in
  `valueSpace(d1) ∩ valueSpace(d2) ⊆ valueSpace(d3)`, so the new range
  axiom is true wherever the two premises are. -/
  | dtRangeIntersect {pd : Subject} {d1 d2 d3 : WfIri}
      (h1 : Derives g ⟨pd, rdfsRange, Term.iri d1⟩)
      (h2 : Derives g ⟨pd, rdfsRange, Term.iri d2⟩)
      (hlic : rangeIntersectLicenses d1 d2 d3 = true) :
      Derives g ⟨pd, rdfsRange, Term.iri d3⟩

  /-- **The premise-free axiom triples** `[ext]` (F*
  `builtin_vocabulary_axioms`) — every triple of `premiseFreeAxioms`,
  with no premise at all. Two groups.

  Group 1, **dt-type1**, unconditional half: `T(xsd:integer, rdf:type,
  rdfs:Datatype)` and `T(xsd:string, rdf:type, rdfs:Datatype)`.

  RDF 1.1 Semantics §7: EVERY D-interpretation recognises `xsd:string`,
  and Table 7's dt-type1 asserts `rdf:type rdfs:Datatype` for each
  recognised datatype. `xsd:integer` is added on the same ground —
  it is in the RDF-compatible XSD types of RDF 1.1 Concepts §5.1 that
  every OWL 2 datatype map must recognise (OWL 2 Syntax §4.1). The
  empty graph therefore entails both, which is what WebOnt-I5.8-011
  asks.

  Group 2, the nine `owl:AnnotationProperty` typings of OWL 2 RDF-Based
  Semantics Section 6, Tables 6.2 and 6.5 — see
  `vocabAnnotationPropertyAxioms` for the transcription and the
  model-theoretic ground. -/
  | premiseFreeAxiom {t : Triple} (h : t ∈ premiseFreeAxioms) :
      Derives g t

  /-- **cax-dw-comp** `[ext]`, a COMPREHENSION row —
  `T(?c1, owl:disjointWith, ?c2) |
  T(_:comp(c2), rdf:type, owl:Class)
  T(_:comp(c2), owl:complementOf, ?c2)
  T(?c1, rdfs:subClassOf, _:comp(c2))`, and symmetrically.

  Two separate claims, each with its own semantic condition.

  1. The blank node EXISTS: RDF-Based Semantics §5.14's comprehension
     condition for `owl:complementOf` says that for every `c ∈ ICEXT(
     I(owl:Class))` there is a `z ∈ IR` with `<z, c> ∈
     IEXT(I(owl:complementOf))`. Asserting that with a blank node is
     asserting exactly the existential the condition supplies.
  2. The subclass edge: §5.7 gives `<c1,c2> ∈ IEXT(I(owl:disjointWith))`
     iff `ICEXT(c1) ∩ ICEXT(c2) = ∅`, and §5.5 gives `ICEXT(z) = IR \
     ICEXT(c2)`. Disjointness therefore puts `ICEXT(c1)` inside
     `ICEXT(z)`, which is `rdfs:subClassOf`. -/
  | caxDwToComplement {c1 c2 : WfIri} {t : Triple}
      (hdecl : Derives g ⟨Subject.iri c1, owlDisjointWith, Term.iri c2⟩)
      (hax : t ∈ complementWitnessTriples c1 c2) :
      Derives g t

  /-- **cls-maxqc1-comp** `[ext]`, the Horn contrapositive of
  cls-maxqc1 at cardinality 1, landing in a comprehension witness —
  `T(?x, owl:maxQualifiedCardinality, "1"^^xsd:nnI)
  T(?x, owl:onProperty, ?p) T(?x, owl:onClass, ?c)
  T(?u, rdf:type, ?x) T(?u,?p,?y1) T(?u,?p,?y2)
  T(?y1, rdf:type, ?c) T(?y1, owl:differentFrom, ?y2) |
  T(?y2, rdf:type, _:comp(c))` plus the comprehension pair for `c`.

  RDF-Based Semantics §5.10: `u ∈ ICEXT(x)` for a
  `maxQualifiedCardinality 1` restriction on `p` with `onClass c` means
  `u` has AT MOST ONE `p`-value in `ICEXT(c)`. Suppose `I(y2) ∈
  ICEXT(c)`. Then `y1` and `y2` are two `p`-values of `u` in `ICEXT(c)`,
  and the `owl:differentFrom` premise makes them distinct — two values
  where at most one is allowed. So `I(y2) ∉ ICEXT(c)`, which is
  membership of the complement class §5.14 supplies. -/
  | clsMaxqc1ToComplement {x u y1s y2s : Subject} {p c : WfIri} {t : Triple}
      (hmqc : Derives g ⟨x, owlMaxQualifiedCardinality,
        Term.literal litNni1⟩)
      (honp : Derives g ⟨x, owlOnProperty, Term.iri p⟩)
      (honc : Derives g ⟨x, owlOnClass, Term.iri c⟩)
      (hty : Derives g ⟨u, rdfType, x.toTerm⟩)
      (h1 : Derives g ⟨u, p, y1s.toTerm⟩)
      (h2 : Derives g ⟨u, p, y2s.toTerm⟩)
      (hy1c : Derives g ⟨y1s, rdfType, Term.iri c⟩)
      (hdiff : Derives g ⟨y1s, owlDifferentFrom, y2s.toTerm⟩)
      (hax : t ∈ complementTypeTriples y2s c) :
      Derives g t

  /-- **minc1-comp** `[ext]`, a COMPREHENSION row —
  `T(?p, rdf:type, owl:ObjectProperty) |
  T(_:minc1(p), rdf:type, owl:Restriction)
  T(_:minc1(p), owl:onProperty, ?p)
  T(_:minc1(p), owl:minCardinality, "1")`.

  RDF-Based Semantics §5.14's comprehension condition for
  `owl:minCardinality`: for every `p ∈ IP` and every non-negative
  integer `n` there is a `z ∈ ICEXT(I(owl:Restriction))` with
  `<z,p> ∈ IEXT(I(owl:onProperty))` and `<z,n> ∈
  IEXT(I(owl:minCardinality))`. The row instantiates it at `n = 1`.
  The driving premise is the property declaration only because a rule
  engine has to enumerate something; the condition itself needs no
  premise at all. -/
  | minCard1Comprehension {p : WfIri} {t : Triple}
      (hdecl : Derives g ⟨Subject.iri p, rdfType,
        Term.iri owlObjectProperty⟩)
      (hax : t ∈ minCard1WitnessTriples p) :
      Derives g t

  /-- **cax-adc-dw** `[ext]` — an `owl:AllDisjointClasses` axiom is
  pairwise `owl:disjointWith`:
  `T(?y, rdf:type, owl:AllDisjointClasses) T(?y, owl:members, ?l)
  LIST[?l, …, ?ci, …, ?cj, …] ci ≠ cj |
  T(?ci, owl:disjointWith, ?cj)`.

  RDF-Based Semantics §5.7 reads `y ∈
  ICEXT(I(owl:AllDisjointClasses))` with members `<c1,…,cn>` as
  `ICEXT(ci) ∩ ICEXT(cj) = ∅` for every `i ≠ j` — which is §5.7's
  condition on `owl:disjointWith` for that pair. The row states the
  pairwise form so that cax-dw, cax-dw-diff and cax-dw-comp all reach
  an `owl:AllDisjointClasses` axiom without each of them growing a
  second list-walking body.

  Carries the SAME deviation `caxAdc` carries and for the same reason:
  the members are required to be distinct TERMS, not to sit at
  distinct POSITIONS, so a class listed twice does not make itself
  disjoint from itself. That is strictly weaker than the F* reading. -/
  | caxAdcToDw {y : Subject} {lst : Term} {ci cj : WfIri} {gc : Graph}
      (hgc : ∀ u, u ∈ gc → Derives g u)
      (hty : Derives g ⟨y, rdfType, Term.iri owlAllDisjointClasses⟩)
      (hmembers : Derives g ⟨y, owlMembers, lst⟩)
      (h1 : ListMember gc lst (Term.iri ci))
      (h2 : ListMember gc lst (Term.iri cj))
      (hne : ci ≠ cj) :
      Derives g ⟨Subject.iri ci, owlDisjointWith, Term.iri cj⟩

  /-- **inv-flip** `[ext]` — schema-level inverseOf domain/range
  exchange, NOT in OWL 2 RL/RDF Table 9. `p owl:inverseOf q` makes the
  extension of `q` the transposition of `p`'s, so a domain class of `p`
  is a range class of `q`, and conversely — in both reading directions
  of the `owl:inverseOf` triple. Sound under OWL 2 Direct and RDF-Based
  Semantics. Four rows, one per emitted shape of
  `RLClosure.inverseOfDomRngFlipFor`; W3C SPARQL entailment
  `sparqldl-11` is the test that needs the schema triple itself. -/
  | invFlipDomRng {p q c : WfIri}
      (hinv : Derives g ⟨Subject.iri p, owlInverseOf, Term.iri q⟩)
      (hdom : Derives g ⟨Subject.iri p, rdfsDomain, Term.iri c⟩) :
      Derives g ⟨Subject.iri q, rdfsRange, Term.iri c⟩
  | invFlipRngDom {p q c : WfIri}
      (hinv : Derives g ⟨Subject.iri p, owlInverseOf, Term.iri q⟩)
      (hrng : Derives g ⟨Subject.iri p, rdfsRange, Term.iri c⟩) :
      Derives g ⟨Subject.iri q, rdfsDomain, Term.iri c⟩
  | invFlipDomRngRev {p q c : WfIri}
      (hinv : Derives g ⟨Subject.iri p, owlInverseOf, Term.iri q⟩)
      (hdom : Derives g ⟨Subject.iri q, rdfsDomain, Term.iri c⟩) :
      Derives g ⟨Subject.iri p, rdfsRange, Term.iri c⟩
  | invFlipRngDomRev {p q c : WfIri}
      (hinv : Derives g ⟨Subject.iri p, owlInverseOf, Term.iri q⟩)
      (hrng : Derives g ⟨Subject.iri q, rdfsRange, Term.iri c⟩) :
      Derives g ⟨Subject.iri p, rdfsDomain, Term.iri c⟩

/-! ## The no-consequent (clash) rows

Rows whose conclusion is `false`: their premises being satisfiable in
the graph is an inconsistency, not a derivation. `RLClosure.detectClash`
is the decision procedure, and `RLTheorems.detectClash_sound` proves
every `true` verdict is one of these. -/

inductive Clash (g : Graph) : Prop where
  /-- **eq-diff1** — `T(?x, owl:sameAs, ?y)
  T(?x, owl:differentFrom, ?y) | false`. -/
  | eqDiff1 {x : Subject} {y : Term}
      (h1 : (⟨x, owlSameAs, y⟩ : Triple) ∈ g)
      (h2 : (⟨x, owlDifferentFrom, y⟩ : Triple) ∈ g) : Clash g
  /-- **prp-irp** — `T(?p, rdf:type, owl:IrreflexiveProperty)
  T(?x,?p,?x) | false`. -/
  | prpIrp {p : WfIri} {x : Subject}
      (hdecl : (⟨Subject.iri p, rdfType,
        Term.iri owlIrreflexiveProperty⟩ : Triple) ∈ g)
      (hd : (⟨x, p, x.toTerm⟩ : Triple) ∈ g) : Clash g
  /-- **prp-asyp** — `T(?p, rdf:type, owl:AsymmetricProperty)
  T(?x,?p,?y) T(?y,?p,?x) | false`. -/
  | prpAsyp {p : WfIri} {x y : Subject}
      (hdecl : (⟨Subject.iri p, rdfType,
        Term.iri owlAsymmetricProperty⟩ : Triple) ∈ g)
      (h1 : (⟨x, p, y.toTerm⟩ : Triple) ∈ g)
      (h2 : (⟨y, p, x.toTerm⟩ : Triple) ∈ g) : Clash g
  /-- **prp-pdw** — `T(?p1, owl:propertyDisjointWith, ?p2)
  T(?x,?p1,?y) T(?x,?p2,?y) | false`. -/
  | prpPdw {p1 p2 : WfIri} {x : Subject} {y : Term}
      (hdecl : (⟨Subject.iri p1, owlPropertyDisjointWith,
        Term.iri p2⟩ : Triple) ∈ g)
      (h1 : (⟨x, p1, y⟩ : Triple) ∈ g)
      (h2 : (⟨x, p2, y⟩ : Triple) ∈ g) : Clash g
  /-- **prp-npa1** — the owl:NegativePropertyAssertion clash with an
  individual target. -/
  | prpNpa1 {i x : Subject} {p : WfIri} {y : Term}
      (hsrc : (⟨i, owlSourceIndividual, x.toTerm⟩ : Triple) ∈ g)
      (hap : (⟨i, owlAssertionProperty, Term.iri p⟩ : Triple) ∈ g)
      (hti : (⟨i, owlTargetIndividual, y⟩ : Triple) ∈ g)
      (hd : (⟨x, p, y⟩ : Triple) ∈ g) : Clash g
  /-- **prp-npa2** — the same with a literal target value. -/
  | prpNpa2 {i x : Subject} {p : WfIri} {y : Term}
      (hsrc : (⟨i, owlSourceIndividual, x.toTerm⟩ : Triple) ∈ g)
      (hap : (⟨i, owlAssertionProperty, Term.iri p⟩ : Triple) ∈ g)
      (htv : (⟨i, owlTargetValue, y⟩ : Triple) ∈ g)
      (hd : (⟨x, p, y⟩ : Triple) ∈ g) : Clash g
  /-- **cls-nothing2** — `T(?x, rdf:type, owl:Nothing) | false`. -/
  | clsNothing2 {x : Subject}
      (h : (⟨x, rdfType, Term.iri owlNothing⟩ : Triple) ∈ g) : Clash g
  /-- **cls-com** — `T(?c1, owl:complementOf, ?c2)
  T(?x, rdf:type, ?c1) T(?x, rdf:type, ?c2) | false`. -/
  | clsCom {c1 x : Subject} {c2 : Term}
      (hdecl : (⟨c1, owlComplementOf, c2⟩ : Triple) ∈ g)
      (h1 : (⟨x, rdfType, c1.toTerm⟩ : Triple) ∈ g)
      (h2 : (⟨x, rdfType, c2⟩ : Triple) ∈ g) : Clash g
  /-- **cls-maxc1** — a max-cardinality-0 restriction with a witness
  edge. -/
  | clsMaxc1 {x u : Subject} {p : WfIri} {y : Term}
      (hmc : (⟨x, owlMaxCardinality,
        Term.literal litNni0⟩ : Triple) ∈ g)
      (honp : (⟨x, owlOnProperty, Term.iri p⟩ : Triple) ∈ g)
      (hty : (⟨u, rdfType, x.toTerm⟩ : Triple) ∈ g)
      (hd : (⟨u, p, y⟩ : Triple) ∈ g) : Clash g
  /-- **cls-maxqc1** — max-qualified-cardinality 0 with a witness edge
  whose target is typed into the qualifying class. -/
  | clsMaxqc1 {x u ys : Subject} {c : Term} {p : WfIri}
      (hmqc : (⟨x, owlMaxQualifiedCardinality,
        Term.literal litNni0⟩ : Triple) ∈ g)
      (honp : (⟨x, owlOnProperty, Term.iri p⟩ : Triple) ∈ g)
      (honc : (⟨x, owlOnClass, c⟩ : Triple) ∈ g)
      (hty : (⟨u, rdfType, x.toTerm⟩ : Triple) ∈ g)
      (hd : (⟨u, p, ys.toTerm⟩ : Triple) ∈ g)
      (hyc : (⟨ys, rdfType, c⟩ : Triple) ∈ g) : Clash g
  /-- **cls-maxqc2** — the same with `owl:onClass owl:Thing`, where the
  target needs no typing premise. -/
  | clsMaxqc2 {x u : Subject} {y : Term} {p : WfIri}
      (hmqc : (⟨x, owlMaxQualifiedCardinality,
        Term.literal litNni0⟩ : Triple) ∈ g)
      (honp : (⟨x, owlOnProperty, Term.iri p⟩ : Triple) ∈ g)
      (honc : (⟨x, owlOnClass, Term.iri owlThing⟩ : Triple) ∈ g)
      (hty : (⟨u, rdfType, x.toTerm⟩ : Triple) ∈ g)
      (hd : (⟨u, p, y⟩ : Triple) ∈ g) : Clash g
  /-- **cax-dw** — `T(?c1, owl:disjointWith, ?c2)
  T(?x, rdf:type, ?c1) T(?x, rdf:type, ?c2) | false`. -/
  | caxDw {c1 x : Subject} {c2 : Term}
      (hdecl : (⟨c1, owlDisjointWith, c2⟩ : Triple) ∈ g)
      (h1 : (⟨x, rdfType, c1.toTerm⟩ : Triple) ∈ g)
      (h2 : (⟨x, rdfType, c2⟩ : Triple) ∈ g) : Clash g
  /-- **cax-adc** — an owl:AllDisjointClasses list with an individual
  typed into two DISTINCT members. (The F* row says two distinct
  POSITIONS; see the module header for why this port says distinct
  terms.) -/
  | caxAdc {y z : Subject} {lst ci cj : Term}
      (hty : (⟨y, rdfType,
        Term.iri owlAllDisjointClasses⟩ : Triple) ∈ g)
      (hmem : (⟨y, owlMembers, lst⟩ : Triple) ∈ g)
      (h1 : ListMember g lst ci)
      (h2 : ListMember g lst cj)
      (hne : ci ≠ cj)
      (t1 : (⟨z, rdfType, ci⟩ : Triple) ∈ g)
      (t2 : (⟨z, rdfType, cj⟩ : Triple) ∈ g) : Clash g
  /-- **eq-diff2** — an `owl:AllDifferent` / `owl:members` list with two
  DISTINCT members related by `owl:sameAs`. (Distinct TERMS, the same
  deviation from the table's distinct POSITIONS that cax-adc carries.) -/
  | eqDiff2 {y zi : Subject} {lst zj : Term}
      (hty : (⟨y, rdfType, Term.iri owlAllDifferent⟩ : Triple) ∈ g)
      (hmem : (⟨y, owlMembers, lst⟩ : Triple) ∈ g)
      (h1 : ListMember g lst zi.toTerm)
      (h2 : ListMember g lst zj)
      (hne : zi.toTerm ≠ zj)
      (hsame : (⟨zi, owlSameAs, zj⟩ : Triple) ∈ g) : Clash g
  /-- **eq-diff3** — the same through `owl:distinctMembers`. -/
  | eqDiff3 {y zi : Subject} {lst zj : Term}
      (hty : (⟨y, rdfType, Term.iri owlAllDifferent⟩ : Triple) ∈ g)
      (hmem : (⟨y, owlDistinctMembers, lst⟩ : Triple) ∈ g)
      (h1 : ListMember g lst zi.toTerm)
      (h2 : ListMember g lst zj)
      (hne : zi.toTerm ≠ zj)
      (hsame : (⟨zi, owlSameAs, zj⟩ : Triple) ∈ g) : Clash g
  /-- **prp-adp** — an `owl:AllDisjointProperties` list with two
  DISTINCT member properties sharing a subject-object pair. -/
  | prpAdp {y u : Subject} {lst v : Term} {p1 p2 : WfIri}
      (hty : (⟨y, rdfType,
        Term.iri owlAllDisjointProperties⟩ : Triple) ∈ g)
      (hmem : (⟨y, owlMembers, lst⟩ : Triple) ∈ g)
      (h1 : ListMember g lst (Term.iri p1))
      (h2 : ListMember g lst (Term.iri p2))
      (hne : p1 ≠ p2)
      (t1 : (⟨u, p1, v⟩ : Triple) ∈ g)
      (t2 : (⟨u, p2, v⟩ : Triple) ∈ g) : Clash g

/-! ## Structural properties

Monotonicity and cut, exactly as in `RDFS/RdfsCore.lean`: every OWL 2
RL/RDF row is a Horn rule (no negation, no counting), so nothing is
lost when the premise set grows. The list-premise relations need their
own monotonicity first. -/

theorem ListMember.mono {g g' : Graph} (hsub : ∀ u, u ∈ g → u ∈ g')
    {head e : Term} (h : ListMember g head e) : ListMember g' head e := by
  induction h with
  | here hf => exact ListMember.here (hsub _ hf)
  | there hr _ ih => exact ListMember.there (hsub _ hr) ih

theorem ListDenotes.mono {g g' : Graph} (hsub : ∀ u, u ∈ g → u ∈ g')
    {head : Term} {es : List Term} (h : ListDenotes g head es) :
    ListDenotes g' head es := by
  induction h with
  | nil => exact ListDenotes.nil
  | cons hnil hf hr _ ih =>
      exact ListDenotes.cons hnil (hsub _ hf) (hsub _ hr) ih

theorem TypesAll.mono {g g' : Graph} (hsub : ∀ u, u ∈ g → u ∈ g')
    {y : Subject} {cs : List Term} (h : TypesAll g y cs) :
    TypesAll g' y cs := by
  induction h with
  | nil => exact TypesAll.nil
  | cons hm _ ih => exact TypesAll.cons (hsub _ hm) ih

theorem ChainHolds.mono {g g' : Graph} (hsub : ∀ u, u ∈ g → u ∈ g')
    {s : Subject} {ps : List WfIri} {fin : Term}
    (h : ChainHolds g s ps fin) : ChainHolds g' s ps fin := by
  induction h with
  | nil => exact ChainHolds.nil
  | last hm => exact ChainHolds.last (hsub _ hm)
  | step hm _ ih => exact ChainHolds.step (hsub _ hm) ih

theorem SharesKeyValues.mono {g g' : Graph} (hsub : ∀ u, u ∈ g → u ∈ g')
    {x y : Subject} {ps : List WfIri} (h : SharesKeyValues g x y ps) :
    SharesKeyValues g' x y ps := by
  induction h with
  | nil => exact SharesKeyValues.nil
  | cons hx hy _ ih => exact SharesKeyValues.cons (hsub _ hx) (hsub _ hy) ih

/-- Monotonicity: a bigger graph derives at least as much. -/
theorem Derives.mono {g g' : Graph} (hsub : ∀ u, u ∈ g → u ∈ g')
    {t : Triple} (h : Derives g t) : Derives g' t := by
  induction h with
  | base hm => exact Derives.base (hsub _ hm)
  | eqRefS _ ih => exact Derives.eqRefS ih
  | eqRefP _ ih => exact Derives.eqRefP ih
  | eqRefO _ ih => exact Derives.eqRefO ih
  | eqSym _ ih => exact Derives.eqSym ih
  | eqTrans _ _ ih1 ih2 => exact Derives.eqTrans ih1 ih2
  | eqRepS _ _ ih1 ih2 => exact Derives.eqRepS ih1 ih2
  | eqRepP _ _ ih1 ih2 => exact Derives.eqRepP ih1 ih2
  | eqRepO _ _ ih1 ih2 => exact Derives.eqRepO ih1 ih2
  | prpDom _ _ ih1 ih2 => exact Derives.prpDom ih1 ih2
  | prpRng _ _ ih1 ih2 => exact Derives.prpRng ih1 ih2
  | prpFp _ _ _ ih1 ih2 ih3 => exact Derives.prpFp ih1 ih2 ih3
  | prpIfp _ _ _ ih1 ih2 ih3 => exact Derives.prpIfp ih1 ih2 ih3
  | prpSymp _ _ ih1 ih2 => exact Derives.prpSymp ih1 ih2
  | prpTrp _ _ _ ih1 ih2 ih3 => exact Derives.prpTrp ih1 ih2 ih3
  | prpSpo1 _ _ ih1 ih2 => exact Derives.prpSpo1 ih1 ih2
  | prpSpo2 _ _ hl hne hc ihgc ih =>
      exact Derives.prpSpo2 ihgc ih hl hne hc
  | prpEqp1 _ _ ih1 ih2 => exact Derives.prpEqp1 ih1 ih2
  | prpEqp2 _ _ ih1 ih2 => exact Derives.prpEqp2 ih1 ih2
  | prpInv1 _ _ ih1 ih2 => exact Derives.prpInv1 ih1 ih2
  | prpInv2 _ _ ih1 ih2 => exact Derives.prpInv2 ih1 ih2
  | prpKey _ _ hl hne _ _ hs ihgc ih1 ih2 ih3 =>
      exact Derives.prpKey ihgc ih1 hl hne ih2 ih3 hs
  | clsThing => exact Derives.clsThing
  | clsNothing1 => exact Derives.clsNothing1
  | clsInt1 _ _ hl hne ht ihgc ih =>
      exact Derives.clsInt1 ihgc ih hl hne ht
  | clsInt2 _ _ hm _ ihgc ih1 ih2 => exact Derives.clsInt2 ihgc ih1 hm ih2
  | clsUni _ _ hm _ ihgc ih1 ih2 => exact Derives.clsUni ihgc ih1 hm ih2
  | clsSvf1 _ _ _ _ ih1 ih2 ih3 ih4 => exact Derives.clsSvf1 ih1 ih2 ih3 ih4
  | clsSvf2 _ _ _ ih1 ih2 ih3 => exact Derives.clsSvf2 ih1 ih2 ih3
  | clsAvf _ _ _ _ ih1 ih2 ih3 ih4 => exact Derives.clsAvf ih1 ih2 ih3 ih4
  | clsHv1 _ _ _ ih1 ih2 ih3 => exact Derives.clsHv1 ih1 ih2 ih3
  | clsHv2 _ _ _ ih1 ih2 ih3 => exact Derives.clsHv2 ih1 ih2 ih3
  | clsHs1 _ _ _ ih1 ih2 ih3 => exact Derives.clsHs1 ih1 ih2 ih3
  | clsHs2 _ _ _ ih1 ih2 ih3 => exact Derives.clsHs2 ih1 ih2 ih3
  | clsMaxc2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact Derives.clsMaxc2 ih1 ih2 ih3 ih4 ih5
  | clsOo _ _ hm ihgc ih => exact Derives.clsOo ihgc ih hm
  | caxSco _ _ ih1 ih2 => exact Derives.caxSco ih1 ih2
  | caxEqc1 _ _ ih1 ih2 => exact Derives.caxEqc1 ih1 ih2
  | caxEqc2 _ _ ih1 ih2 => exact Derives.caxEqc2 ih1 ih2
  | scmClsSelf _ ih => exact Derives.scmClsSelf ih
  | scmClsEqc _ ih => exact Derives.scmClsEqc ih
  | scmClsThing _ ih => exact Derives.scmClsThing ih
  | scmClsNothing _ ih => exact Derives.scmClsNothing ih
  | scmSco _ _ ih1 ih2 => exact Derives.scmSco ih1 ih2
  | scmEqc1a _ ih => exact Derives.scmEqc1a ih
  | scmEqc1b _ ih => exact Derives.scmEqc1b ih
  | scmEqc2 _ _ ih1 ih2 => exact Derives.scmEqc2 ih1 ih2
  | scmSpo _ _ ih1 ih2 => exact Derives.scmSpo ih1 ih2
  | scmEqp1a _ ih => exact Derives.scmEqp1a ih
  | scmEqp1b _ ih => exact Derives.scmEqp1b ih
  | scmEqp2 _ _ ih1 ih2 => exact Derives.scmEqp2 ih1 ih2
  | scmDom1 _ _ ih1 ih2 => exact Derives.scmDom1 ih1 ih2
  | scmDom2 _ _ ih1 ih2 => exact Derives.scmDom2 ih1 ih2
  | scmRng1 _ _ ih1 ih2 => exact Derives.scmRng1 ih1 ih2
  | scmRng2 _ _ ih1 ih2 => exact Derives.scmRng2 ih1 ih2
  | scmInt _ _ hm ihgc ih => exact Derives.scmInt ihgc ih hm
  | scmUni _ _ hm ihgc ih => exact Derives.scmUni ihgc ih hm
  -- `[ext]` rows
  | eqDiffSym _ ih => exact Derives.eqDiffSym ih
  | pdwToDiff _ _ _ hne ih1 ih2 ih3 => exact Derives.pdwToDiff ih1 ih2 ih3 hne
  | caxDwToDiff _ _ _ hne ih1 ih2 ih3 =>
      exact Derives.caxDwToDiff ih1 ih2 ih3 hne
  | fpDiffToDiff _ _ _ _ hne ih1 ih2 ih3 ih4 =>
      exact Derives.fpDiffToDiff ih1 ih2 ih3 ih4 hne
  | ifpDiffToDiff _ _ _ _ hne ih1 ih2 ih3 ih4 =>
      exact Derives.ifpDiffToDiff ih1 ih2 ih3 ih4 hne
  | chainToTrans _ _ hl ihgc ih => exact Derives.chainToTrans ihgc ih hl
  | prpRfl _ _ hind ihgc ih => exact Derives.prpRfl ihgc ih hind
  | xsdAxioms _ hx hax ih => exact Derives.xsdAxioms ih hx hax
  | dtRangeIntersect _ _ hlic ih1 ih2 =>
      exact Derives.dtRangeIntersect ih1 ih2 hlic
  | premiseFreeAxiom hax => exact Derives.premiseFreeAxiom hax
  | caxDwToComplement _ hax ih => exact Derives.caxDwToComplement ih hax
  | clsMaxqc1ToComplement _ _ _ _ _ _ _ _ hax ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 =>
      exact Derives.clsMaxqc1ToComplement ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 hax
  | minCard1Comprehension _ hax ih => exact Derives.minCard1Comprehension ih hax
  | caxAdcToDw _ _ _ h1 h2 hne ihgc ih1 ih2 =>
      exact Derives.caxAdcToDw ihgc ih1 ih2 h1 h2 hne
  | invFlipDomRng _ _ ih1 ih2 => exact Derives.invFlipDomRng ih1 ih2
  | invFlipRngDom _ _ ih1 ih2 => exact Derives.invFlipRngDom ih1 ih2
  | invFlipDomRngRev _ _ ih1 ih2 => exact Derives.invFlipDomRngRev ih1 ih2
  | invFlipRngDomRev _ _ ih1 ih2 => exact Derives.invFlipRngDomRev ih1 ih2

/-- Cut: if every triple of `g'` is derivable from `g`, then everything
derivable from `g'` is derivable from `g`. This is what makes the
iterated closure sound — each round's output is derivable from the
round's input, and cut chains the rounds.

The list-premise rows are the reason those constructors carry a
COLLECTION GRAPH `gc` and the side condition `hgc : ∀ u ∈ gc, Derives g
u`, instead of reading `g` directly. Without it cut is FALSE for those
rows: a round can DERIVE an `rdf:first`/`rdf:rest` triple (eq-rep-s and
prp-spo1 both can), so a later round's collection walk may rest on
structure the earlier graph never asserted, and there is no way to pull
that walk back to `g`. With `gc` a parameter, cut just carries the
side condition through its own induction hypothesis. -/
theorem Derives.cut {g g' : Graph} (hall : ∀ u, u ∈ g' → Derives g u)
    {t : Triple} (h : Derives g' t) : Derives g t := by
  induction h with
  | base hm => exact hall _ hm
  | eqRefS _ ih => exact Derives.eqRefS ih
  | eqRefP _ ih => exact Derives.eqRefP ih
  | eqRefO _ ih => exact Derives.eqRefO ih
  | eqSym _ ih => exact Derives.eqSym ih
  | eqTrans _ _ ih1 ih2 => exact Derives.eqTrans ih1 ih2
  | eqRepS _ _ ih1 ih2 => exact Derives.eqRepS ih1 ih2
  | eqRepP _ _ ih1 ih2 => exact Derives.eqRepP ih1 ih2
  | eqRepO _ _ ih1 ih2 => exact Derives.eqRepO ih1 ih2
  | prpDom _ _ ih1 ih2 => exact Derives.prpDom ih1 ih2
  | prpRng _ _ ih1 ih2 => exact Derives.prpRng ih1 ih2
  | prpFp _ _ _ ih1 ih2 ih3 => exact Derives.prpFp ih1 ih2 ih3
  | prpIfp _ _ _ ih1 ih2 ih3 => exact Derives.prpIfp ih1 ih2 ih3
  | prpSymp _ _ ih1 ih2 => exact Derives.prpSymp ih1 ih2
  | prpTrp _ _ _ ih1 ih2 ih3 => exact Derives.prpTrp ih1 ih2 ih3
  | prpSpo1 _ _ ih1 ih2 => exact Derives.prpSpo1 ih1 ih2
  | prpSpo2 _ _ hl hne hc ihgc ih =>
      exact Derives.prpSpo2 ihgc ih hl hne hc
  | prpEqp1 _ _ ih1 ih2 => exact Derives.prpEqp1 ih1 ih2
  | prpEqp2 _ _ ih1 ih2 => exact Derives.prpEqp2 ih1 ih2
  | prpInv1 _ _ ih1 ih2 => exact Derives.prpInv1 ih1 ih2
  | prpInv2 _ _ ih1 ih2 => exact Derives.prpInv2 ih1 ih2
  | prpKey _ _ hl hne _ _ hs ihgc ih1 ih2 ih3 =>
      exact Derives.prpKey ihgc ih1 hl hne ih2 ih3 hs
  | clsThing => exact Derives.clsThing
  | clsNothing1 => exact Derives.clsNothing1
  | clsInt1 _ _ hl hne ht ihgc ih =>
      exact Derives.clsInt1 ihgc ih hl hne ht
  | clsInt2 _ _ hm _ ihgc ih1 ih2 => exact Derives.clsInt2 ihgc ih1 hm ih2
  | clsUni _ _ hm _ ihgc ih1 ih2 => exact Derives.clsUni ihgc ih1 hm ih2
  | clsSvf1 _ _ _ _ ih1 ih2 ih3 ih4 => exact Derives.clsSvf1 ih1 ih2 ih3 ih4
  | clsSvf2 _ _ _ ih1 ih2 ih3 => exact Derives.clsSvf2 ih1 ih2 ih3
  | clsAvf _ _ _ _ ih1 ih2 ih3 ih4 => exact Derives.clsAvf ih1 ih2 ih3 ih4
  | clsHv1 _ _ _ ih1 ih2 ih3 => exact Derives.clsHv1 ih1 ih2 ih3
  | clsHv2 _ _ _ ih1 ih2 ih3 => exact Derives.clsHv2 ih1 ih2 ih3
  | clsHs1 _ _ _ ih1 ih2 ih3 => exact Derives.clsHs1 ih1 ih2 ih3
  | clsHs2 _ _ _ ih1 ih2 ih3 => exact Derives.clsHs2 ih1 ih2 ih3
  | clsMaxc2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact Derives.clsMaxc2 ih1 ih2 ih3 ih4 ih5
  | clsOo _ _ hm ihgc ih => exact Derives.clsOo ihgc ih hm
  | caxSco _ _ ih1 ih2 => exact Derives.caxSco ih1 ih2
  | caxEqc1 _ _ ih1 ih2 => exact Derives.caxEqc1 ih1 ih2
  | caxEqc2 _ _ ih1 ih2 => exact Derives.caxEqc2 ih1 ih2
  | scmClsSelf _ ih => exact Derives.scmClsSelf ih
  | scmClsEqc _ ih => exact Derives.scmClsEqc ih
  | scmClsThing _ ih => exact Derives.scmClsThing ih
  | scmClsNothing _ ih => exact Derives.scmClsNothing ih
  | scmSco _ _ ih1 ih2 => exact Derives.scmSco ih1 ih2
  | scmEqc1a _ ih => exact Derives.scmEqc1a ih
  | scmEqc1b _ ih => exact Derives.scmEqc1b ih
  | scmEqc2 _ _ ih1 ih2 => exact Derives.scmEqc2 ih1 ih2
  | scmSpo _ _ ih1 ih2 => exact Derives.scmSpo ih1 ih2
  | scmEqp1a _ ih => exact Derives.scmEqp1a ih
  | scmEqp1b _ ih => exact Derives.scmEqp1b ih
  | scmEqp2 _ _ ih1 ih2 => exact Derives.scmEqp2 ih1 ih2
  | scmDom1 _ _ ih1 ih2 => exact Derives.scmDom1 ih1 ih2
  | scmDom2 _ _ ih1 ih2 => exact Derives.scmDom2 ih1 ih2
  | scmRng1 _ _ ih1 ih2 => exact Derives.scmRng1 ih1 ih2
  | scmRng2 _ _ ih1 ih2 => exact Derives.scmRng2 ih1 ih2
  | scmInt _ _ hm ihgc ih => exact Derives.scmInt ihgc ih hm
  | scmUni _ _ hm ihgc ih => exact Derives.scmUni ihgc ih hm
  -- `[ext]` rows
  | eqDiffSym _ ih => exact Derives.eqDiffSym ih
  | pdwToDiff _ _ _ hne ih1 ih2 ih3 => exact Derives.pdwToDiff ih1 ih2 ih3 hne
  | caxDwToDiff _ _ _ hne ih1 ih2 ih3 =>
      exact Derives.caxDwToDiff ih1 ih2 ih3 hne
  | fpDiffToDiff _ _ _ _ hne ih1 ih2 ih3 ih4 =>
      exact Derives.fpDiffToDiff ih1 ih2 ih3 ih4 hne
  | ifpDiffToDiff _ _ _ _ hne ih1 ih2 ih3 ih4 =>
      exact Derives.ifpDiffToDiff ih1 ih2 ih3 ih4 hne
  | chainToTrans _ _ hl ihgc ih => exact Derives.chainToTrans ihgc ih hl
  | prpRfl _ _ hind ihgc ih => exact Derives.prpRfl ihgc ih hind
  | xsdAxioms _ hx hax ih => exact Derives.xsdAxioms ih hx hax
  | dtRangeIntersect _ _ hlic ih1 ih2 =>
      exact Derives.dtRangeIntersect ih1 ih2 hlic
  | premiseFreeAxiom hax => exact Derives.premiseFreeAxiom hax
  | caxDwToComplement _ hax ih => exact Derives.caxDwToComplement ih hax
  | clsMaxqc1ToComplement _ _ _ _ _ _ _ _ hax ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 =>
      exact Derives.clsMaxqc1ToComplement ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 hax
  | minCard1Comprehension _ hax ih => exact Derives.minCard1Comprehension ih hax
  | caxAdcToDw _ _ _ h1 h2 hne ihgc ih1 ih2 =>
      exact Derives.caxAdcToDw ihgc ih1 ih2 h1 h2 hne
  | invFlipDomRng _ _ ih1 ih2 => exact Derives.invFlipDomRng ih1 ih2
  | invFlipRngDom _ _ ih1 ih2 => exact Derives.invFlipRngDom ih1 ih2
  | invFlipDomRngRev _ _ ih1 ih2 => exact Derives.invFlipDomRngRev ih1 ih2
  | invFlipRngDomRev _ _ ih1 ih2 => exact Derives.invFlipRngDomRev ih1 ih2

/-- Clash detection is monotone too: a bigger graph clashes at least as
often. -/
theorem Clash.mono {g g' : Graph} (hsub : ∀ u, u ∈ g → u ∈ g')
    (h : Clash g) : Clash g' := by
  cases h with
  | eqDiff1 h1 h2 => exact Clash.eqDiff1 (hsub _ h1) (hsub _ h2)
  | prpIrp hd hh => exact Clash.prpIrp (hsub _ hd) (hsub _ hh)
  | prpAsyp hd h1 h2 => exact Clash.prpAsyp (hsub _ hd) (hsub _ h1) (hsub _ h2)
  | prpPdw hd h1 h2 => exact Clash.prpPdw (hsub _ hd) (hsub _ h1) (hsub _ h2)
  | prpNpa1 a b c d =>
      exact Clash.prpNpa1 (hsub _ a) (hsub _ b) (hsub _ c) (hsub _ d)
  | prpNpa2 a b c d =>
      exact Clash.prpNpa2 (hsub _ a) (hsub _ b) (hsub _ c) (hsub _ d)
  | clsNothing2 h => exact Clash.clsNothing2 (hsub _ h)
  | clsCom hd h1 h2 => exact Clash.clsCom (hsub _ hd) (hsub _ h1) (hsub _ h2)
  | clsMaxc1 a b c d =>
      exact Clash.clsMaxc1 (hsub _ a) (hsub _ b) (hsub _ c) (hsub _ d)
  | clsMaxqc1 a b c d e f =>
      exact Clash.clsMaxqc1 (hsub _ a) (hsub _ b) (hsub _ c) (hsub _ d)
        (hsub _ e) (hsub _ f)
  | clsMaxqc2 a b c d e =>
      exact Clash.clsMaxqc2 (hsub _ a) (hsub _ b) (hsub _ c) (hsub _ d)
        (hsub _ e)
  | caxDw hd h1 h2 => exact Clash.caxDw (hsub _ hd) (hsub _ h1) (hsub _ h2)
  | caxAdc a b h1 h2 hne t1 t2 =>
      exact Clash.caxAdc (hsub _ a) (hsub _ b) (h1.mono hsub) (h2.mono hsub)
        hne (hsub _ t1) (hsub _ t2)
  | eqDiff2 a b h1 h2 hne t =>
      exact Clash.eqDiff2 (hsub _ a) (hsub _ b) (h1.mono hsub) (h2.mono hsub)
        hne (hsub _ t)
  | eqDiff3 a b h1 h2 hne t =>
      exact Clash.eqDiff3 (hsub _ a) (hsub _ b) (h1.mono hsub) (h2.mono hsub)
        hne (hsub _ t)
  | prpAdp a b h1 h2 hne t1 t2 =>
      exact Clash.prpAdp (hsub _ a) (hsub _ b) (h1.mono hsub) (h2.mono hsub)
        hne (hsub _ t1) (hsub _ t2)

end L4Factoidal.OWL.RL
