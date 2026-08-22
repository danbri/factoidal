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
* **Every `[ext]` rule of the F* engine ledger** — the comprehension-
  witness layer (`svf2_existential_witness`, `minc1_bridge`,
  `cls_hasself1/2`, `cls_svf_thing_*`), the differentFrom-synthesis
  family (`pdw_to_differentFrom`, `fp_diff_to_diff`,
  `cax_dw_to_differentFrom`), the chain/transitivity bridges, and the
  `#236` `cls_maxqc_comp` anchor machinery. Those are sound EXTENSIONS
  whose justification lives in each rule's own F* banner, not W3C
  table rows. A port of the table is a port of the table.

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

end L4Factoidal.OWL.RL
