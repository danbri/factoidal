/-
L4Factoidal.RDF.Semantics — interpretations, denotation, satisfaction.

Ports the interpretation core of `formal/fstar/OWL.Semantics.fst`:
Hayes, RDF 1.1 Semantics §5 (simple interpretations) merged with the
OWL 2 RDF-Based Semantics interpretation structure §4 (IR, IP, IEXT,
ICEXT).

This is the model-theoretic side of the entailment ladder. The three
`*.Spec` modules transcribe the SYNTACTIC characterisations; this
supplies the structures those characterisations are supposed to be
about, so the two can be related by proof instead of by assertion.

## Deliberate enlargements, and why they are safe

The record below is a SUPERSET of the genuine simple interpretations:

* `iext` is totalised over the domain rather than typed on IP — the
  "p in IP" side conditions are dropped;
* `iLit` is total over well-formed literals; the specification sends an
  ill-typed literal to an arbitrary resource anyway;
* a blank-node assignment is total, where the specification's is
  partial. Every partial assignment extends to a total one using the
  domain's witness, so the existential in `Satisfies` is unchanged.

Each of those ENLARGES the class of interpretations. For a SOUNDNESS
result — "every interpretation satisfying A satisfies B" — a larger
class is a stronger statement, so the enlargements cost nothing there.
They would matter for a completeness result, which is why the one
completeness direction this file does not prove is named rather than
assumed.

## `Prop`, not `Bool`

Satisfaction over an infinite domain is definable and not decidable,
and never needs to be decided: the theorems quantify over it.
-/
import L4Factoidal.RDF.EntailmentSimpleSpec
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.RDF

/-! ## Interpretations -/

/-- A simple interpretation, folded into one record.

`idom` is the domain of discourse IR, an arbitrary type with at least
one inhabitant. Infinite domains and embedded datatype value spaces
come for free: any type may serve, and nothing here ever decides or
enumerates membership.

`iTt` gives an RDF 1.2 triple term a denotation as an uninterpreted
function of its components' denotations, which keeps `denotTerm` total
and compositional without committing to a reading the specifications do
not give. -/
structure Interp where
  idom : Type
  idomWit : idom
  iIri : WfIri → idom
  iLit : WfLiteral → idom
  iTt : idom → idom → idom → idom
  iext : idom → idom → idom → Prop

/-- A blank-node assignment — Hayes' "mapping A". -/
abbrev BnodeAssignment (d : Type) := BNodeId → d

/-! ## Denotation -/

def denotSubject (i : Interp) (a : BnodeAssignment i.idom) : Subject → i.idom
  | .iri x => i.iIri x
  | .bnode b => a b

def denotTerm (i : Interp) (a : BnodeAssignment i.idom) : Term → i.idom
  | .iri x => i.iIri x
  | .bnode b => a b
  | .literal l => i.iLit l
  | .tripleTerm s p o => i.iTt (denotSubject i a s) (i.iIri p) (denotTerm i a o)

/-- A subject denotes the same resource in either role. Mechanical, and
used constantly, because the rule rows round-trip objects into
subjects. -/
theorem denot_subjTerm (i : Interp) (a : BnodeAssignment i.idom) (s : Subject) :
    denotTerm i a (subjTerm s) = denotSubject i a s := by
  cases s <;> rfl

theorem denot_toSubject? (i : Interp) (a : BnodeAssignment i.idom)
    {t : Term} {s : Subject} (h : t.toSubject? = some s) :
    denotSubject i a s = denotTerm i a t := by
  rw [← subjTerm_of_toSubject? h, denot_subjTerm]

/-! ## Satisfaction and entailment -/

/-- One triple is true under a fixed assignment when the pair of the
subject's and object's denotations is in IEXT of the predicate's. -/
def TripleHolds (i : Interp) (a : BnodeAssignment i.idom) (t : Triple) : Prop :=
  i.iext (i.iIri t.p) (denotSubject i a t.s) (denotTerm i a t.o)

/-- A whole graph under a FIXED assignment. Soundness proofs work at
this level: the rule rows mint no fresh blank nodes, so one assignment
serves input and output alike. -/
def HoldsAll (i : Interp) (a : BnodeAssignment i.idom) (g : Graph) : Prop :=
  ∀ t : Triple, t ∈ g → TripleHolds i a t

/-- Hayes §5.2: "I(G) = true if [I+A](G) = true for SOME mapping A." -/
def Satisfies (i : Interp) (g : Graph) : Prop :=
  ∃ a : BnodeAssignment i.idom, HoldsAll i a g

/-- Entailment relative to a class of interpretations, kept as a
parameter so a later rung can grow the condition bundle without
restating theorems. -/
def EntailsUnder (conds : Interp → Prop) (g1 g2 : Graph) : Prop :=
  ∀ i : Interp, conds i → Satisfies i g1 → Satisfies i g2

/-- Simple entailment, model-theoretically — RDF 1.1 Semantics §5.2
verbatim: "A graph G simply entails a graph E when every interpretation
which satisfies G also satisfies E." No condition on the
interpretation, which is what makes it the BOTTOM rung. -/
def SimpleEntailsMt (a b : Graph) : Prop := ∀ i : Interp, Satisfies i a → Satisfies i b

/-! ## Class extension — ICEXT, OWL 2 RDF-Based Semantics §4.2 -/

def icext (i : Interp) (x c : i.idom) : Prop := i.iext (i.iIri RDFS.rdfType) x c

/-! ## The interpolation lemma, sound direction

RDF 1.1 Semantics §5.3: "G simply entails a graph E if and only if a
subgraph of G is an instance of E."

`interpolationSound` is that read as an implication from the SYNTACTIC
side: if some instance of `b` sits inside `a`, then every
interpretation satisfying `a` satisfies `b`. That is the direction a
decision procedure needs — it turns a found instance mapping into an
entailment claim.

The witness is the COMPOSED assignment: send a blank-node label through
the substitution, then take the denotation of the result. -/

def composedAssignment (i : Interp) (aa : BnodeAssignment i.idom) (m : BnodeSubst) :
    BnodeAssignment i.idom := fun l => denotTerm i aa (m l)

theorem subst_denot_subj (i : Interp) (aa : BnodeAssignment i.idom) (m : BnodeSubst)
    {ps gs : Subject} (h : SubjInst m ps gs) :
    denotSubject i (composedAssignment i aa m) ps = denotSubject i aa gs := by
  cases ps with
  | iri x => simp only [SubjInst] at h; subst h; rfl
  | bnode b =>
      simp only [SubjInst] at h
      simp only [denotSubject, composedAssignment, h, denot_subjTerm]

theorem subst_denot_term (i : Interp) (aa : BnodeAssignment i.idom) (m : BnodeSubst) :
    ∀ {pat g : Term}, TermInst m pat g →
      denotTerm i (composedAssignment i aa m) pat = denotTerm i aa g
  | .bnode b, g, h => by
      simp only [TermInst] at h
      simp only [denotTerm, composedAssignment, h]
  | .iri x, g, h => by simp only [TermInst] at h; subst h; rfl
  | .literal l, g, h => by simp only [TermInst] at h; subst h; rfl
  | .tripleTerm ps pp po, g, h => by
      obtain ⟨gs, go, rfl, hs, ho⟩ := h
      simp only [denotTerm, subst_denot_subj i aa m hs, subst_denot_term i aa m ho]

theorem subst_triple_holds (i : Interp) (aa : BnodeAssignment i.idom) (m : BnodeSubst)
    {tb ta : Triple} (hrel : TripleInst m tb ta) (h : TripleHolds i aa ta) :
    TripleHolds i (composedAssignment i aa m) tb := by
  obtain ⟨hp, hs, ho⟩ := hrel
  simp only [TripleHolds, hp, subst_denot_subj i aa m hs, subst_denot_term i aa m ho]
  exact h

/-- **The sound direction.** A subgraph of `a` being an instance of `b`
implies that every interpretation satisfying `a` satisfies `b`. -/
theorem interpolationSound {a b : Graph} (h : SimpleEntailmentSpec a b) :
    SimpleEntailsMt a b := by
  obtain ⟨m, hm⟩ := h
  intro i hsat
  obtain ⟨aa, haa⟩ := hsat
  refine ⟨composedAssignment i aa m, fun tb htb => ?_⟩
  obtain ⟨ta, hta, hrel⟩ := hm tb htb
  exact subst_triple_holds i aa m hrel (haa ta hta)

/-- The same from the tree's own COMPUTED definition, so the decision
procedure's answer reaches the model theory in one step. -/
theorem simpleEntails_sound_mt {a b : Graph} (h : SimpleEntails a b) :
    SimpleEntailsMt a b :=
  interpolationSound ((spec_iff_simpleEntails a b).mpr h)

/-! ## The interpolation lemma, complete direction

The converse needs the HERBRAND interpretation: domain the RDF terms,
each IRI and literal denoting itself, and a triple `⟨s, p, o⟩` of `a`
putting `⟨s-as-term, o⟩` into IEXT of `p-as-term`.

Under it "true" means "literally a triple of `a`", so an assignment
satisfying `b` IS a witnessing substitution — the existential
blank-node semantics and the instance condition become one statement.

The enlargements the header lists are exactly what has to be checked
here, and they pass: the Herbrand record is buildable in the enlarged
type, with `iTt` as the quarantine point. It is given a CONSTANT value,
which is why both graphs must be triple-term-free — RDF 1.2 triple
terms have no denotation in either baseline's model theory, and the
constant would make two distinct triple terms denote the same
resource. -/

theorem subjTerm_injective {s1 s2 : Subject} (h : subjTerm s1 = subjTerm s2) : s1 = s2 := by
  cases s1 <;> cases s2 <;> simp_all [subjTerm]

def herbIext (a : Graph) (p x y : Term) : Prop :=
  ∃ t : Triple, t ∈ a ∧ p = Term.iri t.p ∧ x = subjTerm t.s ∧ y = t.o

def herbrand (a : Graph) : Interp :=
  { idom := Term
  , idomWit := .bnode ""
  , iIri := fun x => .iri x
  , iLit := fun l => .literal l
    -- the quarantine point: a constant, hence the triple-term-free
    -- hypothesis on both graphs
  , iTt := fun _ _ _ => .bnode ""
  , iext := herbIext a }

/-- The identity assignment: every blank node denotes itself. -/
def herbId (a : Graph) : BnodeAssignment (herbrand a).idom := fun l => Term.bnode l

theorem herb_denot_subj_id (a : Graph) (s : Subject) :
    denotSubject (herbrand a) (herbId a) s = subjTerm s := by
  cases s <;> rfl

theorem herb_denot_term_id (a : Graph) : ∀ {t : Term}, TermTtFree t →
    denotTerm (herbrand a) (herbId a) t = t
  | .iri _, _ => rfl
  | .bnode _, _ => rfl
  | .literal _, _ => rfl
  | .tripleTerm _ _ _, h => absurd h (by simp [TermTtFree])

/-- A graph satisfies ITSELF under its own Herbrand interpretation. -/
theorem herbrand_satisfies {a : Graph} (h : GraphTtFree a) : Satisfies (herbrand a) a := by
  refine ⟨herbId a, fun t ht => ?_⟩
  simp only [TripleHolds, herb_denot_subj_id, herb_denot_term_id a (h t ht)]
  exact ⟨t, ht, rfl, rfl, rfl⟩

/-- Under the Herbrand interpretation, DENOTATION IS SUBSTITUTION: an
assignment read as a substitution relates a pattern to its own
denotation exactly as the instance relation demands. -/
theorem herb_denot_is_subj_inst {a : Graph} (ab : BnodeAssignment (herbrand a).idom)
    {ps gs : Subject} (h : denotSubject (herbrand a) ab ps = subjTerm gs) :
    SubjInst ab ps gs := by
  cases ps with
  | iri i =>
      have : subjTerm (Subject.iri i) = subjTerm gs := h
      exact (subjTerm_injective this).symm
  | bnode b => exact h

theorem herb_denot_is_term_inst {a : Graph} (ab : BnodeAssignment (herbrand a).idom) :
    ∀ {pat g : Term}, TermTtFree pat → denotTerm (herbrand a) ab pat = g →
      TermInst ab pat g
  | .bnode _, _, _, h => h
  | .iri _, _, _, h => h.symm
  | .literal _, _, _, h => h.symm
  | .tripleTerm _ _ _, _, htt, _ => absurd htt (by simp [TermTtFree])

/-- If the Herbrand interpretation of `a` satisfies `b`, the witnessing
assignment IS an instance-subgraph witness. -/
theorem herbrand_reflects {a b : Graph} (hsat : Satisfies (herbrand a) b)
    (htt : GraphTtFree b) : SimpleEntailmentSpec a b := by
  obtain ⟨ab, hab⟩ := hsat
  refine ⟨ab, fun tb htb => ?_⟩
  obtain ⟨t, hta, hp, hs, ho⟩ := hab tb htb
  refine ⟨t, hta, ?_, herb_denot_is_subj_inst ab hs,
          herb_denot_is_term_inst ab (htt tb htb) ho⟩
  simpa [herbrand] using hp

/-- **The hard direction**, for triple-term-free graphs. -/
theorem interpolationComplete {a b : Graph} (h : SimpleEntailsMt a b)
    (hta : GraphTtFree a) (htb : GraphTtFree b) : SimpleEntailmentSpec a b :=
  herbrand_reflects (h (herbrand a) (herbrand_satisfies hta)) htb

/-- **The interpolation lemma of RDF 1.1 Semantics §5.3**, proved
rather than assumed: the syntactic characterisation and the
model-theoretic definition pick out the same pairs of graphs. -/
theorem interpolationLemma {a b : Graph} (hta : GraphTtFree a) (htb : GraphTtFree b) :
    SimpleEntailmentSpec a b ↔ SimpleEntailsMt a b :=
  ⟨interpolationSound, fun h => interpolationComplete h hta htb⟩

/-- And therefore the tree's own decision procedure, when it says yes,
is saying something about every interpretation. -/
theorem simpleEntails_iff_mt {a b : Graph} (hta : GraphTtFree a) (htb : GraphTtFree b) :
    SimpleEntails a b ↔ SimpleEntailsMt a b :=
  ⟨simpleEntails_sound_mt,
   fun h => (spec_iff_simpleEntails a b).mp (interpolationComplete h hta htb)⟩

/-! ## Blank-node locality

Satisfaction depends only on the assignment's values at the blank-node
labels the graph actually mentions. Needed by any argument that
combines two graphs' assignments. -/

def subjectBnodes : Subject → List BNodeId
  | .iri _ => []
  | .bnode b => [b]

def termBnodes : Term → List BNodeId
  | .iri _ => []
  | .bnode b => [b]
  | .literal _ => []
  | .tripleTerm s _ o => subjectBnodes s ++ termBnodes o

def tripleBnodes (t : Triple) : List BNodeId := subjectBnodes t.s ++ termBnodes t.o

def graphBnodeIds (g : Graph) : List BNodeId := g.flatMap tripleBnodes

def AssignmentsAgreeOn (i : Interp) (bs : List BNodeId)
    (a1 a2 : BnodeAssignment i.idom) : Prop := ∀ b ∈ bs, a1 b = a2 b

theorem denot_subject_agree (i : Interp) {a1 a2 : BnodeAssignment i.idom} {s : Subject}
    (h : AssignmentsAgreeOn i (subjectBnodes s) a1 a2) :
    denotSubject i a1 s = denotSubject i a2 s := by
  cases s with
  | iri _ => rfl
  | bnode b => exact h b (List.mem_singleton.mpr rfl)

theorem denot_term_agree (i : Interp) {a1 a2 : BnodeAssignment i.idom} :
    ∀ {t : Term}, AssignmentsAgreeOn i (termBnodes t) a1 a2 →
      denotTerm i a1 t = denotTerm i a2 t
  | .iri _, _ => rfl
  | .bnode b, h => h b (List.mem_singleton.mpr rfl)
  | .literal _, _ => rfl
  | .tripleTerm s _ o, h => by
      simp only [denotTerm]
      rw [denot_subject_agree i (fun b hb => h b (List.mem_append_left _ hb)),
          denot_term_agree i (fun b hb => h b (List.mem_append_right _ hb))]

theorem tripleHolds_agree (i : Interp) {a1 a2 : BnodeAssignment i.idom} {t : Triple}
    (h : AssignmentsAgreeOn i (tripleBnodes t) a1 a2) :
    TripleHolds i a1 t ↔ TripleHolds i a2 t := by
  simp only [TripleHolds,
    denot_subject_agree i (fun b hb => h b (List.mem_append_left _ hb)),
    denot_term_agree i (fun b hb => h b (List.mem_append_right _ hb))]

/-! ## Build-time checks

The definitions above are `Prop`-valued over an arbitrary domain, so
nothing here can be decided by evaluation. What CAN be checked is the
syntactic machinery the theorems rest on. -/

section Checks

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

#guard subjectBnodes (.bnode "x") == ["x"]
#guard subjectBnodes (.iri (iriW "http://e.org/a")) == []
#guard termBnodes (.tripleTerm (.bnode "s") (iriW "http://e.org/p") (.bnode "o")) == ["s", "o"]
#guard graphBnodeIds [⟨.bnode "x", iriW "http://e.org/p", .bnode "y"⟩] == ["x", "y"]

/-! A ground graph mentions none, which is what makes the locality
lemmas say something about it rather than nothing. -/

#guard graphBnodeIds [⟨.iri (iriW "http://e.org/a"), iriW "http://e.org/p",
                       .iri (iriW "http://e.org/b")⟩] == []

end Checks

end L4Factoidal.RDF
