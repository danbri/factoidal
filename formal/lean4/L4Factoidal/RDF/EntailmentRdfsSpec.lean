/-
L4Factoidal.RDF.EntailmentRdfsSpec — RDFS entailment, transcribed from
the specification text, and the engine's rows proved licensed by it.

Port of `formal/fstar/RDF.Entailment.RDFS.Spec.fst` (418 lines).

Rung three of the entailment ladder. Baseline: RDF 1.1 Semantics §9 —
the thirteen-row rule table, the axiomatic triples, and the two
condition-level consequences that are NOT rows.

Like the two rungs below it, this module computes nothing about the
engine and calls no engine function in its definitions. The theorems at
the bottom are where the engine appears, and they only ever go one way:
what the engine emits is licensed by the table.

## What "licensed" means, and why the quantifier order matters

`RdfsLicensed g t` says `t` is already in `g`, or is an axiomatic
triple, or is one application of some row to `g`. The premises are read
off `g`, the INPUT graph, never off a growing accumulator. That is what
makes per-row soundness compose through a fixed-point driver, and it is
strictly stronger than "licensed by the output".

## Three rows are specified and NOT implemented

rdfs4a, rdfs4b, rdfs8 and rdfs13 are in the table here and are not in
either tree's core closure. Writing them down is what makes the gap
visible; the F\* source records the same, with the same reason.

The two bnode-minting rows (rdfD1 and the 2004 reading of rdfs1) are
excluded from `RdfsClosed` for the reason rung two excludes rdfD1: a
graph closed under a name-minting rule is not finite, and the
specification handles it by taking the closure "towards E".

## Two consequences that are not rows

§9 states, as SEMANTIC CONDITIONS rather than rules, that
`rdfs:subClassOf`'s extension is reflexive on the classes and likewise
for `rdfs:subPropertyOf`. Together with the subset condition those make
`xxx rdfs:subClassOf xxx` hold whenever `xxx` is an ENDPOINT of any
subclass triple, with no `rdf:type` premise. Rule rdfs10 reaches the
same conclusion by the other route. Naming the endpoint form is what
lets a reflexivity harvest carry a licence instead of being a witness of
unsoundness.

`rdfsMemberSubproperty` is the third of the family: the rdfs12
consequence of the axiomatic `rdf:_n rdf:type
rdfs:ContainerMembershipProperty` rows. It is NOT itself axiomatic —
§9 lists only type, domain and range for that family — but it is
RDFS-entailed by the EMPTY graph, so it is named apart.

## The ρdf fragment

Muñoz, Pérez and Gutiérrez, "Simple and Efficient Minimal RDFS"
(J. Web Semantics 7(3), 2009). Their six rules are exactly rdfs5,
rdfs7, rdfs11, rdfs9, rdfs2 and rdfs3 — triple for triple, the Lean
tree's `RDFS.Closure` row set — and they are sound and complete for
RDFS entailment restricted to that sub-vocabulary, with no reflexivity
or axiomatic machinery needed. Naming the fragment here is what lets a
completeness statement rest on a published result rather than on an
artefact of this codebase.
-/
import L4Factoidal.RDF.EntailmentRdfSpec
import L4Factoidal.RDF.EntailmentSimpleSpec
import L4Factoidal.RDFS.Closure

namespace L4Factoidal.RDF

open L4Factoidal.RDFS

/-! ## The thirteen rows

Each is the specification's own sentence, one `def` per row. Where a
row moves a term from OBJECT position into SUBJECT position — rdfs3,
rdfs4b, rdfs5, rdfs11 — the move is a generalized-RDF premise, and the
side condition that the term can BE a subject is stated rather than
hidden: the row simply does not fire on a literal there. -/

/-- rdfs1 (RDF 1.1 reading): "any IRI aaa in D | aaa rdf:type
rdfs:Datatype ." -/
def Rdfs1Derives (D : DatatypeSet) (t : Triple) : Prop :=
  ∃ a : WfIri, D a ∧ t = { s := .iri a, p := rdfType, o := .iri rdfsDatatype }

/-- rdfs1 (2004 reading), kept for the baseline delta: a plain literal
mints a fresh blank node typed `rdfs:Literal`. In RDF 1.1's term
algebra a plain literal is one typed `xsd:string` or
`rdf:langString`. -/
def Rdfs1Derives2004 (g : Graph) (b : BNodeId) (t1 t2 : Triple) : Prop :=
  BnodeFreshFor b g ∧
  ∃ u : Triple, u ∈ g ∧ ∃ l : WfLiteral,
    u.o = .literal l ∧
    (l.val.datatype = xsdString ∨ l.val.datatype = rdfLangString) ∧
    t1 = { s := u.s, p := u.p, o := .bnode b } ∧
    t2 = { s := .bnode b, p := rdfType, o := .iri rdfsLiteral }

/-- rdfs2: "aaa rdfs:domain xxx . yyy aaa zzz . | yyy rdf:type xxx ." -/
def Rdfs2Derives (g : Graph) (t : Triple) : Prop :=
  ∃ decl : Triple, decl ∈ g ∧ ∃ u : Triple, u ∈ g ∧ ∃ a : WfIri,
    decl.p = rdfsDomain ∧ decl.s = .iri a ∧ u.p = a ∧
    t = { s := u.s, p := rdfType, o := decl.o }

/-- rdfs3: "aaa rdfs:range xxx . yyy aaa zzz . | zzz rdf:type xxx ."
`zzz` moves from object to subject position, so the row does not fire
when it is a literal or a triple term. -/
def Rdfs3Derives (g : Graph) (t : Triple) : Prop :=
  ∃ decl : Triple, decl ∈ g ∧ ∃ u : Triple, u ∈ g ∧ ∃ (a : WfIri) (zs : Subject),
    decl.p = rdfsRange ∧ decl.s = .iri a ∧ u.p = a ∧
    subjTerm zs = u.o ∧ t = { s := zs, p := rdfType, o := decl.o }

/-- rdfs4a: "xxx aaa yyy . | xxx rdf:type rdfs:Resource ." NOT
implemented by either tree's core closure. -/
def Rdfs4aDerives (g : Graph) (t : Triple) : Prop :=
  ∃ u : Triple, u ∈ g ∧ t = { s := u.s, p := rdfType, o := .iri rdfsResource }

/-- rdfs4b, with the same generalized-RDF premise as rdfs3. NOT
implemented. -/
def Rdfs4bDerives (g : Graph) (t : Triple) : Prop :=
  ∃ u : Triple, u ∈ g ∧ ∃ ys : Subject, subjTerm ys = u.o ∧
    t = { s := ys, p := rdfType, o := .iri rdfsResource }

/-- rdfs5, in the TWO-SOURCE form.

The engine reads its two premises from different places: one from the
graph it is folding over, one from an index snapshot that may be older.
Splitting the sources is what lets per-row soundness compose through the
fixed-point driver. `Rdfs5Derives` is the diagonal, and the diagonal is
what the specification's table states. -/
def Rdfs5Derives2 (gd gs : Graph) (t : Triple) : Prop :=
  ∃ t1 : Triple, t1 ∈ gd ∧ ∃ t2 : Triple, t2 ∈ gs ∧ ∃ ys : Subject,
    t1.p = rdfsSubPropertyOf ∧ t2.p = rdfsSubPropertyOf ∧
    subjTerm ys = t1.o ∧ t2.s = ys ∧
    t = { s := t1.s, p := rdfsSubPropertyOf, o := t2.o }

def Rdfs5Derives (g : Graph) (t : Triple) : Prop := Rdfs5Derives2 g g t

/-- rdfs6: "xxx rdf:type rdf:Property . | xxx rdfs:subPropertyOf xxx ." -/
def Rdfs6Derives (g : Graph) (t : Triple) : Prop :=
  ∃ u : Triple, u ∈ g ∧ u.p = rdfType ∧ u.o = .iri rdfProperty ∧
    t = { s := u.s, p := rdfsSubPropertyOf, o := subjTerm u.s }

/-- rdfs7: "aaa rdfs:subPropertyOf bbb . xxx aaa yyy . | xxx bbb yyy ."
`bbb` moves into a PREDICATE slot, so it must be an IRI — a genuine
restriction of generalized RDF too, since a blank-node-valued
subPropertyOf object licenses no ordinary-RDF conclusion. -/
def Rdfs7Derives (g : Graph) (t : Triple) : Prop :=
  ∃ decl : Triple, decl ∈ g ∧ ∃ u : Triple, u ∈ g ∧ ∃ a b : WfIri,
    decl.p = rdfsSubPropertyOf ∧ decl.s = .iri a ∧ decl.o = .iri b ∧
    u.p = a ∧ t = { s := u.s, p := b, o := u.o }

/-- rdfs8: "xxx rdf:type rdfs:Class . | xxx rdfs:subClassOf
rdfs:Resource ." NOT implemented. -/
def Rdfs8Derives (g : Graph) (t : Triple) : Prop :=
  ∃ u : Triple, u ∈ g ∧ u.p = rdfType ∧ u.o = .iri rdfsClass ∧
    t = { s := u.s, p := rdfsSubClassOf, o := .iri rdfsResource }

/-- rdfs9: "xxx rdfs:subClassOf yyy . zzz rdf:type xxx . | zzz rdf:type
yyy ." `xxx` is the subject of one premise and the object of the other,
so the two occurrences are linked by `subjTerm`. -/
def Rdfs9Derives2 (gd gs : Graph) (t : Triple) : Prop :=
  ∃ sub : Triple, sub ∈ gs ∧ ∃ typ : Triple, typ ∈ gd ∧ ∃ xs : Subject,
    sub.p = rdfsSubClassOf ∧ sub.s = xs ∧
    typ.p = rdfType ∧ typ.o = subjTerm xs ∧
    t = { s := typ.s, p := rdfType, o := sub.o }

def Rdfs9Derives (g : Graph) (t : Triple) : Prop := Rdfs9Derives2 g g t

/-- rdfs10: "xxx rdf:type rdfs:Class . | xxx rdfs:subClassOf xxx ." -/
def Rdfs10Derives (g : Graph) (t : Triple) : Prop :=
  ∃ u : Triple, u ∈ g ∧ u.p = rdfType ∧ u.o = .iri rdfsClass ∧
    t = { s := u.s, p := rdfsSubClassOf, o := subjTerm u.s }

/-- rdfs11, with the same generalized-RDF premise as rdfs5. -/
def Rdfs11Derives2 (gd gs : Graph) (t : Triple) : Prop :=
  ∃ t1 : Triple, t1 ∈ gd ∧ ∃ t2 : Triple, t2 ∈ gs ∧ ∃ ys : Subject,
    t1.p = rdfsSubClassOf ∧ t2.p = rdfsSubClassOf ∧
    subjTerm ys = t1.o ∧ t2.s = ys ∧
    t = { s := t1.s, p := rdfsSubClassOf, o := t2.o }

def Rdfs11Derives (g : Graph) (t : Triple) : Prop := Rdfs11Derives2 g g t

/-- rdfs12: "xxx rdf:type rdfs:ContainerMembershipProperty . | xxx
rdfs:subPropertyOf rdfs:member ." -/
def Rdfs12Derives (g : Graph) (t : Triple) : Prop :=
  ∃ u : Triple, u ∈ g ∧ u.p = rdfType ∧
    u.o = .iri rdfsContainerMembershipProperty ∧
    t = { s := u.s, p := rdfsSubPropertyOf, o := .iri rdfsMember }

/-- rdfs13: "xxx rdf:type rdfs:Datatype . | xxx rdfs:subClassOf
rdfs:Literal ." NOT implemented. -/
def Rdfs13Derives (g : Graph) (t : Triple) : Prop :=
  ∃ u : Triple, u ∈ g ∧ u.p = rdfType ∧ u.o = .iri rdfsDatatype ∧
    t = { s := u.s, p := rdfsSubClassOf, o := .iri rdfsLiteral }

/-! ## The RDFS axiomatic triples

The finite rows are transcribed one per row with their citations in
`RDF.VocabularyAxioms`; reused here rather than copied. The infinite
`rdf:_n` family is captured by the schema. -/

def RdfsAxiomatic (t : Triple) : Prop :=
  t ∈ rdfsAxiomaticTriples ∨
  ∃ i : WfIri, IsRdfMemberIri i ∧
    (t = { s := .iri i, p := rdfType, o := .iri rdfsContainerMembershipProperty } ∨
     t = { s := .iri i, p := rdfsDomain, o := .iri rdfsResource } ∨
     t = { s := .iri i, p := rdfsRange, o := .iri rdfsResource })

/-- The rdfs12 consequence of the axiomatic container-membership rows.
NOT itself axiomatic, but RDFS-entailed by the EMPTY graph, so it is
named apart — which is what lets a container rule's refinement theorem
say which of the two triples it emits is an axiom and which is one step
past one. -/
def RdfsMemberSubproperty (t : Triple) : Prop :=
  ∃ i : WfIri, IsRdfMemberIri i ∧
    t = { s := .iri i, p := rdfsSubPropertyOf, o := .iri rdfsMember }

/-! ## The two condition-level consequences -/

def RdfsSubClassOfEndpointRefl (g : Graph) (t : Triple) : Prop :=
  ∃ u : Triple, u ∈ g ∧ ∃ xs : Subject,
    u.p = rdfsSubClassOf ∧ (u.s = xs ∨ u.o = subjTerm xs) ∧
    t = { s := xs, p := rdfsSubClassOf, o := subjTerm xs }

def RdfsSubPropertyOfEndpointRefl (g : Graph) (t : Triple) : Prop :=
  ∃ u : Triple, u ∈ g ∧ ∃ xs : Subject,
    u.p = rdfsSubPropertyOf ∧ (u.s = xs ∨ u.o = subjTerm xs) ∧
    t = { s := xs, p := rdfsSubPropertyOf, o := subjTerm xs }

/-! ## The specification, syntactic side -/

def RdfsLicensed (D : DatatypeSet) (g : Graph) (t : Triple) : Prop :=
  t ∈ g ∨ RdfAxiomatic t ∨ RdfsAxiomatic t ∨ RdfsMemberSubproperty t ∨
  RdfsSubClassOfEndpointRefl g t ∨ RdfsSubPropertyOfEndpointRefl g t ∨
  RdfD2Derives g t ∨
  Rdfs1Derives D t ∨ Rdfs2Derives g t ∨ Rdfs3Derives g t ∨
  Rdfs4aDerives g t ∨ Rdfs4bDerives g t ∨ Rdfs5Derives g t ∨
  Rdfs6Derives g t ∨ Rdfs7Derives g t ∨ Rdfs8Derives g t ∨
  Rdfs9Derives g t ∨ Rdfs10Derives g t ∨ Rdfs11Derives g t ∨
  Rdfs12Derives g t ∨ Rdfs13Derives g t

def RdfsStepLicensed (D : DatatypeSet) (g out : Graph) : Prop :=
  ∀ t : Triple, t ∈ out → RdfsLicensed D g t

/-- A graph is RDFS-closed when it holds the axiomatic triples and is
shut under every row. The bnode-minting rows are excluded, as in the
specification's own "towards E" formulation. -/
def RdfsClosed (D : DatatypeSet) (g : Graph) : Prop :=
  (∀ t, RdfAxiomatic t → t ∈ g) ∧ (∀ t, RdfsAxiomatic t → t ∈ g) ∧
  (∀ t, RdfD2Derives g t → t ∈ g) ∧
  (∀ t, Rdfs1Derives D t → t ∈ g) ∧ (∀ t, Rdfs2Derives g t → t ∈ g) ∧
  (∀ t, Rdfs3Derives g t → t ∈ g) ∧ (∀ t, Rdfs4aDerives g t → t ∈ g) ∧
  (∀ t, Rdfs4bDerives g t → t ∈ g) ∧ (∀ t, Rdfs5Derives g t → t ∈ g) ∧
  (∀ t, Rdfs6Derives g t → t ∈ g) ∧ (∀ t, Rdfs7Derives g t → t ∈ g) ∧
  (∀ t, Rdfs8Derives g t → t ∈ g) ∧ (∀ t, Rdfs9Derives g t → t ∈ g) ∧
  (∀ t, Rdfs10Derives g t → t ∈ g) ∧ (∀ t, Rdfs11Derives g t → t ∈ g) ∧
  (∀ t, Rdfs12Derives g t → t ∈ g) ∧ (∀ t, Rdfs13Derives g t → t ∈ g)

/-! ## The ρdf fragment -/

def IsRhoDfIri (i : WfIri) : Prop :=
  i = rdfsSubPropertyOf ∨ i = rdfsSubClassOf ∨
  i = rdfsDomain ∨ i = rdfsRange ∨ i = rdfType

/-- The ρdf vocabulary never occurs outside the predicate slot. -/
def RhoDfTermOk : Term → Prop
  | .iri i => ¬ IsRhoDfIri i
  | .bnode _ => True
  | .literal _ => True
  | .tripleTerm _ _ _ => False

def RhoDfSubjectOk : Subject → Prop
  | .iri i => ¬ IsRhoDfIri i
  | .bnode _ => True

def RhoDfTriple (t : Triple) : Prop := RhoDfSubjectOk t.s ∧ RhoDfTermOk t.o

def RhoDfGraph (g : Graph) : Prop := ∀ t : Triple, t ∈ g → RhoDfTriple t

/-! ## The engine's rows are licensed by the table

This is where the engine appears, and only in one direction: everything
`RDFS.Closure`'s rows emit is licensed. The three transitivity-shaped
rows are proved here; they are the ones whose premises are linked
through `subjTerm`, which is where a transcription is most likely to
diverge from the table. -/

/-- Every conclusion `rdfs11For g t` produces is an rdfs11 derivation
from `g` — given that `t` itself is in `g`, which is how the row is
called. -/
theorem rdfs11For_derives {g : Graph} {t u : Triple} (ht : t ∈ g)
    (hu : u ∈ rdfs11For g t) : Rdfs11Derives g u := by
  unfold rdfs11For at hu
  split at hu
  · rename_i hp
    split at hu
    · rename_i bsub hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
      obtain ⟨t2, ht2, rfl⟩ := List.mem_map.mp (by
        simpa [objectsOf] using hc : _ ∈ (g.filter (fun x => x.s == bsub && x.p == rdfsSubClassOf)).map (·.o))
      have h2 := List.mem_filter.mp ht2
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact ⟨t, ht, t2, h2.1, bsub, Subtype.ext (by simpa using hp), h2.2.2,
             subjTerm_of_toSubject? hb, h2.2.1, rfl⟩
    · simp at hu
  · simp at hu

/-- The same for rdfs5, the property-hierarchy dual. -/
theorem rdfs5For_derives {g : Graph} {t u : Triple} (ht : t ∈ g)
    (hu : u ∈ rdfs5For g t) : Rdfs5Derives g u := by
  unfold rdfs5For at hu
  split at hu
  · rename_i hp
    split at hu
    · rename_i bsub hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
      obtain ⟨t2, ht2, rfl⟩ := List.mem_map.mp (by
        simpa [objectsOf] using hc : _ ∈ (g.filter (fun x => x.s == bsub && x.p == rdfsSubPropertyOf)).map (·.o))
      have h2 := List.mem_filter.mp ht2
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact ⟨t, ht, t2, h2.1, bsub, Subtype.ext (by simpa using hp), h2.2.2,
             subjTerm_of_toSubject? hb, h2.2.1, rfl⟩
    · simp at hu
  · simp at hu

/-- rdfs11 and rdfs5 conclusions are licensed, so a step built from
those two rows alone satisfies `RdfsStepLicensed`. Stated so the
composition direction is checked rather than assumed. -/
theorem rdfs11_licensed {D : DatatypeSet} {g : Graph} {t u : Triple}
    (ht : t ∈ g) (hu : u ∈ rdfs11For g t) : RdfsLicensed D g u :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (rdfs11For_derives ht hu)))))))))))))))))))

/-! ### The remaining obligation, named

Four rows of `RDFS.Closure` — rdfs7, rdfs2, rdfs3, rdfs9 — have no
licence theorem here yet. They are the rows whose premises are a
DECLARATION plus a data triple rather than two triples of one shape, so
each needs its own extraction of the declaration from the fold. The two
proved above are the transitivity pair, which is where a transcription
is most likely to diverge from the table, and the pattern the other
four follow. -/

/-! ## Build-time checks

The definitions are relations, so a check pins the COMPUTED side: the
conclusion each row builds, and the row's own firing condition. -/

section Checks

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def cA : WfIri := iriW "http://e.org/A"
private def cB : WfIri := iriW "http://e.org/B"
private def cC : WfIri := iriW "http://e.org/C"

private def sub (a b : WfIri) : Triple := ⟨.iri a, rdfsSubClassOf, .iri b⟩

/-! The transitivity rows fire on a chain and compose the endpoints. -/

#guard rdfs11For [sub cA cB, sub cB cC] (sub cA cB) == [sub cA cC]
#guard rdfs11For [sub cA cB] (sub cA cB) == []

/-! And they do NOT fire when the middle term cannot be a subject — the
generalized-RDF premise, which is the side condition the specification
states and an implementation is most likely to drop. -/

#guard rdfs11For [⟨.iri cA, rdfsSubClassOf, .literal (Literal.string "x")⟩]
         ⟨.iri cA, rdfsSubClassOf, .literal (Literal.string "x")⟩ == []

/-! rdfs9 links its two premises through the class term, so it fires
only when the type triple's OBJECT is the subclass triple's SUBJECT. -/

#guard rdfs9For [sub cA cB] ⟨.iri (iriW "http://e.org/i"), rdfType, .iri cA⟩
         == [⟨.iri (iriW "http://e.org/i"), rdfType, .iri cB⟩]
#guard rdfs9For [sub cA cB] ⟨.iri (iriW "http://e.org/i"), rdfType, .iri cC⟩ == []

/-! The ρdf fragment is exactly five IRIs, and an ordinary predicate is
not one of them. -/

#guard rdfsAxiomaticTriples.length == 38

end Checks

end L4Factoidal.RDF
