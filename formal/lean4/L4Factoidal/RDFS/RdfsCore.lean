/-
L4Factoidal.RDFS.RdfsCore — the SPECIFICATION of the rdfs-core fragment:
the six RDFS entailment rows as an inductive derivation relation.

Ports the rule set of `formal/fstar/RDF.Entailment.RDFS.RhoDFClosure.fst`
(module banner, section 1) — the six rows that module runs, and only
those six:

    rdfs7  rdfs_rule_subPropertyOf
    rdfs2  rdfs_rule_domain
    rdfs3  rdfs_rule_range
    rdfs9  rdfs_rule_subClassOf
    rdfs11 rdfs_rule_subClassOf_trans
    rdfs5  rdfs_rule_subPropertyOf_trans

This is the reviewer-facing object: `Derives g t` says "t is derivable
from g by the rdfs-core rules", written the way the RDF 1.1 Semantics §9.2
rule table writes it — premises above the line, conclusion below —
with nothing about fuel, indexes, deduplication, or evaluation order.
`L4Factoidal/RDFS/Closure.lean` is the executable closure; the two are
tied together by the theorems in
`L4Factoidal/RDFS/ClosureTheorems.lean` (soundness: everything the
closure computes is derivable here; saturation-completeness: everything
derivable here is in a saturated closure).

WHAT IS NOT HERE. The rows RDF 1.1 Semantics §9.2 lists that the
rdfs-core fragment drops — rdfs1, rdfs4a, rdfs4b, rdfs6, rdfs8, rdfs10,
rdfs12, rdfs13 and the container-membership axioms — are absent by
design, not by oversight. Finding C-2 in the F* tree's
`RDF.Entailment.RDFS.Completeness.fst` is exactly that those rows rest
on interpretation conditions the rdfs-core model theory does not carry, so
the twelve-rule closure cannot instantiate the fragment's soundness
side. This module is the six-row operator that can.

The model theory itself (interpretations, `rho_df_conditions`,
`satisfies`, `rho_df_entails`) is NOT ported: the F* soundness theorem
`rho_df_closure_sound` is stated against interpretations, while the
Lean soundness theorem here is stated against this rule relation. The
two differ in strength — see the header of `ClosureTheorems.lean` for
what is and is not claimed.


Naming: this fragment is called ρdf ("rho-df") in the literature —
Muñoz, Pérez, Gutierrez, "Minimal deductive systems for RDF" (ESWC
2007) — and "core RDFS" / rdfs-core in this repository (owner
decision 2026-08-22: the Greek letter reads as "pdf" on a phone).
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## The derivation relation

`Derives g t` — "graph `g` rdfs-core-derives triple `t`". Membership of
the base case is LIST membership (`t ∈ g`), not the engine's
`Graph.mem`; the engine's `Triple.eqb` is coarser than equality on
literals (language-tag case folding, `rdf:XMLLiteral` canonicalisation),
and a specification relation should not inherit that. Where the coarse
comparison does appear — the executable closure's deduplication — the
theorems say so explicitly.

Each constructor is one row of the RDF 1.1 Semantics §9.2 table, with
the same premise/conclusion shape the F* `rdfs_rule_*` function
implements. Premises are themselves `Derives`, so the relation is the
closure of the one-step rules, i.e. "derivable in any number of steps",
which is what the fixpoint computes. -/

inductive Derives (g : Graph) : Triple → Prop where
  /-- Every triple of the graph is derivable from it (RDF 1.1
  Semantics: entailment extends the asserted graph). -/
  | base {t : Triple} (h : t ∈ g) : Derives g t
  /-- **rdfs2** — §9.2: `aaa rdfs:domain xxx . uuu aaa yyy .`
  entails `uuu rdf:type xxx .` The domain class `xxx` is any term
  (the F* `rdfs_rule_domain` keeps `decl.o` a raw `rdf_term`, not an
  IRI — this port keeps that). -/
  | rdfs2 {p : WfIri} {cls : Term} {s : Subject} {o : Term}
      (hdecl : Derives g ⟨Subject.iri p, rdfsDomain, cls⟩)
      (hdata : Derives g ⟨s, p, o⟩) :
      Derives g ⟨s, rdfType, cls⟩
  /-- **rdfs3** — §9.2: `aaa rdfs:range xxx . uuu aaa vvv .` entails
  `vvv rdf:type xxx .` The object `vvv` must be usable as a subject
  (an IRI or a blank node — a literal object licenses no conclusion),
  which is the F* `term_to_subject` guard. -/
  | rdfs3 {p : WfIri} {cls : Term} {s : Subject} {o : Term} {osub : Subject}
      (hdecl : Derives g ⟨Subject.iri p, rdfsRange, cls⟩)
      (hdata : Derives g ⟨s, p, o⟩)
      (hsub  : o.toSubject? = some osub) :
      Derives g ⟨osub, rdfType, cls⟩
  /-- **rdfs5** — §9.2: `aaa rdfs:subPropertyOf bbb .
  bbb rdfs:subPropertyOf ccc .` entails `aaa rdfs:subPropertyOf ccc .`
  (transitivity of the property hierarchy). -/
  | rdfs5 {a : Subject} {b : Term} {bsub : Subject} {c : Term}
      (h1   : Derives g ⟨a, rdfsSubPropertyOf, b⟩)
      (hsub : b.toSubject? = some bsub)
      (h2   : Derives g ⟨bsub, rdfsSubPropertyOf, c⟩) :
      Derives g ⟨a, rdfsSubPropertyOf, c⟩
  /-- **rdfs7** — §9.2: `aaa rdfs:subPropertyOf bbb . uuu aaa yyy .`
  entails `uuu bbb yyy .` Both property names must be IRIs (the
  conclusion's predicate slot admits nothing else). -/
  | rdfs7 {p q : WfIri} {s : Subject} {o : Term}
      (hdecl : Derives g ⟨Subject.iri p, rdfsSubPropertyOf, Term.iri q⟩)
      (hdata : Derives g ⟨s, p, o⟩) :
      Derives g ⟨s, q, o⟩
  /-- **rdfs9** — §9.2: `uuu rdfs:subClassOf xxx . vvv rdf:type uuu .`
  entails `vvv rdf:type xxx .` The sub-class `uuu` is read off a
  `rdf:type` object, so it is an IRI; the super-class term is
  unrestricted (matching `rdfs_rule_subClassOf`). -/
  | rdfs9 {s : Subject} {a : WfIri} {b : Term}
      (hdata : Derives g ⟨s, rdfType, Term.iri a⟩)
      (hdecl : Derives g ⟨Subject.iri a, rdfsSubClassOf, b⟩) :
      Derives g ⟨s, rdfType, b⟩
  /-- **rdfs11** — §9.2: `uuu rdfs:subClassOf vvv .
  vvv rdfs:subClassOf xxx .` entails `uuu rdfs:subClassOf xxx .`
  (transitivity of the class hierarchy). -/
  | rdfs11 {a : Subject} {b : Term} {bsub : Subject} {c : Term}
      (h1   : Derives g ⟨a, rdfsSubClassOf, b⟩)
      (hsub : b.toSubject? = some bsub)
      (h2   : Derives g ⟨bsub, rdfsSubClassOf, c⟩) :
      Derives g ⟨a, rdfsSubClassOf, c⟩

/-! ## Structural properties of the relation

Two facts the closure theorems need, both proved by induction on the
derivation and both independent of any implementation. -/

/-- Monotonicity: a bigger graph derives at least as much. (Every rule
is a Horn rule — no negation, no counting — so nothing is lost when the
premise set grows.) -/
theorem Derives.mono {g g' : Graph} (hsub : ∀ u, u ∈ g → u ∈ g')
    {t : Triple} (h : Derives g t) : Derives g' t := by
  induction h with
  | base hm => exact Derives.base (hsub _ hm)
  | rdfs2 _ _ ih1 ih2 => exact Derives.rdfs2 ih1 ih2
  | rdfs3 _ _ hs ih1 ih2 => exact Derives.rdfs3 ih1 ih2 hs
  | rdfs5 _ hs _ ih1 ih2 => exact Derives.rdfs5 ih1 hs ih2
  | rdfs7 _ _ ih1 ih2 => exact Derives.rdfs7 ih1 ih2
  | rdfs9 _ _ ih1 ih2 => exact Derives.rdfs9 ih1 ih2
  | rdfs11 _ hs _ ih1 ih2 => exact Derives.rdfs11 ih1 hs ih2

/-- Cut: if every triple of `g'` is derivable from `g`, then everything
derivable from `g'` is derivable from `g`. This is what makes the
iterated closure sound — each round's output is derivable from the
round's input, and cut chains the rounds. -/
theorem Derives.cut {g g' : Graph} (hall : ∀ u, u ∈ g' → Derives g u)
    {t : Triple} (h : Derives g' t) : Derives g t := by
  induction h with
  | base hm => exact hall _ hm
  | rdfs2 _ _ ih1 ih2 => exact Derives.rdfs2 ih1 ih2
  | rdfs3 _ _ hs ih1 ih2 => exact Derives.rdfs3 ih1 ih2 hs
  | rdfs5 _ hs _ ih1 ih2 => exact Derives.rdfs5 ih1 hs ih2
  | rdfs7 _ _ ih1 ih2 => exact Derives.rdfs7 ih1 ih2
  | rdfs9 _ _ ih1 ih2 => exact Derives.rdfs9 ih1 ih2
  | rdfs11 _ hs _ ih1 ih2 => exact Derives.rdfs11 ih1 hs ih2

end L4Factoidal.RDFS
