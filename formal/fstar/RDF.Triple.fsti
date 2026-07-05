module RDF.Triple

// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.2/§3.3 step 5. One concept, one screen: what is a triple. Full
// history + exclusion list in RDF.Triple.fst's banner. Transparent
// `let`s/`type`s throughout — see RDF.Term.fsti's banner for why.

open RDF.Term

(** ==================================================================== *)
(** Concepts — read top to bottom, uninterrupted, to the Appendix.       *)
(** ==================================================================== *)

(** ------------------------------------------------------------------ *)
(** Triples — RDF 1.1 Concepts §3.1                                    *)
(** ------------------------------------------------------------------ *)

/// A triple is a subject, a predicate, and an object — RDF 1.1's
/// smallest unit of assertion ("Bob knows Alice"). The predicate is
/// always an IRI (RDF 1.1 Concepts §3.1: "the predicate is an IRI");
/// the subject is restricted to `RDF.Term.subject` (IRI or blank
/// node, never a literal); the object is any `RDF.Term.rdf_term`.
noeq type triple = {
  s : subject;
  p : wf_iri;
  o : rdf_term;
}

(** ==================================================================== *)
(** Appendix: mechanical definitions (equality + reflexivity lemma).     *)
(** ==================================================================== *)

/// Structural equality on triples: all three positions compare equal.
let triple_eq (a b : triple) : bool =
  subject_eq a.s b.s && a.p = b.p && rdf_term_eq a.o b.o

/// `triple_eq` is reflexive.
let lemma_triple_eq_refl (t : triple) : Lemma (triple_eq t t = true) =
  lemma_subject_eq_refl t.s;
  lemma_rdf_term_eq_refl t.o
