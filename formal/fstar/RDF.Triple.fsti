module RDF.Triple

// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.2/§3.3 step 5. One concept, one screen: what is a triple. A copy-
// move from RDF.Graph.Executable.fst (the `triple` record + `triple_eq`
// + their reflexivity lemma), no behavior change. Transparent `let`s/
// `type`s throughout, same discipline as RDF.Term.fsti/RDF.Vocabulary
// .fsti/RDF.Indexed.fsti — see RDF.Term.fsti's banner for why.
//
// Deliberately NOT here: `add_triple_if_new`/`add_triple_unchecked`
// and the rest of the graph-operation surface (`graph_add`,
// `mem_triple`, `rename_triple_bnodes`, …) — those stay in
// RDF.Graph.Executable.fst this slice, same narrower-than-original-
// plan scoping RDF.Term.fsti's banner explains.

open RDF.Term

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

/// Structural equality on triples: all three positions compare equal.
let triple_eq (a b : triple) : bool =
  subject_eq a.s b.s && a.p = b.p && rdf_term_eq a.o b.o

/// `triple_eq` is reflexive.
let lemma_triple_eq_refl (t : triple) : Lemma (triple_eq t t = true) =
  lemma_subject_eq_refl t.s;
  lemma_rdf_term_eq_refl t.o
