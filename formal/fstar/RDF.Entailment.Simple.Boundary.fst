module RDF.Entailment.Simple.Boundary

// ===================================================================
// THE PARSER-TO-ABSTRACT-GRAPH BOUNDARY for simple entailment
// (issue #318 deliverable 4).
//
// -------------------------------------------------------------------
// WHAT IS AND IS NOT CLAIMED -- read this before citing the module
// -------------------------------------------------------------------
// NOT claimed: that `Parser.NTriples.parse_ntriples_strict` implements
// the N-Triples grammar. That would need a declarative grammar
// semantics (a relation "document D denotes graph G" transcribed from
// the N-Triples Recommendation) and a proof that the parser computes
// it. No such semantics exists in this tree; writing one is separate,
// larger work. Nothing here substitutes for it.
//
// Claimed, in two parts:
//
//   (1) COMPOSITION. `entails_ntriples_documents` is the whole
//       document-in / verdict-out path for simple entailment; the
//       refinement result carries through it unchanged
//       (`entails_ntriples_boundary`). This says exactly: whatever the
//       parser's abstract graphs are, the verdict on them is the
//       declarative simple-entailment relation. It isolates the
//       parser as the ONLY remaining unproven link.
//
//   (2) LABEL INDEPENDENCE -- the part with mathematical content. A
//       parser's abstract graph is only determined up to its choice of
//       blank-node labels: `_:b0` in a document and `_:genid1` from a
//       generated-label path are the same graph, and RDF 1.1 Concepts
//       section 3.4 says so ("blank node identifiers are local to a
//       concrete syntax or implementation"). If the entailment verdict
//       could depend on those labels, no theorem about abstract graphs
//       would transfer to documents. `simple_entails_rename_invariant`
//       proves it cannot: relabelling B's blank nodes by any injective
//       renaming leaves the shipping engine's verdict unchanged.
//       Injectivity is required and is not decoration -- a
//       non-injective relabelling MERGES blank nodes and can only make
//       the pattern harder to satisfy, which is the one-directional
//       `spec_rename_specialises` below.
//
// Both parts inherit the `graph_exact` side condition of
// `simple_entails_sound` (finding SE-1) wherever they need soundness.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph.Executable
open Parser.NTriples
open RDF.Entailment.Simple
open RDF.Entailment.Simple.Spec
open RDF.Entailment.Simple.Refinement

// ===================================================================
// 1. Blank-node relabelling.
// ===================================================================

// A relabelling with a recorded left inverse -- i.e. an injective map
// on blank-node labels. Carrying the inverse rather than an
// injectivity hypothesis keeps the construction of the transported
// substitution explicit (and avoids needing choice to invert).
noeq type relabelling = {
  rl_fwd : bnode_id -> bnode_id;
  rl_bwd : bnode_id -> bnode_id;
  rl_inv : squash (forall (l : bnode_id). rl_bwd (rl_fwd l) == l);
}

let rename_subject (f : bnode_id -> bnode_id) (s : subject) : subject =
  match s with
  | S_IRI i   -> S_IRI i
  | S_BNode b -> S_BNode (f b)

let rec rename_term (f : bnode_id -> bnode_id) (t : rdf_term)
  : Tot rdf_term (decreases t) =
  match t with
  | T_IRI i     -> T_IRI i
  | T_BNode b   -> T_BNode (f b)
  | T_Literal l -> T_Literal l
  | T_TripleTerm s p o -> T_TripleTerm (rename_subject f s) p (rename_term f o)

let rename_triple (f : bnode_id -> bnode_id) (t : triple) : triple =
  { s = rename_subject f t.s; p = t.p; o = rename_term f t.o }

let rename_graph (f : bnode_id -> bnode_id) (g : list triple) : list triple =
  map (rename_triple f) g

// Relabelling touches blank nodes only, so it preserves the
// exact-literal fragment in both directions.
let rec lemma_rename_term_exact (f : bnode_id -> bnode_id) (t : rdf_term)
  : Lemma (ensures term_exact (rename_term f t) <==> term_exact t) (decreases t) =
  match t with
  | T_IRI _ | T_BNode _ | T_Literal _ -> ()
  | T_TripleTerm _ _ o -> lemma_rename_term_exact f o

let rec lemma_rename_graph_exact (f : bnode_id -> bnode_id) (g : list triple)
  : Lemma (requires graph_exact g) (ensures graph_exact (rename_graph f g))
          (decreases g) =
  match g with
  | [] -> ()
  | t :: rest ->
    lemma_rename_term_exact f t.o;
    lemma_rename_graph_exact f rest

// ===================================================================
// 2. Substitution composition: renaming a pattern is the same as
// pre-composing the substitution. No injectivity needed -- this is a
// plain equation, and it is what both directions of the theorem run
// on.
// ===================================================================

let lemma_rename_subj_inst (f : bnode_id -> bnode_id) (m : bnode_subst)
                           (ps : subject) (gs : subject)
  : Lemma (subj_inst (fun l -> m (f l)) ps gs <==>
           subj_inst m (rename_subject f ps) gs) =
  match ps with
  | S_IRI _ -> ()
  | S_BNode _ -> ()

let rec lemma_rename_term_inst (f : bnode_id -> bnode_id) (m : bnode_subst)
                               (pat : rdf_term) (g : rdf_term)
  : Lemma (ensures term_inst (fun l -> m (f l)) pat g <==>
                   term_inst m (rename_term f pat) g)
          (decreases pat) =
  match pat with
  | T_IRI _ | T_BNode _ | T_Literal _ -> ()
  | T_TripleTerm ps pp po ->
    let aux (gs : subject) (go : rdf_term)
      : Lemma ((subj_inst (fun l -> m (f l)) ps gs /\ term_inst (fun l -> m (f l)) po go)
               <==>
               (subj_inst m (rename_subject f ps) gs /\ term_inst m (rename_term f po) go)) =
      lemma_rename_subj_inst f m ps gs;
      lemma_rename_term_inst f m po go
    in
    FStar.Classical.forall_intro_2 aux

let lemma_rename_triple_inst (f : bnode_id -> bnode_id) (m : bnode_subst)
                             (tb : triple) (ta : triple)
  : Lemma (triple_inst (fun l -> m (f l)) tb ta <==>
           triple_inst m (rename_triple f tb) ta) =
  lemma_rename_subj_inst f m tb.s ta.s;
  lemma_rename_term_inst f m tb.o ta.o

// Pointwise-equal substitutions relate the same pairs. (F* arrows are
// not extensional, so the composition equation
// `(M o rl_bwd) o rl_fwd = M` has to be transported pointwise rather
// than as a function equality.)
let lemma_subst_ext_subj (m1 m2 : bnode_subst) (ps : subject) (gs : subject)
  : Lemma (requires forall (l : bnode_id). m1 l == m2 l)
          (ensures subj_inst m1 ps gs <==> subj_inst m2 ps gs) =
  match ps with
  | S_IRI _ -> ()
  | S_BNode _ -> ()

let rec lemma_subst_ext_term (m1 m2 : bnode_subst) (pat : rdf_term) (g : rdf_term)
  : Lemma (requires forall (l : bnode_id). m1 l == m2 l)
          (ensures term_inst m1 pat g <==> term_inst m2 pat g)
          (decreases pat) =
  match pat with
  | T_IRI _ | T_BNode _ | T_Literal _ -> ()
  | T_TripleTerm ps pp po ->
    let aux (gs : subject) (go : rdf_term)
      : Lemma ((subj_inst m1 ps gs /\ term_inst m1 po go) <==>
               (subj_inst m2 ps gs /\ term_inst m2 po go)) =
      lemma_subst_ext_subj m1 m2 ps gs;
      lemma_subst_ext_term m1 m2 po go
    in
    FStar.Classical.forall_intro_2 aux

let lemma_subst_ext_triple (m1 m2 : bnode_subst) (tb : triple) (ta : triple)
  : Lemma (requires forall (l : bnode_id). m1 l == m2 l)
          (ensures triple_inst m1 tb ta <==> triple_inst m2 tb ta) =
  lemma_subst_ext_subj m1 m2 tb.s ta.s;
  lemma_subst_ext_term m1 m2 tb.o ta.o

// memP through `map`, both ways, spelled out because the two
// directions are used separately below.
let rec lemma_memP_rename_intro (f : bnode_id -> bnode_id) (g : list triple) (t : triple)
  : Lemma (requires memP t g) (ensures memP (rename_triple f t) (rename_graph f g))
          (decreases g) =
  match g with
  | [] -> ()
  | h :: rest -> if FStar.StrongExcludedMiddle.strong_excluded_middle (t == h)
                then () else lemma_memP_rename_intro f rest t

let rec lemma_memP_rename_elim (f : bnode_id -> bnode_id) (g : list triple) (t' : triple)
  : Lemma (requires memP t' (rename_graph f g))
          (ensures  exists (t : triple). memP t g /\ t' == rename_triple f t)
          (decreases g) =
  match g with
  | [] -> ()
  | h :: rest ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (t' == rename_triple f h)
    then assert (memP h g)
    else lemma_memP_rename_elim f rest t'

// ===================================================================
// 3. Relabelling and the specification.
// ===================================================================

// Relabelling B by ANY map can only specialise the pattern: a
// non-injective map merges blank nodes, and a merged pattern is
// harder to satisfy. So this direction needs no inverse.
let spec_rename_specialises (f : bnode_id -> bnode_id) (a b : list triple)
  : Lemma (requires simple_entailment_spec a (rename_graph f b))
          (ensures  simple_entailment_spec a b) =
  eliminate exists (m : bnode_subst).
      (forall (tb : triple). memP tb (rename_graph f b) ==>
         (exists (ta : triple). memP ta a /\ triple_inst m tb ta))
  returns (simple_entailment_spec a b)
  with _pm.
    (let m0 : bnode_subst = fun l -> m (f l) in
     let per_triple (tb : triple)
       : Lemma (requires memP tb b)
               (ensures (exists (ta : triple). memP ta a /\ triple_inst m0 tb ta)) =
       lemma_memP_rename_intro f b tb;
       eliminate exists (ta : triple). memP ta a /\ triple_inst m (rename_triple f tb) ta
       returns (exists (ta : triple). memP ta a /\ triple_inst m0 tb ta)
       with _pt.
         (lemma_rename_triple_inst f m tb ta;
          assert (memP ta a /\ triple_inst m0 tb ta))
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires per_triple);
     introduce exists (mm : bnode_subst).
         (forall (tb : triple). memP tb b ==>
            (exists (ta : triple). memP ta a /\ triple_inst mm tb ta))
     with m0
     and ())

// The converse needs injectivity, supplied by the recorded inverse:
// the transported substitution is M composed with the inverse, and
// (M o rl_bwd) o rl_fwd = M is exactly the left-inverse equation.
let spec_rename_generalises (r : relabelling) (a b : list triple)
  : Lemma (requires simple_entailment_spec a b)
          (ensures  simple_entailment_spec a (rename_graph r.rl_fwd b)) =
  eliminate exists (m : bnode_subst).
      (forall (tb : triple). memP tb b ==>
         (exists (ta : triple). memP ta a /\ triple_inst m tb ta))
  returns (simple_entailment_spec a (rename_graph r.rl_fwd b))
  with _pm.
    (let m1 : bnode_subst = fun l -> m (r.rl_bwd l) in
     assert (forall (l : bnode_id). m1 (r.rl_fwd l) == m l);
     let per_triple (tb' : triple)
       : Lemma (requires memP tb' (rename_graph r.rl_fwd b))
               (ensures (exists (ta : triple). memP ta a /\ triple_inst m1 tb' ta)) =
       lemma_memP_rename_elim r.rl_fwd b tb';
       eliminate exists (tb : triple). memP tb b /\ tb' == rename_triple r.rl_fwd tb
       returns (exists (ta : triple). memP ta a /\ triple_inst m1 tb' ta)
       with _pe.
         (eliminate exists (ta : triple). memP ta a /\ triple_inst m tb ta
          returns (exists (ta : triple). memP ta a /\ triple_inst m1 tb' ta)
          with _pt.
            (lemma_subst_ext_triple m (fun l -> m1 (r.rl_fwd l)) tb ta;
             lemma_rename_triple_inst r.rl_fwd m1 tb ta;
             assert (triple_inst m1 (rename_triple r.rl_fwd tb) ta);
             assert (memP ta a /\ triple_inst m1 tb' ta)))
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires per_triple);
     introduce exists (mm : bnode_subst).
         (forall (tb : triple). memP tb (rename_graph r.rl_fwd b) ==>
            (exists (ta : triple). memP ta a /\ triple_inst mm tb ta))
     with m1
     and ())

// ===================================================================
// THEOREM (label independence, at the SHIPPING function). Relabelling
// the entailed graph's blank nodes by an injective map does not change
// the verdict `simple_entails` returns.
//
// This is what licenses reading a theorem about abstract graphs as a
// statement about documents: the parser's blank-node label choice is
// arbitrary, and the verdict does not see it.
// ===================================================================
let simple_entails_rename_invariant (r : relabelling) (a b : list triple)
  : Lemma (requires graph_exact a /\ graph_exact b)
          (ensures  simple_entails a b == simple_entails a (rename_graph r.rl_fwd b)) =
  lemma_rename_graph_exact r.rl_fwd b;
  FStar.Classical.move_requires_2
    (fun (x : list triple) (y : list triple) -> simple_entails_sound x y) a b;
  FStar.Classical.move_requires_2
    (fun (x : list triple) (y : list triple) -> simple_entails_sound x y)
    a (rename_graph r.rl_fwd b);
  FStar.Classical.move_requires_2
    (fun (x : list triple) (y : list triple) -> simple_entails_complete x y) a b;
  FStar.Classical.move_requires_2
    (fun (x : list triple) (y : list triple) -> simple_entails_complete x y)
    a (rename_graph r.rl_fwd b);
  FStar.Classical.move_requires_2
    (fun (x : list triple) (y : list triple) -> spec_rename_generalises r x y) a b;
  FStar.Classical.move_requires_2
    (fun (x : list triple) (y : list triple) -> spec_rename_specialises r.rl_fwd x y) a b

// ===================================================================
// 4. The document boundary.
//
// `entails_ntriples_documents` is the whole path: two N-Triples
// documents in, a simple-entailment verdict out, using the shipping
// strict parser and the shipping search. `None` means a document did
// not parse.
// ===================================================================

let entails_ntriples_documents (doc_a doc_b : string) : option bool =
  match parse_ntriples_strict doc_a, parse_ntriples_strict doc_b with
  | Some ga, Some gb -> Some (simple_entails ga gb)
  | _, _             -> None

// THEOREM (boundary composition). On the exact-literal fragment, the
// document-level verdict is the declarative simple-entailment relation
// on whatever abstract graphs the parser produced. The parser is
// therefore the only unproven link in the chain, and it is named.
let entails_ntriples_boundary (doc_a doc_b : string) (ga gb : list triple)
  : Lemma (requires parse_ntriples_strict doc_a == Some ga /\
                    parse_ntriples_strict doc_b == Some gb /\
                    graph_exact ga /\ graph_exact gb)
          (ensures  (entails_ntriples_documents doc_a doc_b == Some true) <==>
                    simple_entailment_spec ga gb) =
  simple_entails_iff_spec ga gb

// FINDING SE-2 (recorded here because this is where it bites): the
// `graph_exact` hypothesis above is REACHABLE from concrete syntax.
// `parse_ntriples_strict` copies a literal's language tag out of the
// document verbatim -- it does not lowercase it -- and copies the
// datatype IRI verbatim, so a document may legally produce a literal
// with an uppercase language tag or an rdf:XMLLiteral datatype, and
// then finding SE-1's divergence is live. RDF 1.1 Concepts section 3.3
// explicitly PERMITS the parser to normalize ("Lexical representations
// of language tags MAY be converted to lower case"), and RDF 2004
// Concepts section 6.5 REQUIRED it ("normalized to lowercase"). Doing
// it at parse time would discharge half of `graph_exact` for every
// parsed graph. See the design doc for the two fix options and why
// this session did not take either (behaviour change to the shipping
// parser, outside this issue's scope).
