module RDF.Entailment.RDFS.Completeness

// ===================================================================
// COMPLETENESS at the RDFS rung, on the rho-df fragment.
// G3 milestone M1 / coverage gap 1
// (docs/claude-rules/rdf-rdfs-semantics-coverage.md).
//
// RDF.Entailment.RDFS.ModelTheory.fst proves SOUNDNESS: everything the
// rule tables license from a true graph is true, and the shipping
// closure is therefore RDFS-entailed by its input. This module proves
// the CONVERSE half on a named fragment: on a rho-df-closed graph,
// rho-df ENTAILMENT and SIMPLE ENTAILMENT coincide. The canonical
// model is the Herbrand interpretation of the closed graph, reused
// verbatim from the simple rung
// (RDF.Entailment.Simple.ModelTheory.herbrand), and SATURATION is what
// makes it a rho-df interpretation: each semantic condition's
// obligation is discharged because the corresponding rule has already
// fired.
//
// -------------------------------------------------------------------
// FINDING C-1. The gap-1 statement as written in the coverage doc,
//
//     rdfs_entails d_minimal g e  <==>  the RDFS closure of g simply
//                                       entails e,   for rho_df_graph
//                                       g and e
//
// is FALSE, and no fragment predicate on g and e repairs it. Two
// independent witnesses, both inside `rho_df_graph`:
//
//   W1 (reflexivity). g = [ X rdfs:subClassOf Y ], e = [ X
//      rdfs:subClassOf X ]. `cond_subClassOf_ic` puts X in IC and
//      `cond_subClassOf_refl` then makes the self-loop true in every
//      RDFS interpretation, so `rdfs_entails d_minimal g e` HOLDS. The
//      shipping `rdfs_closure` does not derive it (the reflexivity
//      harvest is a separate, regime-scoped second pass -- finding
//      RS-1), so the right-hand side fails. Machine-checked below as
//      `rdfs_entails_subclass_selfloop` (the entailment) together with
//      `rho_df_not_entails_subclass_selfloop` (the same pair is NOT
//      rho-df-entailed, by the Herbrand countermodel) -- i.e. the two
//      entailment relations genuinely differ ON the fragment.
//
//   W2 (universality of rdfs:Resource). `cond_resource` reads
//      ICEXT(I(rdfs:Resource)) = IR, so `e = [ Z rdf:type
//      rdfs:Resource ]` is RDFS-entailed by EVERY graph, for every IRI
//      Z -- including IRIs that occur nowhere in g. The shipping
//      rdfs4a/rdfs4b rows only emit Resource triples for terms that
//      DO occur, so the right-hand side fails again. This one is not a
//      missing rule: no finite graph can list the conclusion for every
//      IRI. It is a structural obstruction to an iff stated over the
//      full `rdfs_conditions` bundle.
//
// The repair is the one the published rho-df result already makes
// (Munoz, Perez, Gutierrez, "Minimal Deductive Systems for RDF", ESWC
// 2007 / JWS 7(3) 2009): restrict the INTERPRETATION CLASS as well as
// the graph. `rho_df_conditions` below keeps exactly the six semantic
// conditions the six rho-df rows rest on and drops the reflexivity,
// IC/IP-membership, resource-universality, datatype and axiomatic-
// triple conditions. That is the choice made here, and it is stated
// rather than hidden: the theorem is about rho-df entailment, NOT
// about `rdfs_entails`. `lemma_rho_df_entails_implies_rdfs` pins the
// direction of the inclusion in machine-checked form -- rho-df
// entailment is STRICTLY STRONGER than RDFS entailment (fewer
// conditions, more interpretations, harder to entail), and W1 above is
// the witness that the inclusion is strict on the fragment.
//
// -------------------------------------------------------------------
// FINDING C-2. Under the reduced class, the SHIPPING twelve-rule
// `rdfs_closure_step` is NOT rho-df-sound: it also runs rdfs1, rdfs4a,
// rdfs4b, rdfs8, rdfs13 and the container-membership row, whose
// conclusions (`... rdf:type rdfs:Resource`, `... rdfs:subClassOf
// rdfs:Literal`, ...) need `cond_resource`, `cond_datatypes_minimal`,
// `cond_class_subclass_resource`, `cond_datatype_subclass_literal`,
// `cond_cmp_member` and `cond_rdfs_axioms` -- none of which is in
// `rho_df_conditions`. So the end-to-end iff cannot be instantiated at
// `rdfs_closure` in the SOUNDNESS direction; it needs a six-rule
// rho-df closure operator, which this tree does not yet expose as a
// function. What IS delivered for the shipping closure is the
// COMPLETENESS direction (`rdfs_closure_rho_df_complete`), which is
// precisely the half that was missing, plus the fully general
// `rho_df_saturation_iff` -- "any sound, extensive, rho-df-closed
// saturation of g decides rho-df entailment of fragment graphs by
// simple entailment" -- which the future rho-df closure operator
// instantiates without further proof.
//
// -------------------------------------------------------------------
// THE FRAGMENT, and why each clause is load-bearing.
//
// `rho_df_frag_graph` (below) asks two things of every triple:
//
//   F1. the OBJECT is an IRI or a blank node -- no literal, no RDF 1.2
//       triple term. Triple-term freedom is the standing quarantine
//       (`graph_tt_free`, Q2 precedent). LITERAL freedom is the
//       generalized-RDF delta D5 biting the canonical model: with
//       `p rdfs:range c` and `a p "lit"` in the graph, `cond_range`
//       demands ICEXT membership FOR THE LITERAL, and rdfs3 cannot
//       conclude `"lit" rdf:type c` because `RDF.Term.subject` has no
//       literal case. The entailment is real and this tree's term
//       algebra cannot express it, so the fragment excludes the
//       premise. Recorded as a genuine restriction, not a formality.
//
//   F2. the object of an `rdfs:subPropertyOf` triple is an IRI. The
//       same D5 pressure one slot over: `cond_subPropertyOf` demands
//       IEXT(y) contain IEXT(x) for the OBJECT y of a subPropertyOf
//       triple, and rdfs7 can only move a conclusion into a predicate
//       slot when that object is an IRI. With `p rdfs:subPropertyOf
//       _:b` in the graph the canonical model falsifies the condition.
//
// The fragment does NOT include the "rho-df vocabulary occurs only in
// predicate position" clause of `RDF.Entailment.RDFS.Spec.rho_df_graph`
// -- the canonical-model proof never needs it, so requiring it would
// weaken the theorem for nothing. The two predicates are therefore
// INCOMPARABLE, deliberately; `rho_df_frag_graph` is what the proof
// pays for.
//
// The entailed graph `e` carries only `graph_tt_free` -- weaker still,
// since reflection out of the Herbrand model needs no more than that.
//
// -------------------------------------------------------------------
// HYPOTHESES CARRIED, not discharged (M2's job).
//
// `rho_df_closed` is a HYPOTHESIS of every theorem below. Discharging
// it for `rdfs_closure g fuel` needs the fixed-point machinery of
// RDF.Entailment.RDFS.FixedPoint (`step_saturated`,
// `lemma_saturated_stable`) plus per-row `_complete` lemmas for the
// six index-driven rows, which do not exist yet (only the five RS-2
// rows have them). `lemma_len_eq_saturated`'s own `no_dup_keys` /
// `no_repeats_p` hypotheses (FixedPoint Gap A/B) sit under that. This
// module does not attempt any of it and does not block on it: the
// completeness content is entirely above that line.
//
// Likewise `is_subgraph g (rdfs_closure g fuel)` is a hypothesis --
// `FixedPoint.lemma_step_extensive` gives it for ONE step under
// `no_dup_keys`, and the iterated form is M2's.
//
// Verify-only module; nothing here extracts.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDFS.Closure
open OWL.Semantics
open RDF.Vocabulary.Axioms
open RDF.Entailment.Simple.Spec
open RDF.Entailment.Simple.ModelTheory
open RDF.Entailment.RDF.Spec
open RDF.Entailment.RDFS.Spec
open RDF.Entailment.RDFS.Refinement
open RDF.Entailment.RDFS.ModelTheory

// ===================================================================
// 1. THE FRAGMENT.
// ===================================================================

let rho_df_object_ok (t : rdf_term) : prop =
  match t with
  | T_IRI _            -> True
  | T_BNode _          -> True
  | T_Literal _        -> False
  | T_TripleTerm _ _ _ -> False

let rho_df_frag_triple (t : triple) : prop =
  rho_df_object_ok t.o /\
  (t.p == i_rdfs_subPropertyOf ==> T_IRI? t.o)

let rho_df_frag_graph (g : list triple) : prop =
  forall (t : triple). memP t g ==> rho_df_frag_triple t

// F1 implies the standing RDF 1.2 quarantine predicate, so the
// Herbrand lemmas of the simple rung apply unchanged.
let lemma_object_ok_tt_free (t : rdf_term)
  : Lemma (requires rho_df_object_ok t) (ensures term_tt_free t) =
  match t with
  | T_IRI _            -> ()
  | T_BNode _          -> ()
  | T_Literal _        -> ()
  | T_TripleTerm _ _ _ -> ()

let lemma_frag_tt_free (g : list triple)
  : Lemma (requires rho_df_frag_graph g) (ensures graph_tt_free g) =
  let per_triple (t : triple)
    : Lemma (requires memP t g) (ensures term_tt_free t.o) =
    lemma_object_ok_tt_free t.o
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires per_triple)

// F1 also makes every object subject-eligible, which is what rdfs3
// needs to fire (the generalized-RDF premise of the Spec module).
let lemma_object_to_subject (t : rdf_term)
  : Lemma (requires rho_df_object_ok t)
          (ensures  exists (s : subject). subj_term s == t) =
  match t with
  | T_IRI i   -> introduce exists (s : subject). subj_term s == t with (S_IRI i) and ()
  | T_BNode b -> introduce exists (s : subject). subj_term s == t with (S_BNode b) and ()
  | T_Literal _        -> ()
  | T_TripleTerm _ _ _ -> ()

// A subject whose term view is an IRI IS that IRI as a subject.
let lemma_subj_term_iri (s : subject) (i : wf_iri)
  : Lemma (requires subj_term s == T_IRI i) (ensures s == S_IRI i) =
  match s with
  | S_IRI _   -> ()
  | S_BNode _ -> ()

// ===================================================================
// 2. THE rho-df INTERPRETATION CLASS.
//
// Exactly the six semantic conditions the six rho-df rows rest on,
// each reused verbatim from RDF.Entailment.RDFS.ModelTheory (which
// quotes the RDF 1.1 Semantics section 9 text at each definition):
//
//   cond_domain               <-> rdfs2
//   cond_range                <-> rdfs3
//   cond_subPropertyOf        <-> rdfs7
//   cond_subPropertyOf_trans  <-> rdfs5
//   cond_subClassOf           <-> rdfs9
//   cond_subClassOf_trans     <-> rdfs11
//
// DROPPED, deliberately, with the reason in each case:
//   cond_subClassOf_refl / cond_subPropertyOf_refl / cond_subClassOf_ic
//   / cond_subPropertyOf_ip  -- finding C-1 witness W1;
//   cond_resource            -- finding C-1 witness W2;
//   cond_rdf_axioms / cond_rdfs_axioms -- the axiomatic tables are not
//     seeded by the shipping closure, and the RDFS domain/range
//     declarations they carry would force type assertions the closure
//     never derives;
//   cond_datatypes / cond_datatypes_minimal / cond_class_subclass_
//   resource / cond_datatype_subclass_literal / cond_cmp_member /
//   cond_rdf_property -- vocabulary outside rho-df.
// ===================================================================

let rho_df_conditions (i : interp) : prop =
  cond_domain i /\ cond_range i /\
  cond_subPropertyOf i /\ cond_subPropertyOf_trans i /\
  cond_subClassOf i /\ cond_subClassOf_trans i

let rho_df_entails (g1 g2 : rdf_graph) : prop = entails_under rho_df_conditions g1 g2

// The inclusion, machine-checked: every RDFS interpretation is a
// rho-df interpretation, so rho-df entailment is the STRONGER
// relation. (Finding C-1: strictly stronger, on the fragment.)
let lemma_rdfs_conditions_imply_rho_df (dd : datatype_set) (i : interp)
  : Lemma (requires rdfs_conditions dd i) (ensures rho_df_conditions i) = ()

let lemma_rho_df_entails_implies_rdfs (dd : datatype_set) (g e : rdf_graph)
  : Lemma (requires rho_df_entails g e) (ensures rdfs_entails dd g e) =
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (lemma_rdfs_conditions_imply_rho_df dd))

// ===================================================================
// 3. rho-df CLOSEDNESS.
//
// The six rows of the rho-df deductive system, at the DIAGONAL (both
// premises read from the same graph) -- the form the W3C table states
// and the form a saturated graph satisfies.
// ===================================================================

let rho_df_closed (c : list triple) : prop =
  (forall (t : triple). rdfs2_derives  c t ==> memP t c) /\
  (forall (t : triple). rdfs3_derives  c t ==> memP t c) /\
  (forall (t : triple). rdfs5_derives  c t ==> memP t c) /\
  (forall (t : triple). rdfs7_derives  c t ==> memP t c) /\
  (forall (t : triple). rdfs9_derives  c t ==> memP t c) /\
  (forall (t : triple). rdfs11_derives c t ==> memP t c)

// ===================================================================
// 4. THE CANONICAL MODEL IS A rho-df INTERPRETATION.
//
// One lemma per condition. Each has the same three-move shape:
//   (a) read the two Herbrand premises back as triples of `c`;
//   (b) exhibit the rho-df rule instance whose conclusion is wanted;
//   (c) `rho_df_closed c` puts that conclusion in `c`, which is
//       exactly the Herbrand fact the condition asks for.
// Move (c) is where SATURATION does the work.
// ===================================================================

#push-options "--z3rlimit 60"
let step_domain (c : list triple) (p cc x y : rdf_term)
  : Lemma (requires rho_df_closed c /\
                    herb_iext c (T_IRI rdfs_domain) p cc /\
                    herb_iext c p x y)
          (ensures  herb_iext c (T_IRI rdf_type) x cc) =
  lemma_vocab_agree ();
  eliminate exists (decl : triple).
      memP decl c /\ T_IRI rdfs_domain == T_IRI decl.p /\
      p == subj_term decl.s /\ cc == decl.o
  returns herb_iext c (T_IRI rdf_type) x cc
  with _ .
    (eliminate exists (u : triple).
        memP u c /\ p == T_IRI u.p /\ x == subj_term u.s /\ y == u.o
     returns herb_iext c (T_IRI rdf_type) x cc
     with _ . begin
       lemma_subj_term_iri decl.s u.p;
       let concl : triple = { s = u.s; p = i_rdf_type; o = decl.o } in
       introduce exists (d2 u2 : triple) (aa : wf_iri).
           memP d2 c /\ d2.p == i_rdfs_domain /\ d2.s == S_IRI aa /\
           memP u2 c /\ u2.p == aa /\
           concl == ({ s = u2.s; p = i_rdf_type; o = d2.o } <: triple)
       with decl u u.p
       and ();
       assert (rdfs2_derives c concl);
       assert (memP concl c);
       introduce exists (t : triple).
           memP t c /\ T_IRI rdf_type == T_IRI t.p /\
           x == subj_term t.s /\ cc == t.o
       with concl
       and ()
     end)

let step_range (c : list triple) (p cc x y : rdf_term)
  : Lemma (requires rho_df_frag_graph c /\ rho_df_closed c /\
                    herb_iext c (T_IRI rdfs_range) p cc /\
                    herb_iext c p x y)
          (ensures  herb_iext c (T_IRI rdf_type) y cc) =
  lemma_vocab_agree ();
  eliminate exists (decl : triple).
      memP decl c /\ T_IRI rdfs_range == T_IRI decl.p /\
      p == subj_term decl.s /\ cc == decl.o
  returns herb_iext c (T_IRI rdf_type) y cc
  with _ .
    (eliminate exists (u : triple).
        memP u c /\ p == T_IRI u.p /\ x == subj_term u.s /\ y == u.o
     returns herb_iext c (T_IRI rdf_type) y cc
     with _ . begin
       lemma_subj_term_iri decl.s u.p;
       assert (rho_df_frag_triple u);
       lemma_object_to_subject u.o;
       eliminate exists (zs : subject). subj_term zs == u.o
       returns herb_iext c (T_IRI rdf_type) y cc
       with _ . begin
         let concl : triple = { s = zs; p = i_rdf_type; o = decl.o } in
         introduce exists (d2 u2 : triple) (aa : wf_iri) (zs2 : subject).
             memP d2 c /\ d2.p == i_rdfs_range /\ d2.s == S_IRI aa /\
             memP u2 c /\ u2.p == aa /\
             subj_term zs2 == u2.o /\
             concl == ({ s = zs2; p = i_rdf_type; o = d2.o } <: triple)
         with decl u u.p zs
         and ();
         assert (rdfs3_derives c concl);
         assert (memP concl c);
         introduce exists (t : triple).
             memP t c /\ T_IRI rdf_type == T_IRI t.p /\
             y == subj_term t.s /\ cc == t.o
         with concl
         and ()
       end
     end)

let step_sub_property (c : list triple) (x y u v : rdf_term)
  : Lemma (requires rho_df_frag_graph c /\ rho_df_closed c /\
                    herb_iext c (T_IRI rdfs_subPropertyOf) x y /\
                    herb_iext c x u v)
          (ensures  herb_iext c y u v) =
  lemma_vocab_agree ();
  eliminate exists (decl : triple).
      memP decl c /\ T_IRI rdfs_subPropertyOf == T_IRI decl.p /\
      x == subj_term decl.s /\ y == decl.o
  returns herb_iext c y u v
  with _ .
    (eliminate exists (w : triple).
        memP w c /\ x == T_IRI w.p /\ u == subj_term w.s /\ v == w.o
     returns herb_iext c y u v
     with _ . begin
       lemma_subj_term_iri decl.s w.p;
       assert (rho_df_frag_triple decl);
       assert (T_IRI? decl.o);
       let b : wf_iri = T_IRI?._0 decl.o in
       assert (decl.o == T_IRI b);
       let concl : triple = { s = w.s; p = b; o = w.o } in
       introduce exists (d2 u2 : triple) (aa bb : wf_iri).
           memP d2 c /\ d2.p == i_rdfs_subPropertyOf /\
           d2.s == S_IRI aa /\ d2.o == T_IRI bb /\
           memP u2 c /\ u2.p == aa /\
           concl == ({ s = u2.s; p = bb; o = u2.o } <: triple)
       with decl w w.p b
       and ();
       assert (rdfs7_derives c concl);
       assert (memP concl c);
       introduce exists (t : triple).
           memP t c /\ y == T_IRI t.p /\ u == subj_term t.s /\ v == t.o
       with concl
       and ()
     end)

let step_sub_property_trans (c : list triple) (x y z : rdf_term)
  : Lemma (requires rho_df_closed c /\
                    herb_iext c (T_IRI rdfs_subPropertyOf) x y /\
                    herb_iext c (T_IRI rdfs_subPropertyOf) y z)
          (ensures  herb_iext c (T_IRI rdfs_subPropertyOf) x z) =
  lemma_vocab_agree ();
  eliminate exists (t1 : triple).
      memP t1 c /\ T_IRI rdfs_subPropertyOf == T_IRI t1.p /\
      x == subj_term t1.s /\ y == t1.o
  returns herb_iext c (T_IRI rdfs_subPropertyOf) x z
  with _ .
    (eliminate exists (t2 : triple).
        memP t2 c /\ T_IRI rdfs_subPropertyOf == T_IRI t2.p /\
        y == subj_term t2.s /\ z == t2.o
     returns herb_iext c (T_IRI rdfs_subPropertyOf) x z
     with _ . begin
       let concl : triple = { s = t1.s; p = i_rdfs_subPropertyOf; o = t2.o } in
       introduce exists (a1 a2 : triple) (ys : subject).
           memP a1 c /\ a1.p == i_rdfs_subPropertyOf /\
           memP a2 c /\ a2.p == i_rdfs_subPropertyOf /\
           subj_term ys == a1.o /\ a2.s == ys /\
           concl == ({ s = a1.s; p = i_rdfs_subPropertyOf; o = a2.o } <: triple)
       with t1 t2 t2.s
       and ();
       assert (rdfs5_derives c concl);
       assert (memP concl c);
       introduce exists (t : triple).
           memP t c /\ T_IRI rdfs_subPropertyOf == T_IRI t.p /\
           x == subj_term t.s /\ z == t.o
       with concl
       and ()
     end)

let step_sub_class (c : list triple) (x y u : rdf_term)
  : Lemma (requires rho_df_closed c /\
                    herb_iext c (T_IRI rdfs_subClassOf) x y /\
                    herb_iext c (T_IRI rdf_type) u x)
          (ensures  herb_iext c (T_IRI rdf_type) u y) =
  lemma_vocab_agree ();
  eliminate exists (sub : triple).
      memP sub c /\ T_IRI rdfs_subClassOf == T_IRI sub.p /\
      x == subj_term sub.s /\ y == sub.o
  returns herb_iext c (T_IRI rdf_type) u y
  with _ .
    (eliminate exists (typ : triple).
        memP typ c /\ T_IRI rdf_type == T_IRI typ.p /\
        u == subj_term typ.s /\ x == typ.o
     returns herb_iext c (T_IRI rdf_type) u y
     with _ . begin
       let concl : triple = { s = typ.s; p = i_rdf_type; o = sub.o } in
       introduce exists (sb tp : triple) (xs : subject).
           memP sb c /\ sb.p == i_rdfs_subClassOf /\ sb.s == xs /\
           memP tp c /\ tp.p == i_rdf_type /\ tp.o == subj_term xs /\
           concl == ({ s = tp.s; p = i_rdf_type; o = sb.o } <: triple)
       with sub typ sub.s
       and ();
       assert (rdfs9_derives c concl);
       assert (memP concl c);
       introduce exists (t : triple).
           memP t c /\ T_IRI rdf_type == T_IRI t.p /\
           u == subj_term t.s /\ y == t.o
       with concl
       and ()
     end)

let step_sub_class_trans (c : list triple) (x y z : rdf_term)
  : Lemma (requires rho_df_closed c /\
                    herb_iext c (T_IRI rdfs_subClassOf) x y /\
                    herb_iext c (T_IRI rdfs_subClassOf) y z)
          (ensures  herb_iext c (T_IRI rdfs_subClassOf) x z) =
  lemma_vocab_agree ();
  eliminate exists (t1 : triple).
      memP t1 c /\ T_IRI rdfs_subClassOf == T_IRI t1.p /\
      x == subj_term t1.s /\ y == t1.o
  returns herb_iext c (T_IRI rdfs_subClassOf) x z
  with _ .
    (eliminate exists (t2 : triple).
        memP t2 c /\ T_IRI rdfs_subClassOf == T_IRI t2.p /\
        y == subj_term t2.s /\ z == t2.o
     returns herb_iext c (T_IRI rdfs_subClassOf) x z
     with _ . begin
       let concl : triple = { s = t1.s; p = i_rdfs_subClassOf; o = t2.o } in
       introduce exists (a1 a2 : triple) (ys : subject).
           memP a1 c /\ a1.p == i_rdfs_subClassOf /\
           memP a2 c /\ a2.p == i_rdfs_subClassOf /\
           subj_term ys == a1.o /\ a2.s == ys /\
           concl == ({ s = a1.s; p = i_rdfs_subClassOf; o = a2.o } <: triple)
       with t1 t2 t2.s
       and ();
       assert (rdfs11_derives c concl);
       assert (memP concl c);
       introduce exists (t : triple).
           memP t c /\ T_IRI rdfs_subClassOf == T_IRI t.p /\
           x == subj_term t.s /\ z == t.o
       with concl
       and ()
     end)
#pop-options

// -------------------------------------------------------------------
// The six lifted to the condition statements.
// -------------------------------------------------------------------

#push-options "--z3rlimit 60"
let lemma_herb_cond_domain (c : list triple)
  : Lemma (requires rho_df_closed c) (ensures cond_domain (herbrand c)) =
  introduce forall (p cc x y : rdf_term).
      herb_iext c (T_IRI rdfs_domain) p cc ==>
      herb_iext c p x y ==>
      herb_iext c (T_IRI rdf_type) x cc
  with introduce _ ==> _
  with _ . introduce _ ==> _
  with _ . step_domain c p cc x y

let lemma_herb_cond_range (c : list triple)
  : Lemma (requires rho_df_frag_graph c /\ rho_df_closed c)
          (ensures cond_range (herbrand c)) =
  introduce forall (p cc x y : rdf_term).
      herb_iext c (T_IRI rdfs_range) p cc ==>
      herb_iext c p x y ==>
      herb_iext c (T_IRI rdf_type) y cc
  with introduce _ ==> _
  with _ . introduce _ ==> _
  with _ . step_range c p cc x y

let lemma_herb_cond_sub_property (c : list triple)
  : Lemma (requires rho_df_frag_graph c /\ rho_df_closed c)
          (ensures cond_subPropertyOf (herbrand c)) =
  introduce forall (x y u v : rdf_term).
      herb_iext c (T_IRI rdfs_subPropertyOf) x y ==>
      herb_iext c x u v ==>
      herb_iext c y u v
  with introduce _ ==> _
  with _ . introduce _ ==> _
  with _ . step_sub_property c x y u v

let lemma_herb_cond_sub_property_trans (c : list triple)
  : Lemma (requires rho_df_closed c)
          (ensures cond_subPropertyOf_trans (herbrand c)) =
  introduce forall (x y z : rdf_term).
      herb_iext c (T_IRI rdfs_subPropertyOf) x y ==>
      herb_iext c (T_IRI rdfs_subPropertyOf) y z ==>
      herb_iext c (T_IRI rdfs_subPropertyOf) x z
  with introduce _ ==> _
  with _ . introduce _ ==> _
  with _ . step_sub_property_trans c x y z

let lemma_herb_cond_sub_class (c : list triple)
  : Lemma (requires rho_df_closed c)
          (ensures cond_subClassOf (herbrand c)) =
  introduce forall (x y u : rdf_term).
      herb_iext c (T_IRI rdfs_subClassOf) x y ==>
      herb_iext c (T_IRI rdf_type) u x ==>
      herb_iext c (T_IRI rdf_type) u y
  with introduce _ ==> _
  with _ . introduce _ ==> _
  with _ . step_sub_class c x y u

let lemma_herb_cond_sub_class_trans (c : list triple)
  : Lemma (requires rho_df_closed c)
          (ensures cond_subClassOf_trans (herbrand c)) =
  introduce forall (x y z : rdf_term).
      herb_iext c (T_IRI rdfs_subClassOf) x y ==>
      herb_iext c (T_IRI rdfs_subClassOf) y z ==>
      herb_iext c (T_IRI rdfs_subClassOf) x z
  with introduce _ ==> _
  with _ . introduce _ ==> _
  with _ . step_sub_class_trans c x y z
#pop-options

// -------------------------------------------------------------------
// THEOREM. The Herbrand interpretation of a rho-df-closed fragment
// graph IS a rho-df interpretation. This is the machine-checked form
// of "saturation makes the canonical model a model".
// -------------------------------------------------------------------
val lemma_herbrand_rho_df_conditions (c : list triple)
  : Lemma (requires rho_df_frag_graph c /\ rho_df_closed c)
          (ensures  rho_df_conditions (herbrand c))

let lemma_herbrand_rho_df_conditions c =
  lemma_herb_cond_domain c;
  lemma_herb_cond_range c;
  lemma_herb_cond_sub_property c;
  lemma_herb_cond_sub_property_trans c;
  lemma_herb_cond_sub_class c;
  lemma_herb_cond_sub_class_trans c

// ===================================================================
// 5. THE CLOSED-GRAPH THEOREM.
//
// On a rho-df-closed fragment graph, rho-df entailment IS simple
// entailment. The completeness direction is the new half; the
// soundness direction is `interpolation_sound` restricted to a
// smaller interpretation class, which needs no hypotheses at all.
// ===================================================================

val rho_df_closed_complete (c e : list triple)
  : Lemma (requires rho_df_frag_graph c /\ rho_df_closed c /\
                    graph_tt_free e /\ rho_df_entails c e)
          (ensures  simple_entailment_spec c e)

let rho_df_closed_complete c e =
  lemma_frag_tt_free c;
  lemma_herbrand_rho_df_conditions c;
  lemma_herbrand_satisfies c;
  assert (satisfies (herbrand c) e);
  lemma_herbrand_reflects c e

val rho_df_closed_sound (c e : list triple)
  : Lemma (requires simple_entailment_spec c e)
          (ensures  rho_df_entails c e)

let rho_df_closed_sound c e = interpolation_sound c e

// -------------------------------------------------------------------
// THEOREM (rho-df completeness, closed-graph form).
// -------------------------------------------------------------------
val rho_df_closed_iff (c e : list triple)
  : Lemma (requires rho_df_frag_graph c /\ rho_df_closed c /\ graph_tt_free e)
          (ensures  rho_df_entails c e <==> simple_entailment_spec c e)

let rho_df_closed_iff c e =
  introduce rho_df_entails c e ==> simple_entailment_spec c e
  with _ . rho_df_closed_complete c e;
  introduce simple_entailment_spec c e ==> rho_df_entails c e
  with _ . rho_df_closed_sound c e

// ===================================================================
// 6. THE SATURATION FORM.
//
// The shape a closure operator instantiates: `c` is any graph that is
// EXTENSIVE over `g` (contains it), rho-df-SOUND for `g` (entailed by
// it), and rho-df-CLOSED. Then `c` decides rho-df entailment of
// fragment graphs from `g` by simple entailment.
//
// `is_subgraph` is RDF.Entailment.Simple.Spec's own predicate, reused.
// ===================================================================

let lemma_subgraph_satisfies (i : interp) (g c : list triple)
  : Lemma (requires is_subgraph g c /\ satisfies i c) (ensures satisfies i g) =
  eliminate exists (a : bnode_assignment i.idom). holds_all i a c
  returns satisfies i g
  with _ . assert (holds_all i a g)

val rho_df_saturation_complete (g c e : list triple)
  : Lemma (requires rho_df_frag_graph c /\ rho_df_closed c /\
                    graph_tt_free e /\ is_subgraph g c /\
                    rho_df_entails g e)
          (ensures  simple_entailment_spec c e)

let rho_df_saturation_complete g c e =
  introduce forall (i : interp).
      rho_df_conditions i ==> satisfies i c ==> satisfies i e
  with introduce rho_df_conditions i ==> (satisfies i c ==> satisfies i e)
  with _ . introduce satisfies i c ==> satisfies i e
  with _ . lemma_subgraph_satisfies i g c;
  assert (rho_df_entails c e);
  rho_df_closed_complete c e

val rho_df_saturation_sound (g c e : list triple)
  : Lemma (requires rho_df_entails g c /\ simple_entailment_spec c e)
          (ensures  rho_df_entails g e)

let rho_df_saturation_sound g c e =
  rho_df_closed_sound c e;
  introduce forall (i : interp).
      rho_df_conditions i ==> satisfies i g ==> satisfies i e
  with introduce rho_df_conditions i ==> (satisfies i g ==> satisfies i e)
  with _ . introduce satisfies i g ==> satisfies i e
  with _ . ()

// -------------------------------------------------------------------
// THEOREM (rho-df completeness, saturation form). The end-to-end
// statement M1 asks for, with the closure operator abstracted to its
// three properties.
// -------------------------------------------------------------------
val rho_df_saturation_iff (g c e : list triple)
  : Lemma (requires rho_df_frag_graph c /\ rho_df_closed c /\
                    graph_tt_free e /\ is_subgraph g c /\
                    rho_df_entails g c)
          (ensures  rho_df_entails g e <==> simple_entailment_spec c e)

let rho_df_saturation_iff g c e =
  introduce rho_df_entails g e ==> simple_entailment_spec c e
  with _ . rho_df_saturation_complete g c e;
  introduce simple_entailment_spec c e ==> rho_df_entails g e
  with _ . rho_df_saturation_sound g c e

// ===================================================================
// 7. THE SHIPPING CLOSURE, completeness direction.
//
// The half that was missing. The three hypotheses are named, and each
// is M2's to discharge (see the banner):
//   * `rho_df_frag_graph (rdfs_closure g fuel)` -- fragment
//     preservation. Every rho-df row copies objects from its premises
//     and the five RS-2 rows emit IRI objects, so this follows from
//     `rho_df_frag_graph g` by a per-row argument this module does not
//     run.
//   * `rho_df_closed (rdfs_closure g fuel)` -- saturation
//     (FixedPoint.step_saturated plus the six missing per-row
//     `_complete` lemmas).
//   * `is_subgraph g (rdfs_closure g fuel)` -- iterated extensivity
//     (FixedPoint.lemma_step_extensive, under its `no_dup_keys`
//     hypothesis).
//
// NOTE the direction. The converse is NOT available for the shipping
// closure and must not be claimed: finding C-2 -- the twelve-rule step
// also runs rdfs1 / rdfs4a / rdfs4b / rdfs8 / rdfs13 / container
// membership, whose conclusions are not rho-df-entailed.
// ===================================================================

val rdfs_closure_rho_df_complete (g e : rdf_graph) (fuel : nat)
  : Lemma (requires rho_df_frag_graph (rdfs_closure g fuel) /\
                    rho_df_closed (rdfs_closure g fuel) /\
                    graph_tt_free e /\
                    is_subgraph g (rdfs_closure g fuel) /\
                    rho_df_entails g e)
          (ensures  simple_entailment_spec (rdfs_closure g fuel) e)

let rdfs_closure_rho_df_complete g e fuel =
  rho_df_saturation_complete g (rdfs_closure g fuel) e

// ===================================================================
// 8. FINDING C-1, MACHINE-CHECKED (witness W1).
//
// The reduction of the interpretation class in section 2 is NECESSARY,
// not a convenience. This section proves the two halves of witness W1
// as separate lemmas over an ARBITRARY pair of distinct IRIs -- no
// concrete example.org strings, so the separation is not an artefact
// of one chosen graph:
//
//   `rdfs_entails_subclass_selfloop`        -- [X sc Y] RDFS-entails
//                                              [X sc X], for ANY X, Y;
//   `rho_df_not_entails_subclass_selfloop`  -- [X sc Y] does NOT
//                                              rho-df-entail [X sc X],
//                                              for X <> Y.
//
// Together: the two entailment relations DIFFER on a two-triple
// fragment graph. Since the shipping `rdfs_closure` never derives the
// self-loop (the reflexivity harvest is a separate regime-scoped
// pass -- finding RS-1), the coverage doc's gap-1 statement, which
// pairs `rdfs_entails d_minimal` with closure-then-simple-entailment,
// cannot be an iff. This is also the NON-VACUITY check for section 5's
// hypotheses: `lemma_selfloop_witness_closed` exhibits a NON-EMPTY
// graph satisfying `rho_df_frag_graph /\ rho_df_closed`, so the
// theorems above are not quantified over an empty set of graphs.
// ===================================================================

let sc_triple (x y : wf_iri) : triple =
  { s = S_IRI x; p = i_rdfs_subClassOf; o = T_IRI y }

// The four rho-df predicate IRIs the witness graph must be shown NOT
// to carry. Concrete strings, decided by normalisation.
let lemma_rho_df_vocab_distinct ()
  : Lemma (~(i_rdfs_subClassOf == i_rdfs_domain) /\
           ~(i_rdfs_subClassOf == i_rdfs_range) /\
           ~(i_rdfs_subClassOf == i_rdfs_subPropertyOf) /\
           ~(i_rdfs_subClassOf == i_rdf_type)) =
  assert_norm (i_rdfs_subClassOf <> i_rdfs_domain);
  assert_norm (i_rdfs_subClassOf <> i_rdfs_range);
  assert_norm (i_rdfs_subClassOf <> i_rdfs_subPropertyOf);
  assert_norm (i_rdfs_subClassOf <> i_rdf_type)

let lemma_selfloop_witness_frag (x y : wf_iri)
  : Lemma (rho_df_frag_graph [sc_triple x y]) = ()

// The single-triple graph IS rho-df-closed when the two IRIs differ:
// five rows have no matching premise at all, and rdfs11 would need
// `subj_term ys == T_IRI y` with `ys == S_IRI x`, i.e. X = Y.
#push-options "--z3rlimit 60"
let lemma_selfloop_witness_closed (x y : wf_iri)
  : Lemma (requires ~(x == y)) (ensures rho_df_closed [sc_triple x y]) =
  lemma_rho_df_vocab_distinct ()
#pop-options

// The Herbrand interpretation of the witness graph is the
// COUNTERMODEL: it makes [X sc Y] true and [X sc X] false.
let lemma_selfloop_not_in_herbrand (x y : wf_iri)
  : Lemma (requires ~(x == y))
          (ensures  ~(herb_iext [sc_triple x y]
                                (T_IRI i_rdfs_subClassOf) (T_IRI x) (T_IRI x))) = ()

#push-options "--z3rlimit 60"
val rho_df_not_entails_subclass_selfloop (x y : wf_iri)
  : Lemma (requires ~(x == y))
          (ensures  ~(rho_df_entails [sc_triple x y] [sc_triple x x]))

let rho_df_not_entails_subclass_selfloop x y =
  let c : list triple = [sc_triple x y] in
  lemma_selfloop_witness_frag x y;
  lemma_selfloop_witness_closed x y;
  lemma_frag_tt_free c;
  lemma_herbrand_rho_df_conditions c;
  lemma_herbrand_satisfies c;
  lemma_selfloop_not_in_herbrand x y;
  assert (rho_df_conditions (herbrand c));
  assert (satisfies (herbrand c) c);
  assert (~(satisfies (herbrand c) [sc_triple x x]))
#pop-options

// The same pair IS an RDFS entailment: `cond_subClassOf_ic` puts X in
// IC and `cond_subClassOf_refl` closes the loop. No premise about Y is
// used, and no rule of the table is involved -- this is a CONDITION,
// which is exactly why no rule-set completeness argument can reach it.
#push-options "--z3rlimit 60"
val rdfs_entails_subclass_selfloop (x y : wf_iri)
  : Lemma (rdfs_entails d_minimal [sc_triple x y] [sc_triple x x])

let rdfs_entails_subclass_selfloop x y =
  lemma_vocab_agree ();
  introduce forall (i : interp).
      rdfs_conditions d_minimal i ==>
      satisfies i [sc_triple x y] ==> satisfies i [sc_triple x x]
  with introduce rdfs_conditions d_minimal i ==>
                 (satisfies i [sc_triple x y] ==> satisfies i [sc_triple x x])
  with _ . introduce satisfies i [sc_triple x y] ==> satisfies i [sc_triple x x]
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a [sc_triple x y]
    returns satisfies i [sc_triple x x]
    with _ . begin
      assert (memP (sc_triple x y) [sc_triple x y]);
      assert (triple_holds i a (sc_triple x y));
      assert (i.iext (i.i_iri rdfs_subClassOf) (i.i_iri x) (i.i_iri y));
      assert (icext i (i.i_iri x) (i.i_iri rdfs_Class));
      assert (i.iext (i.i_iri rdfs_subClassOf) (i.i_iri x) (i.i_iri x));
      assert (triple_holds i a (sc_triple x x));
      assert (holds_all i a [sc_triple x x])
    end
  end
#pop-options

// -------------------------------------------------------------------
// THEOREM (the separation). On the rho-df fragment, RDFS entailment is
// STRICTLY WEAKER as a hypothesis than rho-df entailment -- so the two
// cannot be interchanged in a completeness statement.
// -------------------------------------------------------------------
val rho_df_entailment_strictly_stronger (x y : wf_iri)
  : Lemma (requires ~(x == y))
          (ensures  rdfs_entails d_minimal [sc_triple x y] [sc_triple x x] /\
                    ~(rho_df_entails [sc_triple x y] [sc_triple x x]))

let rho_df_entailment_strictly_stronger x y =
  rdfs_entails_subclass_selfloop x y;
  rho_df_not_entails_subclass_selfloop x y
