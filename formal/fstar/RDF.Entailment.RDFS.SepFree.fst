module RDF.Entailment.RDFS.SepFree

// ===================================================================
// #338 follow-up, PHASE 1: every RDFS closure rule preserves
// "separator-freeness" (no U+001F in a subject label, a predicate, or
// an IRI/bnode object label).
//
// WHY: `closure_chain_wf g` (RDF.Entailment.RDFS.ModelTheory.fst,
// `forall n. ig_wf_sp (build_indexed (closure_iter g n))`) needs
// `ig_wf_sp` at every step of the closure, and
// `RDF.Indexed.KeyInjectivity.lemma_build_indexed_wf_sp` discharges
// `ig_wf_sp (build_indexed g)` from the SIDE CONDITION
// `graph_sp_sep_free g` (subject label + predicate clean, per triple
// of g). A one-graph discharge is not enough for a CHAIN: each
// `closure_iter` step adds triples the rule tables construct out of
// PREMISE triples, so "the input graph was clean" only propagates to
// "the output graph is clean" if every rule's CONCLUSION is clean
// whenever its PREMISES are. That per-rule preservation is what this
// module proves, one lemma per row of RDF.Entailment.RDF.Spec /
// RDF.Entailment.RDFS.Spec's rule tables. Phase 2 (not here) folds
// these into a single step-lemma against `rdfs_closure_step` and
// induction over `closure_iter`.
//
// STRENGTHENING OVER KeyInjectivity's SIDE CONDITION: `graph_sp_sep_free`
// (KeyInjectivity) covers subject label + predicate only -- exactly
// what `sp_key` needs. That is NOT enough to carry itself through a
// closure step: several rows' conclusion SUBJECT comes from a premise
// OBJECT (rdfs3, rdfs4b -- `subj_term ys == u.o`), so a hypothesis that
// says nothing about object cleanliness cannot supply it. This module's
// `graph_sep_free` therefore covers all three positions -- subject,
// predicate, AND (IRI/bnode) object label -- and `lemma_graph_sep_free_sp`
// is the one-line bridge back down to KeyInjectivity's weaker condition
// for the cases (most of them) that only need it.
//
// TRAP, DELIBERATELY NOT CLOSED HERE: `rdf_axiomatic`, `rdfs_axiomatic`,
// and `rdfs_member_subproperty` all route through
// `RDF.Entailment.RDF.Spec.is_rdf_member_iri`, which admits
// `rdf:_<ANY string n>` -- INCLUDING strings containing U+001F. "licensed
// by these predicates implies sep-free" is therefore FALSE in general;
// no lemma of that shape is attempted. What IS true, and included below
// (section 4), is that the FINITE concrete tables
// (`rdf_axiomatic_triples`, `rdfs_axiomatic_triples`,
// `container_membership_properties` = the shipping `rdf:_1`..`rdf:_5`
// slice) are separator-free -- every entry is a literal ASCII string.
// Phase 2 handles the engine's actual container-membership rule (which
// only ever emits over that finite slice, by direct construction) with
// that fact rather than with the (false) general `is_rdf_member_iri`
// closure property.
//
// Verify-only module; nothing here extracts, and nothing here is wired
// into build-ocaml.sh (orchestrator's job on landing).
// ===================================================================

open FStar.String
open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Vocabulary.Axioms
open RDFS.Closure
open RDF.Entailment.Simple.Spec
open RDF.Entailment.RDF.Spec
open RDF.Entailment.RDFS.Spec
open RDF.Indexed.KeyInjectivity

// ===================================================================
// 1. The strengthened per-triple condition: subject label, predicate,
// AND (IRI/bnode) object label all separator-free. `T_Literal` and
// `T_TripleTerm` objects carry no bare IRI/bnode label at the top
// level (a triple term's own components are not this triple's `o`
// label), so they impose no constraint here -- `True`.
// ===================================================================

let obj_label_sep_free (o : rdf_term) : prop =
  match o with
  | T_IRI i -> str_sep_free i
  | T_BNode b -> str_sep_free b
  | _ -> True

let triple_sep_free (t : triple) : prop =
  subj_label_sep_free t.s /\ str_sep_free t.p /\ obj_label_sep_free t.o

let graph_sep_free (g : list triple) : prop =
  forall (t : triple). memP t g ==> triple_sep_free t

// The bridge back to KeyInjectivity's weaker (subject+predicate-only)
// side condition -- every graph this module's rows need already
// satisfies the stronger `graph_sep_free`, which entails it.
let lemma_graph_sep_free_sp (g : list triple)
  : Lemma (requires graph_sep_free g) (ensures graph_sp_sep_free g) =
  introduce forall (t : triple). memP t g ==> (subj_label_sep_free t.s /\ str_sep_free t.p)
  with introduce memP t g ==> (subj_label_sep_free t.s /\ str_sep_free t.p)
  with _ . ()

// ===================================================================
// 2. Vocabulary constants are separator-free. Every constant below is
// a concrete ASCII string (RDF.Vocabulary.fsti); `assert_norm` on
// `str_sep_free` (itself `count_sep (list_of_string s) == 0`) closes
// each conjunct by normalization, exactly as KeyInjectivity's own
// "I_"/"B_" tag lemmas do.
// ===================================================================

let lemma_vocab_sep_free ()
  : Lemma (ensures
      str_sep_free i_rdf_type /\
      str_sep_free i_rdfs_Resource /\
      str_sep_free i_rdfs_Class /\
      str_sep_free i_rdfs_Datatype /\
      str_sep_free i_rdfs_Literal /\
      str_sep_free i_rdfs_subClassOf /\
      str_sep_free i_rdfs_subPropertyOf /\
      str_sep_free i_rdfs_domain /\
      str_sep_free i_rdfs_range /\
      str_sep_free i_rdfs_member /\
      str_sep_free i_rdfs_ContainerMembershipProperty /\
      str_sep_free i_rdf_Property) =
  assert_norm (str_sep_free i_rdf_type);
  assert_norm (str_sep_free i_rdfs_Resource);
  assert_norm (str_sep_free i_rdfs_Class);
  assert_norm (str_sep_free i_rdfs_Datatype);
  assert_norm (str_sep_free i_rdfs_Literal);
  assert_norm (str_sep_free i_rdfs_subClassOf);
  assert_norm (str_sep_free i_rdfs_subPropertyOf);
  assert_norm (str_sep_free i_rdfs_domain);
  assert_norm (str_sep_free i_rdfs_range);
  assert_norm (str_sep_free i_rdfs_member);
  assert_norm (str_sep_free i_rdfs_ContainerMembershipProperty);
  assert_norm (str_sep_free i_rdf_Property)

// ===================================================================
// 3. `subj_term` bridging, both directions. Several rows move a term
// between subject position (one triple) and object position (another)
// via `subj_term`/the `subj_term ys == u.o` premise shape; both
// directions of "clean subject label iff clean object label" are
// needed across the rows below.
// ===================================================================

// Object-to-subject: a premise object that instantiates a subject
// (`subj_term ys == o`) carries the object's cleanliness over to the
// subject's label -- needed wherever a conclusion SUBJECT is read off
// a premise OBJECT (rdfs3, rdfs4b, the endpoint-reflexivity rows).
let lemma_subj_term_obj_sep_free (ys : subject) (o : rdf_term)
  : Lemma (requires subj_term ys == o /\ obj_label_sep_free o)
          (ensures subj_label_sep_free ys) =
  match ys with
  | S_IRI i -> ()
  | S_BNode b -> ()

// Subject-to-object: the converse, needed wherever a conclusion OBJECT
// is `subj_term` of a premise subject (rdfs6, rdfs10, the
// endpoint-reflexivity rows' own conclusion object).
let lemma_subj_term_sep_free (xs : subject)
  : Lemma (requires subj_label_sep_free xs)
          (ensures obj_label_sep_free (subj_term xs)) =
  match xs with
  | S_IRI i -> ()
  | S_BNode b -> ()

// ===================================================================
// 4. Per-row conclusion lemmas. One per premise-driven row of the RDF
// (rdfD2) and RDFS (rdfs1..rdfs13 minus rdfs4a/4b's NOT-IMPLEMENTED
// status not mattering here -- their `_derives` relations are still
// spec-level rows this module covers) rule tables, plus the two
// endpoint-reflexivity condition-level consequences. Each is proved by
// eliminating the row's existential and tracing every component of the
// conclusion triple to either (a) a component of a premise triple
// `memP _ g`, licensed by `graph_sep_free g`, possibly crossing a
// `subj_term` bridge from section 3; or (b) a vocabulary constant,
// licensed by `lemma_vocab_sep_free`.
// ===================================================================

// rdfD2: `xxx aaa yyy . |- aaa rdf:type rdf:Property .`
// Conclusion subject is the PREMISE PREDICATE (`S_IRI u.p`) -- clean
// because `graph_sep_free` covers predicates directly, no bridge
// needed.
let lemma_rdfD2_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfD2_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (u : triple). memP u g /\ t == rdfD2_conclusion u
  returns triple_sep_free t
  with _ . ()

// rdfs1 (RDF 1.1 reading): `any IRI aaa in D |- aaa rdf:type rdfs:Datatype .`
// The conclusion subject comes from D, not from g -- the side condition
// is on `dd`, per the brief's `datatype_set_sep_free`.
let datatype_set_sep_free (dd : datatype_set) : prop =
  forall (a : wf_iri). dd a ==> str_sep_free a

let lemma_rdfs1_sep_free (dd : datatype_set) (t : triple)
  : Lemma (requires datatype_set_sep_free dd /\ rdfs1_derives dd t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (a : wf_iri).
      dd a /\ t == ({ s = S_IRI a; p = i_rdf_type; o = T_IRI i_rdfs_Datatype } <: triple)
  returns triple_sep_free t
  with _ . ()

// rdfs2: `aaa rdfs:domain xxx . yyy aaa zzz . |- yyy rdf:type xxx .`
let lemma_rdfs2_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs2_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (decl u : triple) (aa : wf_iri).
      memP decl g /\ decl.p == i_rdfs_domain /\ decl.s == S_IRI aa /\
      memP u g /\ u.p == aa /\
      t == ({ s = u.s; p = i_rdf_type; o = decl.o } <: triple)
  returns triple_sep_free t
  with _ . ()

// rdfs3: `aaa rdfs:range xxx . yyy aaa zzz . |- zzz rdf:type xxx .`
// Conclusion subject `zs` is the premise OBJECT `u.o`, via
// `subj_term zs == u.o` -- crosses the object-to-subject bridge.
let lemma_rdfs3_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs3_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (decl u : triple) (aa : wf_iri) (zs : subject).
      memP decl g /\ decl.p == i_rdfs_range /\ decl.s == S_IRI aa /\
      memP u g /\ u.p == aa /\
      subj_term zs == u.o /\
      t == ({ s = zs; p = i_rdf_type; o = decl.o } <: triple)
  returns triple_sep_free t
  with _ . lemma_subj_term_obj_sep_free zs u.o

// rdfs4a: `xxx aaa yyy . |- xxx rdf:type rdfs:Resource .`
let lemma_rdfs4a_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs4a_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (u : triple). memP u g /\
      t == ({ s = u.s; p = i_rdf_type; o = T_IRI i_rdfs_Resource } <: triple)
  returns triple_sep_free t
  with _ . ()

// rdfs4b: `xxx aaa yyy . |- yyy rdf:type rdfs:Resource .`
// Conclusion subject `ys` is the premise OBJECT `u.o` -- same bridge
// as rdfs3.
let lemma_rdfs4b_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs4b_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (u : triple) (ys : subject). memP u g /\ subj_term ys == u.o /\
      t == ({ s = ys; p = i_rdf_type; o = T_IRI i_rdfs_Resource } <: triple)
  returns triple_sep_free t
  with _ . lemma_subj_term_obj_sep_free ys u.o

// rdfs5: `xxx rdfs:subPropertyOf yyy . yyy rdfs:subPropertyOf zzz . |-
//         xxx rdfs:subPropertyOf zzz .`
// The conclusion's subject/object come straight from `t1.s`/`t2.o` --
// the linking variable `ys` (which bridges `t1.o`/`t2.s`) never
// appears in the conclusion, so no bridge lemma is needed here.
let lemma_rdfs5_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs5_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (t1 t2 : triple) (ys : subject).
      memP t1 g /\ t1.p == i_rdfs_subPropertyOf /\
      memP t2 g /\ t2.p == i_rdfs_subPropertyOf /\
      subj_term ys == t1.o /\ t2.s == ys /\
      t == ({ s = t1.s; p = i_rdfs_subPropertyOf; o = t2.o } <: triple)
  returns triple_sep_free t
  with _ . ()

// rdfs6: `xxx rdf:type rdf:Property . |- xxx rdfs:subPropertyOf xxx .`
// Conclusion object is `subj_term u.s` -- the subject-to-object bridge.
let lemma_rdfs6_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs6_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (u : triple). memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdf_Property /\
      t == ({ s = u.s; p = i_rdfs_subPropertyOf; o = subj_term u.s } <: triple)
  returns triple_sep_free t
  with _ . lemma_subj_term_sep_free u.s

// rdfs7: `aaa rdfs:subPropertyOf bbb . xxx aaa yyy . |- xxx bbb yyy .`
let lemma_rdfs7_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs7_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (decl u : triple) (aa b : wf_iri).
      memP decl g /\ decl.p == i_rdfs_subPropertyOf /\
      decl.s == S_IRI aa /\ decl.o == T_IRI b /\
      memP u g /\ u.p == aa /\
      t == ({ s = u.s; p = b; o = u.o } <: triple)
  returns triple_sep_free t
  with _ . ()

// rdfs8: `xxx rdf:type rdfs:Class . |- xxx rdfs:subClassOf rdfs:Resource .`
let lemma_rdfs8_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs8_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (u : triple). memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdfs_Class /\
      t == ({ s = u.s; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Resource } <: triple)
  returns triple_sep_free t
  with _ . ()

// rdfs9: `xxx rdfs:subClassOf yyy . zzz rdf:type xxx . |- zzz rdf:type yyy .`
// Same shape as rdfs5: the linking variable `xs` never appears in the
// conclusion, so no bridge lemma is needed.
let lemma_rdfs9_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs9_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (sub typ : triple) (xs : subject).
      memP sub g /\ sub.p == i_rdfs_subClassOf /\ sub.s == xs /\
      memP typ g /\ typ.p == i_rdf_type /\ typ.o == subj_term xs /\
      t == ({ s = typ.s; p = i_rdf_type; o = sub.o } <: triple)
  returns triple_sep_free t
  with _ . ()

// rdfs10: `xxx rdf:type rdfs:Class . |- xxx rdfs:subClassOf xxx .`
let lemma_rdfs10_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs10_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (u : triple). memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdfs_Class /\
      t == ({ s = u.s; p = i_rdfs_subClassOf; o = subj_term u.s } <: triple)
  returns triple_sep_free t
  with _ . lemma_subj_term_sep_free u.s

// rdfs11: `xxx rdfs:subClassOf yyy . yyy rdfs:subClassOf zzz . |-
//          xxx rdfs:subClassOf zzz .` -- same shape as rdfs5.
let lemma_rdfs11_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs11_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (t1 t2 : triple) (ys : subject).
      memP t1 g /\ t1.p == i_rdfs_subClassOf /\
      memP t2 g /\ t2.p == i_rdfs_subClassOf /\
      subj_term ys == t1.o /\ t2.s == ys /\
      t == ({ s = t1.s; p = i_rdfs_subClassOf; o = t2.o } <: triple)
  returns triple_sep_free t
  with _ . ()

// rdfs12: `xxx rdf:type rdfs:ContainerMembershipProperty . |-
//          xxx rdfs:subPropertyOf rdfs:member .`
let lemma_rdfs12_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs12_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (u : triple). memP u g /\ u.p == i_rdf_type /\
      u.o == T_IRI i_rdfs_ContainerMembershipProperty /\
      t == ({ s = u.s; p = i_rdfs_subPropertyOf; o = T_IRI i_rdfs_member } <: triple)
  returns triple_sep_free t
  with _ . ()

// rdfs13: `xxx rdf:type rdfs:Datatype . |- xxx rdfs:subClassOf rdfs:Literal .`
let lemma_rdfs13_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs13_derives g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (u : triple). memP u g /\ u.p == i_rdf_type /\ u.o == T_IRI i_rdfs_Datatype /\
      t == ({ s = u.s; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Literal } <: triple)
  returns triple_sep_free t
  with _ . ()

// `rdfs:subClassOf` endpoint reflexivity (section 9 semantic
// conditions, the `rdfs_reflexivity_axioms` harvest's licence). The
// witness `xs` is EITHER the premise subject OR (bridged) the premise
// object -- both cases feed both a subject-position and an
// object-position occurrence in the conclusion, so both bridge
// directions are exercised depending on the disjunct.
let lemma_rdfs_subClassOf_endpoint_refl_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs_subClassOf_endpoint_refl g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (u : triple) (xs : subject).
      memP u g /\ u.p == i_rdfs_subClassOf /\
      (u.s == xs \/ u.o == subj_term xs) /\
      t == ({ s = xs; p = i_rdfs_subClassOf; o = subj_term xs } <: triple)
  returns triple_sep_free t
  with _ . begin
    eliminate u.s == xs \/ u.o == subj_term xs
    returns triple_sep_free t
    with _ . lemma_subj_term_sep_free xs
    and  _ . begin
      lemma_subj_term_obj_sep_free xs u.o;
      lemma_subj_term_sep_free xs
    end
  end

// `rdfs:subPropertyOf` endpoint reflexivity -- dual of the above.
let lemma_rdfs_subPropertyOf_endpoint_refl_sep_free (g : list triple) (t : triple)
  : Lemma (requires graph_sep_free g /\ rdfs_subPropertyOf_endpoint_refl g t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (u : triple) (xs : subject).
      memP u g /\ u.p == i_rdfs_subPropertyOf /\
      (u.s == xs \/ u.o == subj_term xs) /\
      t == ({ s = xs; p = i_rdfs_subPropertyOf; o = subj_term xs } <: triple)
  returns triple_sep_free t
  with _ . begin
    eliminate u.s == xs \/ u.o == subj_term xs
    returns triple_sep_free t
    with _ . lemma_subj_term_sep_free xs
    and  _ . begin
      lemma_subj_term_obj_sep_free xs u.o;
      lemma_subj_term_sep_free xs
    end
  end

// ===================================================================
// 5. The FINITE concrete tables are separator-free: `rdf_axiomatic_
// triples` (8 rows), `rdfs_axiomatic_triples` (38 rows), and
// `container_membership_properties` (the shipping `rdf:_1`..`rdf:_5`
// slice). Every entry is built from literal ASCII strings, so this
// closes by normalization -- but 46 triples over `assert_norm` in one
// shot risks the normalizer choking on one giant term, so the robust
// route (per the brief) is a decidable BOOLEAN checker, mirroring
// KeyInjectivity's own `graph_sp_sep_free_b`/soundness pattern, with
// one `assert_norm` per checker call.
// ===================================================================

let obj_label_sep_free_b (o : rdf_term) : bool =
  match o with
  | T_IRI i -> count_sep_b (list_of_string i) = 0
  | T_BNode b -> count_sep_b (list_of_string b) = 0
  | _ -> true

let triple_sep_free_b (t : triple) : bool =
  count_sep_b (list_of_string (subj_label t.s)) = 0 &&
  count_sep_b (list_of_string t.p) = 0 &&
  obj_label_sep_free_b t.o

let rec graph_sep_free_b (g : list triple) : bool =
  match g with
  | [] -> true
  | t :: rest -> triple_sep_free_b t && graph_sep_free_b rest

let rec lemma_graph_sep_free_b_sound (g : list triple)
  : Lemma (requires graph_sep_free_b g == true)
          (ensures graph_sep_free g) =
  match g with
  | [] -> ()
  | t :: rest ->
    lemma_count_sep_b_eq (list_of_string (subj_label t.s));
    lemma_count_sep_b_eq (list_of_string t.p);
    (match t.o with
     | T_IRI i -> lemma_count_sep_b_eq (list_of_string i)
     | T_BNode b -> lemma_count_sep_b_eq (list_of_string b)
     | _ -> ());
    lemma_graph_sep_free_b_sound rest

let rec iri_list_sep_free_b (l : list wf_iri) : bool =
  match l with
  | [] -> true
  | i :: rest -> count_sep_b (list_of_string i) = 0 && iri_list_sep_free_b rest

let rec lemma_iri_list_sep_free_b_sound (l : list wf_iri)
  : Lemma (requires iri_list_sep_free_b l == true)
          (ensures forall (p : wf_iri). memP p l ==> str_sep_free p) =
  match l with
  | [] -> ()
  | i :: rest ->
    lemma_count_sep_b_eq (list_of_string i);
    lemma_iri_list_sep_free_b_sound rest

let lemma_axiomatic_tables_sep_free ()
  : Lemma (ensures
      (forall (t : triple). memP t rdf_axiomatic_triples ==> triple_sep_free t) /\
      (forall (t : triple). memP t rdfs_axiomatic_triples ==> triple_sep_free t) /\
      (forall (p : wf_iri). memP p container_membership_properties ==> str_sep_free p)) =
  assert_norm (graph_sep_free_b rdf_axiomatic_triples == true);
  lemma_graph_sep_free_b_sound rdf_axiomatic_triples;
  assert_norm (graph_sep_free_b rdfs_axiomatic_triples == true);
  lemma_graph_sep_free_b_sound rdfs_axiomatic_triples;
  assert_norm (iri_list_sep_free_b container_membership_properties == true);
  lemma_iri_list_sep_free_b_sound container_membership_properties
