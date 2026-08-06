module RDF.Indexed.KeyInjectivity

// ===================================================================
// #338: `sp_key` injectivity on U+001F-free keys, and the discharge
// of `ig_wf_sp` for graphs meeting that side condition.
//
// The gap this closes: `ig_wf_sp` -- "everything served from the
// sp-bucket is a graph triple with EXACTLY the queried subject and
// predicate" -- was only available in the weak form (membership plus
// own-key-equals-queried-key), because recovering the components
// from a composite key needs sp_key injectivity, and sp_key is NOT
// injective on arbitrary wf_iris: `is_iri` admits U+001F, and
// RDF.Semantics.HypothesisWitness.theorem_sp_key_not_injective
// exhibits the collision. The repair, per the issue: injectivity
// holds as soon as ONE side of the key equation is U+001F-free, by a
// separator-counting argument -- a clean key contains exactly one
// separator, equality forces the other side to contain exactly one
// too, and a one-separator string splits uniquely.
//
// The one-sided form is what the wf discharge needs: the in-bucket
// side comes from the graph (side condition), while the queried
// (s, p) in `ig_wf_sp`'s forall stays completely arbitrary.
//
// Verify-only module; nothing here extracts. The enabling refactor
// (subject_to_key / sp_key built with `^` instead of the opaque
// `String.concat`) lives in RDF.Indexed.fsti with its own comment.
//
// Follow-up (NOT here): `closure_chain_wf g` = forall n. ig_wf_sp
// (build_indexed (closure_iter g n)) additionally needs "every
// closure rule preserves separator-freeness" -- a rule-by-rule
// induction that belongs with the licensing program's machinery.
// This module provides the per-graph discharge it will compose with.
// ===================================================================

open FStar.String
open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open OWL.Semantics
open OWL.Semantics.MemLemmas

// ===================================================================
// 0. The separator, and counting it.
// ===================================================================

let sep_char : char = '\x1f'

let rec count_sep (l : list char) : nat =
  match l with
  | [] -> 0
  | c :: rest -> (if c = sep_char then 1 else 0) + count_sep rest

let rec lemma_count_sep_append (a b : list char)
  : Lemma (ensures count_sep (a @ b) == count_sep a + count_sep b)
          (decreases a) =
  match a with
  | [] -> ()
  | _ :: t -> lemma_count_sep_append t b

// A string is separator-free when its character list counts zero.
let str_sep_free (s : string) : prop =
  count_sep (list_of_string s) == 0

// ===================================================================
// 1. The unique-split lemma: a decomposition around a separator with
// a separator-free prefix is unique among such decompositions.
// ===================================================================

let rec lemma_sep_split_unique (a1 b1 a2 b2 : list char)
  : Lemma
    (requires count_sep a1 == 0 /\ count_sep a2 == 0 /\
              a1 @ (sep_char :: b1) == a2 @ (sep_char :: b2))
    (ensures a1 == a2 /\ b1 == b2)
    (decreases a1) =
  match a1, a2 with
  | [], [] -> ()
  | [], _ :: _ -> ()   // head of RHS is a2's head == sep_char, against count 0
  | _ :: _, [] -> ()   // symmetric
  | _ :: xs, _ :: ys -> lemma_sep_split_unique xs b1 ys b2

// ===================================================================
// 2. The key builders, decomposed and bridged.
// ===================================================================

// The subject's raw label (the part after the two-char tag).
let subj_label (s : subject) : string =
  match s with
  | S_IRI i -> i
  | S_BNode b -> b

let subj_label_sep_free (s : subject) : prop = str_sep_free (subj_label s)

// A separator-free label gives a separator-free subject key.
let lemma_subject_key_sep_free (s : subject)
  : Lemma (requires subj_label_sep_free s)
          (ensures str_sep_free (subject_to_key s)) =
  match s with
  | S_IRI i ->
    list_of_concat "I_" i;
    lemma_count_sep_append (list_of_string "I_") (list_of_string i);
    assert_norm (count_sep (list_of_string "I_") == 0)
  | S_BNode b ->
    list_of_concat "B_" b;
    lemma_count_sep_append (list_of_string "B_") (list_of_string b);
    assert_norm (count_sep (list_of_string "B_") == 0)

// subject_to_key is injective outright -- the two-char tag separates
// the constructors, and the label is carried whole.
let lemma_subject_to_key_injective (s1 s2 : subject)
  : Lemma (requires subject_to_key s1 == subject_to_key s2)
          (ensures s1 == s2) =
  match s1, s2 with
  | S_IRI i1, S_IRI i2 ->
    concat_injective "I_" "I_" i1 i2
  | S_BNode b1, S_BNode b2 ->
    concat_injective "B_" "B_" b1 b2
  | S_IRI i, S_BNode b ->
    list_of_concat "I_" i;
    list_of_concat "B_" b;
    assert_norm (list_of_string "I_" == ['I'; '_']);
    assert_norm (list_of_string "B_" == ['B'; '_']);
    assert_norm (('I' = 'B') == false)
  | S_BNode b, S_IRI i ->
    list_of_concat "B_" b;
    list_of_concat "I_" i;
    assert_norm (list_of_string "B_" == ['B'; '_']);
    assert_norm (list_of_string "I_" == ['I'; '_']);
    assert_norm (('B' = 'I') == false)

// sp_key's character-list decomposition: subject key, one separator,
// predicate.
let lemma_sp_key_decomposes (s : subject) (p : wf_iri)
  : Lemma (list_of_string (sp_key s p) ==
           list_of_string (subject_to_key s) @
           (sep_char :: list_of_string p)) =
  list_of_concat (subject_to_key s) (unit_sep ^ p);
  list_of_concat unit_sep p;
  assert_norm (list_of_string unit_sep == [sep_char])

// ===================================================================
// 3. The theorem: sp_key is injective as soon as ONE side is clean.
// ===================================================================

val sp_key_injective_one_sided
    (s1 : subject) (p1 : wf_iri) (s2 : subject) (p2 : wf_iri)
  : Lemma
    (requires subj_label_sep_free s1 /\ str_sep_free p1 /\
              sp_key s1 p1 == sp_key s2 p2)
    (ensures s1 == s2 /\ p1 == p2)

let sp_key_injective_one_sided s1 p1 s2 p2 =
  lemma_sp_key_decomposes s1 p1;
  lemma_sp_key_decomposes s2 p2;
  lemma_subject_key_sep_free s1;
  let a1 = list_of_string (subject_to_key s1) in
  let b1 = list_of_string p1 in
  let a2 = list_of_string (subject_to_key s2) in
  let b2 = list_of_string p2 in
  // Count the separators on both sides of the (equal) key lists: the
  // clean side counts exactly one, which forces a2 and b2 clean too.
  lemma_count_sep_append a1 (sep_char :: b1);
  lemma_count_sep_append a2 (sep_char :: b2);
  assert (count_sep a2 == 0 /\ count_sep b2 == 0);
  lemma_sep_split_unique a1 b1 a2 b2;
  // Lists back to strings, strings back to subjects.
  string_of_list_of_string (subject_to_key s1);
  string_of_list_of_string (subject_to_key s2);
  string_of_list_of_string p1;
  string_of_list_of_string p2;
  lemma_subject_to_key_injective s1 s2

// ===================================================================
// 4. Discharging ig_wf_sp for separator-free graphs.
// ===================================================================

// The side condition: every triple's subject label and predicate are
// separator-free. (Objects are irrelevant to the sp bucket.) Parser
// output always satisfies this -- is_iri_body_char requires code
// points above 0x20 -- but the condition is stated on the graph, not
// the parser, because ig_wf_sp's forall ranges over the type.
let graph_sp_sep_free (g : list triple) : prop =
  forall (t : triple). memP t g ==>
    subj_label_sep_free t.s /\ str_sep_free t.p

val lemma_build_indexed_wf_sp (g : rdf_graph)
  : Lemma (requires graph_sp_sep_free g)
          (ensures ig_wf_sp (build_indexed g))

let lemma_build_indexed_wf_sp g =
  lemma_build_indexed_wf_sp_weak g;
  let ig = build_indexed g in
  assert (ig.ig_triples == g);
  introduce forall (s : subject) (p : wf_iri) (t : triple).
      memP t (bucket_lookup ig.ig_sp (sp_key s p)) ==>
      (memP t ig.ig_triples /\ t.s == s /\ t.p == p)
  with introduce memP t (bucket_lookup ig.ig_sp (sp_key s p)) ==>
                 (memP t ig.ig_triples /\ t.s == s /\ t.p == p)
  with _ . begin
    // The weak form places t in the graph with its own key equal to
    // the queried key; t's side of the equation is clean by the side
    // condition, so injectivity recovers the components.
    assert (Some (sp_key s p) == bucket_key_sp t);
    sp_key_injective_one_sided t.s t.p s p
  end

// ===================================================================
// 5. A machine-checked instance (the issue's ask: a theorem nobody
// can instantiate carries no assurance until someone can).
// ===================================================================

// Decidable form of the side condition, so concrete instances close
// by normalization.
let rec count_sep_b (l : list char) : nat =
  match l with
  | [] -> 0
  | c :: rest -> (if c = sep_char then 1 else 0) + count_sep_b rest

let rec lemma_count_sep_b_eq (l : list char)
  : Lemma (count_sep_b l == count_sep l) =
  match l with
  | [] -> ()
  | _ :: rest -> lemma_count_sep_b_eq rest

let triple_sp_sep_free_b (t : triple) : bool =
  count_sep_b (list_of_string (subj_label t.s)) = 0 &&
  count_sep_b (list_of_string t.p) = 0

let rec graph_sp_sep_free_b (g : list triple) : bool =
  match g with
  | [] -> true
  | t :: rest -> triple_sp_sep_free_b t && graph_sp_sep_free_b rest

let rec lemma_graph_sp_sep_free_b_sound (g : list triple)
  : Lemma (requires graph_sp_sep_free_b g == true)
          (ensures graph_sp_sep_free g) =
  match g with
  | [] -> ()
  | t :: rest ->
    lemma_count_sep_b_eq (list_of_string (subj_label t.s));
    lemma_count_sep_b_eq (list_of_string t.p);
    lemma_graph_sp_sep_free_b_sound rest

// A concrete two-triple graph with a populated sp bucket.
let ki_p : wf_iri =
  assert_norm (is_iri "http://ex/p");
  "http://ex/p"
let ki_q : wf_iri =
  assert_norm (is_iri "http://ex/q");
  "http://ex/q"
let ki_a : subject = S_IRI ki_p
let ki_sample : rdf_graph = [
  ({ s = ki_a;        p = ki_p; o = T_IRI ki_q } <: triple);
  ({ s = S_BNode "b0"; p = ki_q; o = T_IRI ki_p } <: triple)
]

// The instance: ig_wf_sp holds of a real, non-empty indexed graph.
let theorem_wf_sp_nonempty_instance ()
  : Lemma (ig_wf_sp (build_indexed ki_sample)) =
  assert_norm (graph_sp_sep_free_b ki_sample == true);
  lemma_graph_sp_sep_free_b_sound ki_sample;
  lemma_build_indexed_wf_sp ki_sample

// ===================================================================
// 6. The subject bucket needs no side condition at all.
//
// bucket_key_subj t = Some (subject_to_key t.s), and subject_to_key
// is injective outright (section 2), so the weak membership form
// upgrades to full ig_wf_subj for EVERY graph -- no separator
// hypothesis. This is the discharge the eq-rep-* rule family's
// licensing lemmas consume.
// ===================================================================

val lemma_build_indexed_wf_subj (g : rdf_graph)
  : Lemma (ensures ig_wf_subj (build_indexed g))

let lemma_build_indexed_wf_subj g =
  lemma_build_indexed_wf_subj_weak g;
  let ig = build_indexed g in
  assert (ig.ig_triples == g);
  introduce forall (s : subject) (t : triple).
      memP t (bucket_lookup ig.ig_subj (subject_to_key s)) ==>
      (memP t ig.ig_triples /\ t.s == s)
  with introduce memP t (bucket_lookup ig.ig_subj (subject_to_key s)) ==>
                 (memP t ig.ig_triples /\ t.s == s)
  with _ . begin
    assert (Some (subject_to_key s) == bucket_key_subj t);
    lemma_subject_to_key_injective t.s s
  end

// ===================================================================
// 7. The object bucket needs no side condition either.
//
// bucket_key_obj t = term_to_key_opt t.o, and term_to_key_opt is now
// built with `^` (RDF.Indexed.fsti, matching subject_to_key's own
// rewrite), so it is injective outright on its non-None range by the
// same two-char-tag argument -- section 2's `lemma_subject_to_key_
// injective` proof, replayed one constructor pair at a time with the
// two extra all-None cases (T_Literal / T_TripleTerm) discharged by
// contradiction against `Some k`. This is the discharge the eq-rep-o
// rule's licensing lemma consumes, via the subject-shaped `ig_wf_obj`
// (OWL.Semantics) the rule actually queries with.
// ===================================================================

// term_to_key_opt is injective on the rdf_terms it actually keys
// (T_IRI / T_BNode); the literal/triple-term constructors always key
// to None, so the requires' `Some k` on both sides already rules them
// out (term_to_key_opt unfolds definitionally, so F* sees `None ==
// Some k` is False in those branches without any extra lemma).
val lemma_term_to_key_opt_injective (o1 o2 : rdf_term) (k : string)
  : Lemma (requires term_to_key_opt o1 == Some k /\ term_to_key_opt o2 == Some k)
          (ensures o1 == o2)

let lemma_term_to_key_opt_injective o1 o2 k =
  match o1, o2 with
  | T_IRI i1, T_IRI i2 ->
    concat_injective "I_" "I_" i1 i2
  | T_BNode b1, T_BNode b2 ->
    concat_injective "B_" "B_" b1 b2
  | T_IRI i, T_BNode b ->
    list_of_concat "I_" i;
    list_of_concat "B_" b;
    assert_norm (list_of_string "I_" == ['I'; '_']);
    assert_norm (list_of_string "B_" == ['B'; '_']);
    assert_norm (('I' = 'B') == false)
  | T_BNode b, T_IRI i ->
    list_of_concat "B_" b;
    list_of_concat "I_" i;
    assert_norm (list_of_string "B_" == ['B'; '_']);
    assert_norm (list_of_string "I_" == ['I'; '_']);
    assert_norm (('B' = 'I') == false)
  | T_Literal _, _ -> ()
  | T_TripleTerm _ _ _, _ -> ()
  | _, T_Literal _ -> ()
  | _, T_TripleTerm _ _ _ -> ()

// Bridge: a subject's key agrees with the term_to_key_opt of the term
// it converts to -- both reduce to the same "I_"^i / "B_"^b shape.
// Purely definitional (both sides are non-recursive `let`s), which is
// why the proof is just case analysis with no lemma calls.
let lemma_subject_to_key_eq_term_to_key_opt (s : subject)
  : Lemma (ensures term_to_key_opt (subject_to_term s) == Some (subject_to_key s)) =
  match s with
  | S_IRI _ -> ()
  | S_BNode _ -> ()

// The eq-rep-o discharge: every triple the object bucket serves up
// under a subject-shaped key is a real snapshot triple whose object
// is exactly the term that subject denotes.
val lemma_build_indexed_wf_obj (g : rdf_graph)
  : Lemma (ensures ig_wf_obj (build_indexed g))

let lemma_build_indexed_wf_obj g =
  lemma_build_indexed_wf_obj_weak g;
  let ig = build_indexed g in
  assert (ig.ig_triples == g);
  introduce forall (s : subject) (t : triple).
      memP t (bucket_lookup ig.ig_obj (subject_to_key s)) ==>
      (memP t ig.ig_triples /\ t.o == subject_to_term s)
  with introduce memP t (bucket_lookup ig.ig_obj (subject_to_key s)) ==>
                 (memP t ig.ig_triples /\ t.o == subject_to_term s)
  with _ . begin
    assert (Some (subject_to_key s) == bucket_key_obj t);
    lemma_subject_to_key_eq_term_to_key_opt s;
    lemma_term_to_key_opt_injective t.o (subject_to_term s) (subject_to_key s)
  end

// ===================================================================
// 8. The predicate-object bucket: po_key_opt is a COMPOSITE key
// (predicate ^ separator ^ object-key) like sp_key (section 3), not a
// single-component key like subject_to_key / term_to_key_opt (sections
// 6/7) -- so it needs the SAME one-sided separator-free side condition
// sp_key's discharge does, roles mirrored (prefix = predicate, suffix
// = object-key, where sp_key's prefix/suffix were subject-key/
// predicate). This is the discharge OWL.RL.Refinement's
// owl_rule_inverse_functional_licensed consumes, via the subject-
// shaped `ig_wf_po` (OWL.Semantics) it actually queries with -- the
// same subject-shaped trick section 7 used for `ig_wf_obj` (po_key_opt
// is only ever `Some` on a non-literal object, and prp-ifp's
// `find_subjects_indexed` only reaches ig_po in that case).
// ===================================================================

// Bridge: po_key_opt agrees with po_key (RDF.Indexed.fsti) on the
// subject-shaped object -- both reduce to the same "p ^ sep ^ I_/B_"
// shape, purely definitional (mirroring
// lemma_subject_to_key_eq_term_to_key_opt's own one-line proof).
let lemma_po_key_eq_po_key_opt (p : wf_iri) (s : subject)
  : Lemma (ensures po_key_opt p (subject_to_term s) == Some (po_key p s)) =
  lemma_subject_to_key_eq_term_to_key_opt s

// Half-inverse: recovering a subject from a term pins the term. Same
// statement as OWL.RL.Refinement's own restatement of this fact
// (`lemma_term_to_subject_subj_term`); restated here so this module
// does not depend on the Refinement layer.
let lemma_term_to_subject_roundtrip (t : rdf_term) (s : subject)
  : Lemma (requires term_to_subject t == Some s)
          (ensures subject_to_term s == t) =
  match t with
  | T_IRI _ -> ()
  | T_BNode _ -> ()
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

// po_key_opt p o is `Some` on exactly the terms term_to_subject
// recognises (T_IRI / T_BNode); both give None on T_Literal /
// T_TripleTerm. Direct (no term_to_key_opt hop) so a proof that
// matches on term_to_subject knows immediately which way po_key_opt
// (and OWL.RL.Refinement's `find_subjects_indexed` callers) went --
// used both to rule out the "object doesn't convert" case below and
// by OWL.RL.Refinement's prp-ifp licensing proof (section 16).
let lemma_po_key_opt_some_iff_term_to_subject_some (p : wf_iri) (o : rdf_term)
  : Lemma (ensures Some? (po_key_opt p o) == Some? (term_to_subject o)) =
  match o with
  | T_IRI _ -> ()
  | T_BNode _ -> ()
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

// po_key's character-list decomposition: predicate, one separator,
// subject key -- the mirror image of sp_key_decomposes (section 3),
// prefix and suffix roles swapped.
let lemma_po_key_decomposes (p : wf_iri) (s : subject)
  : Lemma (list_of_string (po_key p s) ==
           list_of_string p @ (sep_char :: list_of_string (subject_to_key s))) =
  list_of_concat p (unit_sep ^ subject_to_key s);
  list_of_concat unit_sep (subject_to_key s);
  assert_norm (list_of_string unit_sep == [sep_char])

val po_key_injective_one_sided
    (p1 : wf_iri) (s1 : subject) (p2 : wf_iri) (s2 : subject)
  : Lemma
    (requires str_sep_free p1 /\ subj_label_sep_free s1 /\
              po_key p1 s1 == po_key p2 s2)
    (ensures p1 == p2 /\ s1 == s2)

let po_key_injective_one_sided p1 s1 p2 s2 =
  lemma_po_key_decomposes p1 s1;
  lemma_po_key_decomposes p2 s2;
  lemma_subject_key_sep_free s1;
  let a1 = list_of_string p1 in
  let b1 = list_of_string (subject_to_key s1) in
  let a2 = list_of_string p2 in
  let b2 = list_of_string (subject_to_key s2) in
  lemma_count_sep_append a1 (sep_char :: b1);
  lemma_count_sep_append a2 (sep_char :: b2);
  assert (count_sep a2 == 0 /\ count_sep b2 == 0);
  lemma_sep_split_unique a1 b1 a2 b2;
  string_of_list_of_string p1;
  string_of_list_of_string p2;
  string_of_list_of_string (subject_to_key s1);
  string_of_list_of_string (subject_to_key s2);
  lemma_subject_to_key_injective s1 s2

// The side condition: every triple's predicate is separator-free, and
// when its object converts to a subject (the only case ig_po files it
// under), that subject's label is separator-free too. Mirrors
// graph_sp_sep_free (section 4); a triple whose object does NOT
// convert (literal/triple-term) imposes no condition since ig_po never
// files it.
let graph_po_sep_free (g : list triple) : prop =
  forall (t : triple). memP t g ==>
    str_sep_free t.p /\
    (match term_to_subject t.o with
     | Some s -> subj_label_sep_free s
     | None -> True)

val lemma_build_indexed_wf_po (g : rdf_graph)
  : Lemma (requires graph_po_sep_free g)
          (ensures ig_wf_po (build_indexed g))

let lemma_build_indexed_wf_po g =
  lemma_build_indexed_wf_po_weak g;
  let ig = build_indexed g in
  assert (ig.ig_triples == g);
  introduce forall (p : wf_iri) (s : subject) (t : triple).
      memP t (bucket_lookup ig.ig_po (po_key p s)) ==>
      (memP t ig.ig_triples /\ t.p == p /\ t.o == subject_to_term s)
  with introduce memP t (bucket_lookup ig.ig_po (po_key p s)) ==>
                 (memP t ig.ig_triples /\ t.p == p /\ t.o == subject_to_term s)
  with _ . begin
    // The weak form places t in the graph with its own key equal to
    // the queried key. t's own key is `bucket_key_po t == po_key_opt
    // t.p t.o`, which is `Some` here, so t.o converts to a subject
    // t_s; the queried side (p, s) is clean by the side condition, so
    // injectivity recovers the components.
    assert (Some (po_key p s) == bucket_key_po t);
    assert (Some (po_key p s) == po_key_opt t.p t.o);
    lemma_po_key_opt_some_iff_term_to_subject_some t.p t.o;
    match term_to_subject t.o with
    | Some t_s ->
      lemma_term_to_subject_roundtrip t.o t_s;
      lemma_po_key_eq_po_key_opt t.p t_s;
      po_key_injective_one_sided t.p t_s p s
    | None -> ()
  end

// ===================================================================
// 9. #348: literal-arm injectivity for `term_to_key_total`, and full
// `triple_to_key` injectivity on separator-free triples.
//
// `term_to_key_total` (RDF.Graph.fsti) extends `term_to_key_opt` with a
// literal branch and a triple-term branch built RECURSIVELY through it.
// #348 found the literal branch folded lexical_form/datatype/lang tag/
// direction with a plain "^^" TEXT join and NO separator at all between
// datatype, lang tag, and direction -- a collision surface WIDER than
// sp_key's (#338): e.g. a `datatype` IRI containing a literal `'@'`
// (legal in an IRI's `ireg-name`/`iuserinfo`, RFC 3987) could collide
// with a shorter datatype plus a language tag. RDF.Graph.fsti's fix
// joins every part with `unit_sep`, built with `^` (not the opaque
// `String.concat`), so this section's separator-counting toolkit
// (sections 0/1 above) applies to it exactly as it does to sp_key/po_key.
//
// SIDE CONDITION. `term_sep_free` extends `str_sep_free` recursively
// over an `rdf_term`: an IRI/bnode's label clean, a literal's lexical
// form + datatype + (if present) language tag clean (`literal_sep_free`),
// or a triple term's subject label + predicate clean AND its object
// clean by the same recursive condition. `direction` needs NO side
// condition -- its key contribution (`RDF.Graph.lit_key_dir_part`) is
// one of three FIXED ASCII strings, distinguished by direct string
// comparison, not separator counting.
//
// SHAPE OF THE PROOF, TWO-SIDED (not one-sided like sp_key/po_key
// above): `no_dup_keys`'s two triples are both drawn from the SAME
// separator-free graph, so both sides' cleanliness is available
// directly from the caller's hypothesis -- no need for sp_key's
// "derive the other side's count from the total" trick. Each level
// peels one component with `lemma_sep_split_unique`, applied to BOTH
// `a1` and `a2` (re-read section 1's signature: it needs `count_sep a1
// == 0 /\ count_sep a2 == 0`, NO constraint on `b1`/`b2`, so the "rest"
// may itself contain further separators -- exactly what lets this
// compose through `triple_to_key`'s 3-part shape and the literal key's
// 4-part shape without a generalised n-ary version of the lemma).
// ===================================================================

// The literal side condition. `direction` excluded (see banner).
let literal_sep_free (l : literal) : prop =
  str_sep_free l.lexical_form /\ str_sep_free l.datatype /\
  (match l.lang_tag with | Some t -> str_sep_free t | None -> True)

// Decidable companion, mirroring `count_sep_b`/`graph_sp_sep_free_b`'s
// own soundness pattern (section 5) -- needed so
// `RDF.Entailment.RDFS.SepFree`'s `obj_label_sep_free_b` (extended for
// #348 in that module) has a literal-content checker to call.
let literal_sep_free_b (l : literal) : bool =
  count_sep_b (list_of_string l.lexical_form) = 0 &&
  count_sep_b (list_of_string l.datatype) = 0 &&
  (match l.lang_tag with | Some t -> count_sep_b (list_of_string t) = 0 | None -> true)

let lemma_literal_sep_free_b_sound (l : literal)
  : Lemma (requires literal_sep_free_b l == true)
          (ensures literal_sep_free l) =
  lemma_count_sep_b_eq (list_of_string l.lexical_form);
  lemma_count_sep_b_eq (list_of_string l.datatype);
  (match l.lang_tag with
   | Some t -> lemma_count_sep_b_eq (list_of_string t)
   | None -> ())

// The full recursive rdf_term side condition `term_to_key_total`
// injectivity needs.
let rec term_sep_free (o : rdf_term) : Tot prop (decreases o) =
  match o with
  | T_IRI i -> str_sep_free i
  | T_BNode b -> str_sep_free b
  | T_Literal l -> literal_sep_free l
  | T_TripleTerm s p obj -> subj_label_sep_free s /\ str_sep_free p /\ term_sep_free obj

// ===================================================================
// 9a. The literal key's list_of_string decomposition, one level at a
// time -- three nested `a ^ (unit_sep ^ rest)` splits, mirroring
// `lemma_sp_key_decomposes`/`lemma_po_key_decomposes` (sections 3/8)
// but chained instead of single-shot, since the literal key has four
// parts (three internal separators) where sp_key/po_key have two.
// ===================================================================

let lemma_literal_key_decomposes_1 (l : wf_literal)
  : Lemma (list_of_string (term_to_key_total (T_Literal l)) ==
           list_of_string ("L_" ^ l.lexical_form) @
           (sep_char :: list_of_string
             (l.datatype ^ (unit_sep ^
               (lit_key_lang_part l ^ (unit_sep ^ lit_key_dir_part l)))))) =
  list_of_concat ("L_" ^ l.lexical_form)
    (unit_sep ^ (l.datatype ^ (unit_sep ^
      (lit_key_lang_part l ^ (unit_sep ^ lit_key_dir_part l)))));
  list_of_concat unit_sep (l.datatype ^ (unit_sep ^
    (lit_key_lang_part l ^ (unit_sep ^ lit_key_dir_part l))));
  assert_norm (list_of_string unit_sep == [sep_char])

let lemma_literal_key_decomposes_2 (l : literal)
  : Lemma (list_of_string
             (l.datatype ^ (unit_sep ^ (lit_key_lang_part l ^ (unit_sep ^ lit_key_dir_part l)))) ==
           list_of_string l.datatype @
           (sep_char :: list_of_string (lit_key_lang_part l ^ (unit_sep ^ lit_key_dir_part l)))) =
  list_of_concat l.datatype (unit_sep ^ (lit_key_lang_part l ^ (unit_sep ^ lit_key_dir_part l)));
  list_of_concat unit_sep (lit_key_lang_part l ^ (unit_sep ^ lit_key_dir_part l));
  assert_norm (list_of_string unit_sep == [sep_char])

let lemma_literal_key_decomposes_3 (l : literal)
  : Lemma (list_of_string (lit_key_lang_part l ^ (unit_sep ^ lit_key_dir_part l)) ==
           list_of_string (lit_key_lang_part l) @ (sep_char :: list_of_string (lit_key_dir_part l))) =
  list_of_concat (lit_key_lang_part l) (unit_sep ^ lit_key_dir_part l);
  list_of_concat unit_sep (lit_key_dir_part l);
  assert_norm (list_of_string unit_sep == [sep_char])

// `"L_" ^ lexical_form` is separator-free exactly when `lexical_form`
// is (the "L_" tag itself is two plain ASCII chars) -- mirrors
// `lemma_subject_key_sep_free`'s "I_"/"B_" argument (section 2).
let lemma_literal_prefix_sep_free (l : literal)
  : Lemma (requires str_sep_free l.lexical_form)
          (ensures str_sep_free ("L_" ^ l.lexical_form)) =
  list_of_concat "L_" l.lexical_form;
  lemma_count_sep_append (list_of_string "L_") (list_of_string l.lexical_form);
  assert_norm (count_sep (list_of_string "L_") == 0)

// `lit_key_lang_part` is separator-free whenever the underlying tag
// (when present) is -- the "@" marker contributes zero separators.
let lemma_lit_key_lang_part_sep_free (l : literal)
  : Lemma (requires (match l.lang_tag with | Some t -> str_sep_free t | None -> True))
          (ensures str_sep_free (lit_key_lang_part l)) =
  match l.lang_tag with
  | None ->
    // `list_of_string` is opaque to Z3 outside the normalizer (it is a
    // primitive `val`, no SMT equations) -- `assert_norm` on the WRAPPED
    // `str_sep_free ""` (not the unwrapped `count_sep (list_of_string
    // "") == 0`) is what actually forces the normalizer to close the
    // literal case; the unwrapped form leaves nothing SMT can reuse to
    // discharge the `str_sep_free (lit_key_lang_part l)` goal below.
    assert (lit_key_lang_part l == "");
    assert_norm (str_sep_free "")
  | Some t ->
    assert (lit_key_lang_part l == "@" ^ t);
    list_of_concat "@" t;
    lemma_count_sep_append (list_of_string "@") (list_of_string t);
    assert_norm (count_sep (list_of_string "@") == 0)

// `lit_key_dir_part l` uniquely determines `l.direction`: the three
// possible values are FIXED, pairwise-distinct ASCII strings, so
// equality of the strings decides equality of the `option
// text_direction` by direct case split + `assert_norm`.
let lemma_lit_key_dir_part_injective (l1 l2 : literal)
  : Lemma (requires lit_key_dir_part l1 == lit_key_dir_part l2)
          (ensures l1.direction == l2.direction) =
  match l1.direction, l2.direction with
  | None, None -> ()
  | Some Dir_LTR, Some Dir_LTR -> ()
  | Some Dir_RTL, Some Dir_RTL -> ()
  | None, Some Dir_LTR -> assert_norm (("" = "--ltr") == false)
  | None, Some Dir_RTL -> assert_norm (("" = "--rtl") == false)
  | Some Dir_LTR, None -> assert_norm (("--ltr" = "") == false)
  | Some Dir_RTL, None -> assert_norm (("--rtl" = "") == false)
  | Some Dir_LTR, Some Dir_RTL -> assert_norm (("--ltr" = "--rtl") == false)
  | Some Dir_RTL, Some Dir_LTR -> assert_norm (("--rtl" = "--ltr") == false)

// `lit_key_lang_part` similarly determines `l.lang_tag` -- `""` has
// length 0 (impossible for a "@"-prefixed string, length >= 1), and
// for two "Some" tags `concat_injective` recovers the tag from the
// fixed-length "@" prefix (same trick section 2 uses for "I_"/"B_").
let lemma_lit_key_lang_part_injective (l1 l2 : literal)
  : Lemma (requires lit_key_lang_part l1 == lit_key_lang_part l2)
          (ensures l1.lang_tag == l2.lang_tag) =
  match l1.lang_tag, l2.lang_tag with
  | None, None -> ()
  | Some t1, Some t2 ->
    assert (lit_key_lang_part l1 == "@" ^ t1);
    assert (lit_key_lang_part l2 == "@" ^ t2);
    concat_injective "@" "@" t1 t2
  | None, Some t2 ->
    assert (lit_key_lang_part l1 == "");
    assert (lit_key_lang_part l2 == "@" ^ t2);
    assert_norm (FStar.String.length "" == 0);
    assert_norm (FStar.String.length "@" == 1);
    concat_length "@" t2
  | Some t1, None ->
    assert (lit_key_lang_part l1 == "@" ^ t1);
    assert (lit_key_lang_part l2 == "");
    assert_norm (FStar.String.length "" == 0);
    assert_norm (FStar.String.length "@" == 1);
    concat_length "@" t1

// ===================================================================
// 9b. The literal-arm injectivity theorem -- section 5's harvest ask,
// scoped to #348: `term_to_key_total (T_Literal l1) ==
// term_to_key_total (T_Literal l2)` under a separator-free side
// condition on BOTH literals forces `l1 == l2`.
// ===================================================================

val lemma_literal_key_injective (l1 l2 : wf_literal)
  : Lemma (requires literal_sep_free l1 /\ literal_sep_free l2 /\
                     term_to_key_total (T_Literal l1) == term_to_key_total (T_Literal l2))
          (ensures l1 == l2)

let lemma_literal_key_injective l1 l2 =
  lemma_literal_key_decomposes_1 l1;
  lemma_literal_key_decomposes_1 l2;
  lemma_literal_prefix_sep_free l1;
  lemma_literal_prefix_sep_free l2;
  let pfx1 = list_of_string ("L_" ^ l1.lexical_form) in
  let rest1 = list_of_string (l1.datatype ^ (unit_sep ^
    (lit_key_lang_part l1 ^ (unit_sep ^ lit_key_dir_part l1)))) in
  let pfx2 = list_of_string ("L_" ^ l2.lexical_form) in
  let rest2 = list_of_string (l2.datatype ^ (unit_sep ^
    (lit_key_lang_part l2 ^ (unit_sep ^ lit_key_dir_part l2)))) in
  lemma_sep_split_unique pfx1 rest1 pfx2 rest2;
  string_of_list_of_string ("L_" ^ l1.lexical_form);
  string_of_list_of_string ("L_" ^ l2.lexical_form);
  concat_injective "L_" "L_" l1.lexical_form l2.lexical_form;
  string_of_list_of_string
    (l1.datatype ^ (unit_sep ^ (lit_key_lang_part l1 ^ (unit_sep ^ lit_key_dir_part l1))));
  string_of_list_of_string
    (l2.datatype ^ (unit_sep ^ (lit_key_lang_part l2 ^ (unit_sep ^ lit_key_dir_part l2))));
  // Level 2: peel `datatype` off the shared remainder.
  lemma_literal_key_decomposes_2 l1;
  lemma_literal_key_decomposes_2 l2;
  let dpfx1 = list_of_string l1.datatype in
  let drest1 = list_of_string (lit_key_lang_part l1 ^ (unit_sep ^ lit_key_dir_part l1)) in
  let dpfx2 = list_of_string l2.datatype in
  let drest2 = list_of_string (lit_key_lang_part l2 ^ (unit_sep ^ lit_key_dir_part l2)) in
  lemma_sep_split_unique dpfx1 drest1 dpfx2 drest2;
  string_of_list_of_string l1.datatype;
  string_of_list_of_string l2.datatype;
  string_of_list_of_string (lit_key_lang_part l1 ^ (unit_sep ^ lit_key_dir_part l1));
  string_of_list_of_string (lit_key_lang_part l2 ^ (unit_sep ^ lit_key_dir_part l2));
  // Level 3: peel the language-tag suffix off the final remainder.
  lemma_literal_key_decomposes_3 l1;
  lemma_literal_key_decomposes_3 l2;
  lemma_lit_key_lang_part_sep_free l1;
  lemma_lit_key_lang_part_sep_free l2;
  let lpfx1 = list_of_string (lit_key_lang_part l1) in
  let lrest1 = list_of_string (lit_key_dir_part l1) in
  let lpfx2 = list_of_string (lit_key_lang_part l2) in
  let lrest2 = list_of_string (lit_key_dir_part l2) in
  lemma_sep_split_unique lpfx1 lrest1 lpfx2 lrest2;
  string_of_list_of_string (lit_key_lang_part l1);
  string_of_list_of_string (lit_key_lang_part l2);
  string_of_list_of_string (lit_key_dir_part l1);
  string_of_list_of_string (lit_key_dir_part l2);
  lemma_lit_key_lang_part_injective l1 l2;
  lemma_lit_key_dir_part_injective l1 l2;
  assert (l1.lexical_form == l2.lexical_form);
  assert (l1.datatype == l2.datatype);
  assert (l1.lang_tag == l2.lang_tag);
  assert (l1.direction == l2.direction)

// ===================================================================
// 9c. Full `term_to_key_total` injectivity across all four `rdf_term`
// constructors. Same-constructor pairs recurse into 9b (literal),
// replay section 2/7's "I_"/"B_" tag argument (IRI/bnode), or a fresh
// two-level split (triple term, mirroring sp_key/po_key). Different-
// constructor pairs are ruled out by comparing the key's first TWO
// characters -- each constructor's tag ("I_"/"B_"/"L_"/"T_") is
// distinct, same technique as `lemma_subject_to_key_injective`'s own
// cross-constructor cases (section 2), replayed here pairwise.
// ===================================================================

let lemma_triple_term_key_decomposes_1 (s : subject) (p : wf_iri) (obj : rdf_term)
  : Lemma (list_of_string (term_to_key_total (T_TripleTerm s p obj)) ==
           list_of_string ("T_" ^ subject_to_key s) @
           (sep_char :: list_of_string (p ^ (unit_sep ^ term_to_key_total obj)))) =
  list_of_concat ("T_" ^ subject_to_key s) (unit_sep ^ (p ^ (unit_sep ^ term_to_key_total obj)));
  list_of_concat unit_sep (p ^ (unit_sep ^ term_to_key_total obj));
  assert_norm (list_of_string unit_sep == [sep_char])

let lemma_triple_term_key_decomposes_2 (p : wf_iri) (obj : rdf_term)
  : Lemma (list_of_string (p ^ (unit_sep ^ term_to_key_total obj)) ==
           list_of_string p @ (sep_char :: list_of_string (term_to_key_total obj))) =
  list_of_concat p (unit_sep ^ term_to_key_total obj);
  list_of_concat unit_sep (term_to_key_total obj);
  assert_norm (list_of_string unit_sep == [sep_char])

// `"T_" ^ subject_to_key s` is separator-free exactly when
// `subject_to_key s` is -- mirrors `lemma_literal_prefix_sep_free`'s
// "L_" argument above (itself mirroring section 2's "I_"/"B_" one).
let lemma_triple_term_prefix_sep_free (s : subject)
  : Lemma (requires str_sep_free (subject_to_key s))
          (ensures str_sep_free ("T_" ^ subject_to_key s)) =
  list_of_concat "T_" (subject_to_key s);
  lemma_count_sep_append (list_of_string "T_") (list_of_string (subject_to_key s));
  assert_norm (count_sep (list_of_string "T_") == 0)

#push-options "--z3rlimit 120"
let rec lemma_term_to_key_total_injective (o1 o2 : rdf_term)
  : Lemma (requires term_sep_free o1 /\ term_sep_free o2 /\
                     term_to_key_total o1 == term_to_key_total o2)
          (ensures o1 == o2)
    (decreases o1) =
  match o1, o2 with
  | T_IRI i1, T_IRI i2 -> concat_injective "I_" "I_" i1 i2
  | T_BNode b1, T_BNode b2 -> concat_injective "B_" "B_" b1 b2
  | T_Literal l1, T_Literal l2 -> lemma_literal_key_injective l1 l2
  | T_TripleTerm s1 p1 obj1, T_TripleTerm s2 p2 obj2 ->
    lemma_triple_term_key_decomposes_1 s1 p1 obj1;
    lemma_triple_term_key_decomposes_1 s2 p2 obj2;
    lemma_subject_key_sep_free s1;
    lemma_subject_key_sep_free s2;
    lemma_triple_term_prefix_sep_free s1;
    lemma_triple_term_prefix_sep_free s2;
    let a1 = list_of_string ("T_" ^ subject_to_key s1) in
    let b1 = list_of_string (p1 ^ (unit_sep ^ term_to_key_total obj1)) in
    let a2 = list_of_string ("T_" ^ subject_to_key s2) in
    let b2 = list_of_string (p2 ^ (unit_sep ^ term_to_key_total obj2)) in
    lemma_sep_split_unique a1 b1 a2 b2;
    string_of_list_of_string ("T_" ^ subject_to_key s1);
    string_of_list_of_string ("T_" ^ subject_to_key s2);
    concat_injective "T_" "T_" (subject_to_key s1) (subject_to_key s2);
    lemma_subject_to_key_injective s1 s2;
    string_of_list_of_string (p1 ^ (unit_sep ^ term_to_key_total obj1));
    string_of_list_of_string (p2 ^ (unit_sep ^ term_to_key_total obj2));
    lemma_triple_term_key_decomposes_2 p1 obj1;
    lemma_triple_term_key_decomposes_2 p2 obj2;
    let c1 = list_of_string p1 in
    let d1 = list_of_string (term_to_key_total obj1) in
    let c2 = list_of_string p2 in
    let d2 = list_of_string (term_to_key_total obj2) in
    lemma_sep_split_unique c1 d1 c2 d2;
    string_of_list_of_string p1;
    string_of_list_of_string p2;
    string_of_list_of_string (term_to_key_total obj1);
    string_of_list_of_string (term_to_key_total obj2);
    lemma_term_to_key_total_injective obj1 obj2
  // Cross-constructor pairs: the key's first two characters differ
  // ("I_"/"B_"/"L_"/"T_"), so the equal-key hypothesis is contradictory.
  | T_IRI i1, T_BNode b2 ->
    list_of_concat "I_" i1; list_of_concat "B_" b2;
    assert_norm (list_of_string "I_" == ['I'; '_']);
    assert_norm (list_of_string "B_" == ['B'; '_']);
    assert_norm (('I' = 'B') == false)
  | T_BNode b1, T_IRI i2 ->
    list_of_concat "B_" b1; list_of_concat "I_" i2;
    assert_norm (list_of_string "B_" == ['B'; '_']);
    assert_norm (list_of_string "I_" == ['I'; '_']);
    assert_norm (('B' = 'I') == false)
  | T_IRI i1, T_Literal l2 ->
    list_of_concat "I_" i1; lemma_literal_key_decomposes_1 l2; list_of_concat "L_" l2.lexical_form;
    assert_norm (list_of_string "I_" == ['I'; '_']);
    assert_norm (list_of_string "L_" == ['L'; '_']);
    assert_norm (('I' = 'L') == false)
  | T_Literal l1, T_IRI i2 ->
    lemma_literal_key_decomposes_1 l1; list_of_concat "L_" l1.lexical_form; list_of_concat "I_" i2;
    assert_norm (list_of_string "L_" == ['L'; '_']);
    assert_norm (list_of_string "I_" == ['I'; '_']);
    assert_norm (('L' = 'I') == false)
  | T_IRI i1, T_TripleTerm s2 p2 obj2 ->
    list_of_concat "I_" i1;
    lemma_triple_term_key_decomposes_1 s2 p2 obj2; list_of_concat "T_" (subject_to_key s2);
    assert_norm (list_of_string "I_" == ['I'; '_']);
    assert_norm (list_of_string "T_" == ['T'; '_']);
    assert_norm (('I' = 'T') == false)
  | T_TripleTerm s1 p1 obj1, T_IRI i2 ->
    lemma_triple_term_key_decomposes_1 s1 p1 obj1; list_of_concat "T_" (subject_to_key s1);
    list_of_concat "I_" i2;
    assert_norm (list_of_string "T_" == ['T'; '_']);
    assert_norm (list_of_string "I_" == ['I'; '_']);
    assert_norm (('T' = 'I') == false)
  | T_BNode b1, T_Literal l2 ->
    list_of_concat "B_" b1; lemma_literal_key_decomposes_1 l2; list_of_concat "L_" l2.lexical_form;
    assert_norm (list_of_string "B_" == ['B'; '_']);
    assert_norm (list_of_string "L_" == ['L'; '_']);
    assert_norm (('B' = 'L') == false)
  | T_Literal l1, T_BNode b2 ->
    lemma_literal_key_decomposes_1 l1; list_of_concat "L_" l1.lexical_form; list_of_concat "B_" b2;
    assert_norm (list_of_string "L_" == ['L'; '_']);
    assert_norm (list_of_string "B_" == ['B'; '_']);
    assert_norm (('L' = 'B') == false)
  | T_BNode b1, T_TripleTerm s2 p2 obj2 ->
    list_of_concat "B_" b1;
    lemma_triple_term_key_decomposes_1 s2 p2 obj2; list_of_concat "T_" (subject_to_key s2);
    assert_norm (list_of_string "B_" == ['B'; '_']);
    assert_norm (list_of_string "T_" == ['T'; '_']);
    assert_norm (('B' = 'T') == false)
  | T_TripleTerm s1 p1 obj1, T_BNode b2 ->
    lemma_triple_term_key_decomposes_1 s1 p1 obj1; list_of_concat "T_" (subject_to_key s1);
    list_of_concat "B_" b2;
    assert_norm (list_of_string "T_" == ['T'; '_']);
    assert_norm (list_of_string "B_" == ['B'; '_']);
    assert_norm (('T' = 'B') == false)
  | T_Literal l1, T_TripleTerm s2 p2 obj2 ->
    lemma_literal_key_decomposes_1 l1; list_of_concat "L_" l1.lexical_form;
    lemma_triple_term_key_decomposes_1 s2 p2 obj2; list_of_concat "T_" (subject_to_key s2);
    assert_norm (list_of_string "L_" == ['L'; '_']);
    assert_norm (list_of_string "T_" == ['T'; '_']);
    assert_norm (('L' = 'T') == false)
  | T_TripleTerm s1 p1 obj1, T_Literal l2 ->
    lemma_triple_term_key_decomposes_1 s1 p1 obj1; list_of_concat "T_" (subject_to_key s1);
    lemma_literal_key_decomposes_1 l2; list_of_concat "L_" l2.lexical_form;
    assert_norm (list_of_string "T_" == ['T'; '_']);
    assert_norm (list_of_string "L_" == ['L'; '_']);
    assert_norm (('T' = 'L') == false)
#pop-options

// ===================================================================
// 9d. `triple_to_key` injectivity on separator-free triples, and the
// `no_dup_keys`-shaped graph corollary
// `RDF.Entailment.RDFS.FixedPoint.lemma_len_eq_saturated_sep_free`
// (Gap A) instantiates against the pre-dedup intermediate graph.
// ===================================================================

let triple_full_sep_free (t : triple) : prop =
  subj_label_sep_free t.s /\ str_sep_free t.p /\ term_sep_free t.o

#push-options "--z3rlimit 100"
val lemma_triple_to_key_injective (t1 t2 : triple)
  : Lemma (requires triple_full_sep_free t1 /\ triple_full_sep_free t2 /\
                     triple_to_key t1 == triple_to_key t2)
          (ensures t1 == t2)

let lemma_triple_to_key_injective t1 t2 =
  lemma_subject_key_sep_free t1.s;
  lemma_subject_key_sep_free t2.s;
  list_of_concat (subject_to_key t1.s) (unit_sep ^ (t1.p ^ (unit_sep ^ term_to_key_total t1.o)));
  list_of_concat unit_sep (t1.p ^ (unit_sep ^ term_to_key_total t1.o));
  list_of_concat (subject_to_key t2.s) (unit_sep ^ (t2.p ^ (unit_sep ^ term_to_key_total t2.o)));
  list_of_concat unit_sep (t2.p ^ (unit_sep ^ term_to_key_total t2.o));
  assert_norm (list_of_string unit_sep == [sep_char]);
  let a1 = list_of_string (subject_to_key t1.s) in
  let b1 = list_of_string (t1.p ^ (unit_sep ^ term_to_key_total t1.o)) in
  let a2 = list_of_string (subject_to_key t2.s) in
  let b2 = list_of_string (t2.p ^ (unit_sep ^ term_to_key_total t2.o)) in
  lemma_sep_split_unique a1 b1 a2 b2;
  string_of_list_of_string (subject_to_key t1.s);
  string_of_list_of_string (subject_to_key t2.s);
  lemma_subject_to_key_injective t1.s t2.s;
  string_of_list_of_string (t1.p ^ (unit_sep ^ term_to_key_total t1.o));
  string_of_list_of_string (t2.p ^ (unit_sep ^ term_to_key_total t2.o));
  // Second split: predicate off the shared remainder.
  assert (str_sep_free t1.p);
  assert (str_sep_free t2.p);
  list_of_concat t1.p (unit_sep ^ term_to_key_total t1.o);
  list_of_concat t2.p (unit_sep ^ term_to_key_total t2.o);
  list_of_concat unit_sep (term_to_key_total t1.o);
  list_of_concat unit_sep (term_to_key_total t2.o);
  let c1 = list_of_string t1.p in
  let d1 = list_of_string (term_to_key_total t1.o) in
  let c2 = list_of_string t2.p in
  let d2 = list_of_string (term_to_key_total t2.o) in
  lemma_sep_split_unique c1 d1 c2 d2;
  string_of_list_of_string t1.p;
  string_of_list_of_string t2.p;
  string_of_list_of_string (term_to_key_total t1.o);
  string_of_list_of_string (term_to_key_total t2.o);
  lemma_term_to_key_total_injective t1.o t2.o;
  assert (t1.s == t2.s);
  assert (t1.p == t2.p);
  assert (t1.o == t2.o)
#pop-options

// The graph-level side condition and the `no_dup_keys`-shaped payoff.
// Stated WITHOUT reference to `RDF.Entailment.RDFS.FixedPoint.no_dup_keys`
// by name (this module sits below it in the dependency order) -- the
// `ensures` below is definitionally the same `forall`, so a caller in
// that module discharges its own `no_dup_keys h` by unfolding.
let graph_full_sep_free (g : list triple) : prop =
  forall (t : triple). memP t g ==> triple_full_sep_free t

val lemma_graph_full_sep_free_no_dup_keys (g : list triple)
  : Lemma (requires graph_full_sep_free g)
          (ensures forall (t1 t2 : triple).
             memP t1 g /\ memP t2 g /\ triple_to_key t1 == triple_to_key t2 ==> t1 == t2)

let lemma_graph_full_sep_free_no_dup_keys g =
  introduce forall (t1 t2 : triple).
      memP t1 g /\ memP t2 g /\ triple_to_key t1 == triple_to_key t2 ==> t1 == t2
  with introduce memP t1 g /\ memP t2 g /\ triple_to_key t1 == triple_to_key t2 ==> t1 == t2
  with _ . lemma_triple_to_key_injective t1 t2
