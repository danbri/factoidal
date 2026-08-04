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
