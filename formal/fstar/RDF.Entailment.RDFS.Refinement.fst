module RDF.Entailment.RDFS.Refinement

// ===================================================================
// REFINEMENT: the SHIPPING RDF / RDFS closure rules against the
// declarative rule tables of RDF.Entailment.RDF.Spec.fst and
// RDF.Entailment.RDFS.Spec.fst.
//
// Every theorem below names a function the engine actually runs
// (RDFS.Closure.fsti's `rdf_property_axiom_closure`, `rdfs_rule_*`,
// `rdfs_closure_step`, `rdfs_closure`, `rdfs_reflexivity_axioms`,
// `rdfs_closure_with_reflexivity`) -- not a model or transcription of
// it. Verify-only proof layer; no shipping module is edited.
//
// -------------------------------------------------------------------
// WHAT "SOUND" MEANS HERE, precisely
// -------------------------------------------------------------------
// A closure rule is a graph transformer, so its soundness statement is
// the TRANSCRIPTION-FIDELITY property:
//
//     every triple in the output is either already in the input, or is
//     an axiomatic triple, or is derived from the input by ONE
//     application of the rule row the rule claims to implement.
//
// That is `rdfs_licensed` from the Spec module, specialised per rule.
// Composed with the model-theoretic justification of each rule row
// (RDF.Entailment.RDFS.ModelTheory.fst), it gives RDFS-soundness of
// the shipping closure in the entailment sense.
//
// Stating it against the INPUT graph (not the growing accumulator) is
// the shape decision that makes the fixed-point driver's induction go
// through; it is also strictly stronger than the accumulator form.
//
// -------------------------------------------------------------------
// FINDINGS (details at each theorem)
// -------------------------------------------------------------------
//   RS-1  `rdfs_reflexivity_axioms` is UNSOUND at the RDFS rung. It
//         emits `C rdfs:subClassOf C` for every C typed `owl:Class`
//         and `P rdfs:subPropertyOf P` for every P typed
//         `owl:ObjectProperty` / `owl:DatatypeProperty`. Neither is
//         RDFS-entailed: rdfs10 / rdfs6 fire on `rdfs:Class` and
//         `rdf:Property`, and an RDFS interpretation is free to read
//         `owl:Class` as an arbitrary IRI. Machine-checked witness:
//         `reflexivity_axioms_not_rdfs_sound`.
//   RS-2  Rules rdfs1, rdfs4a, rdfs4b, rdfs8, rdfs13 and rdfD1 are NOT
//         implemented anywhere in the tree. This is INCOMPLETENESS,
//         not unsoundness, and it is why the completeness theorem in
//         the ModelTheory module is stated for the rho-df fragment,
//         where none of them is needed.
//   RS-3  `rdfs_rule_range` (rdfs3) silently drops the case where the
//         object is a literal or an RDF 1.2 triple term, because the
//         conclusion would need a literal SUBJECT (generalized RDF,
//         delta D5). The declarative `rdfs3_derives` carries the same
//         premise, so the refinement is exact -- the incompleteness is
//         in the tree's term algebra, not in this proof.
//   RS-4  `RDF.Entailment.Regime.rdfs_closure` -- the function the
//         rdf12 entailment manifests reach through `entails_rdfs` --
//         SHADOWS `RDFS.Closure.rdfs_closure` and implements only an
//         rdf:reifies range rule. None of rdfs1..rdfs13 runs on that
//         path. See the design note; nothing is proven about it here
//         because there is nothing RDFS-shaped to prove.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDFS.Closure
open OWL.Semantics
open OWL.Semantics.MemLemmas
open RDF.Vocabulary.Axioms
open RDF.Entailment.Simple.Spec
open RDF.Entailment.RDF.Spec
open RDF.Entailment.RDFS.Spec

// ===================================================================
// 0. The vocabulary constants agree.
//
// RDFS.Closure and RDF.Vocabulary.Axioms each cast RDF.Vocabulary's
// canonical strings to `wf_iri` independently (two `assert_norm`
// sites, by design -- see RDFS.Closure.fsti's banner). The Spec
// modules are written over the Axioms copies and the shipping rules
// over the RDFS.Closure copies, so the refinement proofs need the
// identification. It is definitional; these lemmas make that fact
// available to the SMT encoding by name.
// ===================================================================

let lemma_vocab_agree ()
  : Lemma (RDFS.Closure.rdf_type == i_rdf_type /\
           RDFS.Closure.rdfs_domain == i_rdfs_domain /\
           RDFS.Closure.rdfs_range == i_rdfs_range /\
           RDFS.Closure.rdfs_subClassOf == i_rdfs_subClassOf /\
           RDFS.Closure.rdfs_subPropertyOf == i_rdfs_subPropertyOf /\
           RDFS.Closure.rdfs_member == i_rdfs_member /\
           RDFS.Closure.rdfs_Class == i_rdfs_Class /\
           RDFS.Closure.rdf_Property == i_rdf_Property /\
           RDFS.Closure.rdfs_ContainerMembershipProperty ==
             i_rdfs_ContainerMembershipProperty) = ()

// The three constants the rows added in 2026-07-31 (rdfs1, rdfs4a,
// rdfs4b, rdfs8, rdfs13) need. Kept as a SEPARATE lemma rather than as
// extra conjuncts of `lemma_vocab_agree`: growing that lemma changed
// the SMT context enough to break `selfloop_not_axiomatic`'s 50-fuel
// enumeration of the axiomatic tables, and a budget bump did not
// recover it.
let lemma_vocab_agree_rs2 ()
  : Lemma (RDFS.Closure.rdfs_Resource == i_rdfs_Resource /\
           RDFS.Closure.rdfs_Literal == i_rdfs_Literal /\
           RDFS.Closure.rdfs_Datatype == i_rdfs_Datatype) = ()

// `term_to_subject` and `subj_term` are mutually inverse where both
// are defined. The Spec's rules are phrased with `subj_term`, the
// shipping rules pattern-match with `term_to_subject`.
let lemma_term_to_subject_subj_term (t : rdf_term) (s : subject)
  : Lemma (requires term_to_subject t == Some s) (ensures subj_term s == t) =
  match t with
  | T_IRI _ -> ()
  | T_BNode _ -> ()
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

// ===================================================================
// 1. rdfD2 -- `rdf_property_axiom_closure` (the pure "RDF" regime).
//
// RDFS.Closure.fsti:
//   rdf_property_axiom_of_triple t = { s = S_IRI t.p; p = rdf_type;
//                                      o = T_IRI rdf_Property }
//   rdf_property_axiom_closure g  = graph_dedup_sort
//                                     (add_triples_if_new g axioms)
// which is exactly the RDF 1.1 Semantics section 8 row rdfD2.
// ===================================================================

let lemma_rdf_property_axiom_matches (u : triple)
  : Lemma (rdf_property_axiom_of_triple u == rdfD2_conclusion u) = ()

// memP through `add_triples_if_new` (which is `graph_add`, i.e.
// `g @ [t]` guarded by a membership test).
let rec lemma_add_triples_if_new_memP (g ts : list triple) (x : triple)
  : Lemma (ensures memP x (add_triples_if_new g ts) ==> memP x g \/ memP x ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | hd :: tl ->
    lemma_add_triples_if_new_memP (add_triple_if_new g hd) tl x;
    if mem_triple hd g then ()
    else append_memP g [hd] x

// memP through the dedup walk (the triple analogue of
// OWL.Semantics.Soundness's `lemma_dedup_pairs_memP`).
let rec lemma_dedup_sorted_memP (prev : option string)
    (ts acc : list triple) (x : triple)
  : Lemma (ensures memP x (dedup_sorted_aux prev ts acc) ==>
                   (memP x ts \/ memP x acc))
          (decreases ts) =
  match ts with
  | [] -> rev_memP acc x
  | t :: rest ->
    lemma_dedup_sorted_memP prev rest acc x;
    lemma_dedup_sorted_memP (Some (triple_to_key t)) rest (t :: acc) x

// memP through the DECORATED dedup walk. Same shape as
// `lemma_dedup_sorted_memP` above, reading each key out of the pair
// instead of recomputing it. `graph_dedup_sort` became a
// decorate-sort-undecorate pass on 2026-08-02 (about half of QUDT's
// closure time was `triple_to_key` string building inside the sort
// comparator), so the walk it performs is this one.
let rec lemma_dedup_sorted_decorated_memP (prev : option string)
    (ts : list (string * triple)) (acc : list triple) (x : triple)
  : Lemma (ensures memP x (dedup_sorted_decorated_aux prev ts acc) ==>
                   (memP x (map snd ts) \/ memP x acc))
          (decreases ts) =
  match ts with
  | [] -> rev_memP acc x
  | (k, t) :: rest ->
    lemma_dedup_sorted_decorated_memP prev rest acc x;
    lemma_dedup_sorted_decorated_memP (Some k) rest (t :: acc) x

// Every triple `graph_dedup_sort` returns came from the input graph.
//
// The chain is one step longer than it used to be, because the sort now
// runs over `(key, triple)` pairs: walk-lemma to get membership in
// `map snd sorted`, `memP_map_elim` to name the pair, the sortWith
// lemma to push that pair back into the decorated list, and
// `memP_map_elim` once more to name the triple it decorated.
let lemma_graph_dedup_sort_memP (g : list triple) (x : triple)
  : Lemma (ensures memP x (graph_dedup_sort g) ==> memP x g) =
  let f = (fun (t : triple) -> (triple_to_key t, t)) in
  let dec : list (string * triple) = map f g in
  let sorted = sortWith cmp_decorated_triple dec in
  lemma_dedup_sorted_decorated_memP None sorted [] x;
  introduce memP x (graph_dedup_sort g) ==> memP x g
  with _. begin
    memP_map_elim snd x sorted;
    eliminate exists (p : (string * triple)). memP p sorted /\ snd p == x
    returns memP x g
    with _. begin
      lemma_sortWith_memP cmp_decorated_triple dec p;
      memP_map_elim f p g;
      eliminate exists (t : triple). memP t g /\ f t == p
      returns memP x g
      with _. ()
    end
  end

val rdf_property_axiom_closure_licensed (g : rdf_graph)
  : Lemma (ensures forall (t : triple).
             memP t (rdf_property_axiom_closure g) ==>
             (memP t g \/ rdfD2_derives g t))

let rdf_property_axiom_closure_licensed g =
  let axioms : rdf_graph = map rdf_property_axiom_of_triple g in
  introduce forall (t : triple).
      memP t (rdf_property_axiom_closure g) ==>
      (memP t g \/ rdfD2_derives g t)
  with introduce memP t (rdf_property_axiom_closure g) ==>
                 (memP t g \/ rdfD2_derives g t)
  with _ . begin
    lemma_graph_dedup_sort_memP (add_triples_if_new g axioms) t;
    lemma_add_triples_if_new_memP g axioms t;
    let helper () : Lemma (requires memP t axioms) (ensures rdfD2_derives g t) =
      memP_map_elim rdf_property_axiom_of_triple t g;
      eliminate exists (u : triple). memP u g /\ rdf_property_axiom_of_triple u == t
      returns (rdfD2_derives g t)
      with _ . assert (memP u g /\ t == rdfD2_conclusion u)
    in
    FStar.Classical.move_requires helper ()
  end

// ===================================================================
// 2. rdfs2 -- `rdfs_rule_domain`.
//
// The rule reads the ig_pred bucket twice (domain declarations, then
// the data triples of each declared property), so its hypotheses are
// `ig_wf_pred` plus "the snapshot IS the graph". Exactly the
// hypotheses OWL.Semantics.Soundness.rdfs_rule_domain_sound uses.
// ===================================================================

// `licensed_by2 r src seed out`: every triple of `out` is either in
// the SEED graph the rule was handed, or derived by rule `r` from the
// SOURCE graph its premises were read from. The two are the same graph
// for a single rule application, but NOT inside `rdfs_closure_step`,
// which builds one index snapshot from the step's input and then
// chains seven rules through a growing accumulator. Keeping them
// separate is what makes the per-rule results compose through the
// driver; `licensed_by` is the diagonal.
let licensed_by2 (r : list triple -> triple -> prop) (src seed acc : list triple) : prop =
  forall (t : triple). memP t acc ==> (memP t seed \/ r src t)

let licensed_by (r : list triple -> triple -> prop) (g acc : list triple) : prop =
  licensed_by2 r g g acc

val rdfs_rule_domain_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_pred ig)
          (ensures licensed_by2 rdfs2_derives ig.ig_triples g (rdfs_rule_domain g ig))

let rdfs_rule_domain_licensed g ig =
  let inv = licensed_by2 rdfs2_derives ig.ig_triples g in
  let decls = bucket_lookup ig.ig_pred rdfs_domain in
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            emit_once_term ig acc2 t.s rdf_type decl.o)
          acc matching
      | _ -> acc in
  introduce forall (acc : rdf_graph) (decl : triple).
      (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with introduce (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with _ . begin
    assert (memP decl ig.ig_triples /\ decl.p == rdfs_domain);
    match decl.s with
    | S_IRI p ->
      let matching = bucket_lookup ig.ig_pred p in
      let inner_step : rdf_graph -> triple -> rdf_graph =
        fun (acc2 : rdf_graph) (t : triple) ->
          emit_once_term ig acc2 t.s rdf_type decl.o in
      introduce forall (acc2 : rdf_graph) (t : triple).
          (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with introduce (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with _ . begin
        assert (memP t ig.ig_triples /\ t.p == p);
        let new_t : triple = { s = t.s; p = rdf_type; o = decl.o } in
        assert (memP decl ig.ig_triples /\ decl.p == i_rdfs_domain /\ decl.s == S_IRI p);
        assert (memP t ig.ig_triples /\ t.p == p);
        assert (new_t == ({ s = t.s; p = i_rdf_type; o = decl.o } <: triple));
        assert (rdfs2_derives ig.ig_triples new_t)
      end;
      fold_left_inv inv inner_step matching acc
    | _ -> ()
  end;
  fold_left_inv inv outer_step decls g;
  assert_norm (rdfs_rule_domain g ig == fold_left outer_step g decls)

// ===================================================================
// 3. rdfs3 -- `rdfs_rule_range`. Finding RS-3 lives here: the rule
// only fires when the object is subject-eligible, and so does the
// declarative rule, so the refinement is exact.
// ===================================================================

val rdfs_rule_range_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_pred ig)
          (ensures licensed_by2 rdfs3_derives ig.ig_triples g (rdfs_rule_range g ig))

let rdfs_rule_range_licensed g ig =
  let inv = licensed_by2 rdfs3_derives ig.ig_triples g in
  let decls = bucket_lookup ig.ig_pred rdfs_range in
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            match term_to_subject t.o with
            | Some b_subj ->
              emit_once_term ig acc2 b_subj rdf_type decl.o
            | None -> acc2)
          acc matching
      | _ -> acc in
  introduce forall (acc : rdf_graph) (decl : triple).
      (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with introduce (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with _ . begin
    assert (memP decl ig.ig_triples /\ decl.p == rdfs_range);
    match decl.s with
    | S_IRI p ->
      let matching = bucket_lookup ig.ig_pred p in
      let inner_step : rdf_graph -> triple -> rdf_graph =
        fun (acc2 : rdf_graph) (t : triple) ->
          match term_to_subject t.o with
          | Some b_subj ->
            emit_once_term ig acc2 b_subj rdf_type decl.o
          | None -> acc2 in
      introduce forall (acc2 : rdf_graph) (t : triple).
          (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with introduce (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with _ . begin
        assert (memP t ig.ig_triples /\ t.p == p);
        match term_to_subject t.o with
        | Some b_subj ->
          lemma_term_to_subject_subj_term t.o b_subj;
          let new_t : triple = { s = b_subj; p = rdf_type; o = decl.o } in
          assert (memP decl ig.ig_triples /\ decl.p == i_rdfs_range /\ decl.s == S_IRI p);
          assert (memP t ig.ig_triples /\ t.p == p /\ subj_term b_subj == t.o);
          assert (new_t == ({ s = b_subj; p = i_rdf_type; o = decl.o } <: triple));
          assert (rdfs3_derives ig.ig_triples new_t)
        | None -> ()
      end;
      fold_left_inv inv inner_step matching acc
    | _ -> ()
  end;
  fold_left_inv inv outer_step decls g;
  assert_norm (rdfs_rule_range g ig == fold_left outer_step g decls)

// ===================================================================
// 4. rdfs7 -- `rdfs_rule_subPropertyOf`.
// ===================================================================

val rdfs_rule_subPropertyOf_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_pred ig)
          (ensures licensed_by2 rdfs7_derives ig.ig_triples g
                     (rdfs_rule_subPropertyOf g ig))

let rdfs_rule_subPropertyOf_licensed g ig =
  let inv = licensed_by2 rdfs7_derives ig.ig_triples g in
  let decls = bucket_lookup ig.ig_pred rdfs_subPropertyOf in
  // Mirrors the engine's own `rdfs7_emit` lambda-lift (RDFS.Closure.
  // fsti, rdfs7_reaches_fact park resolution, 2026-08-06): the inner
  // fold now names the SAME top-level helper the engine calls
  // (`rdfs7_emit ig q`) instead of a proof-local anonymous copy of the
  // lambda, so the `assert_norm` bridge below normalizes both sides to
  // the identical term.
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (decl : triple) ->
      match decl.s, decl.o with
      | S_IRI p, T_IRI q ->
        let matching = bucket_lookup ig.ig_pred p in
        fold_left (rdfs7_emit ig q) acc matching
      | _, _ -> acc in
  introduce forall (acc : rdf_graph) (decl : triple).
      (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with introduce (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with _ . begin
    assert (memP decl ig.ig_triples /\ decl.p == rdfs_subPropertyOf);
    // Nested, constructor-complete case analysis rather than a
    // catch-all on the PAIR: the shipping rule scrutinises
    // `decl.s, decl.o` as a tuple, and F* only reduces that tuple
    // match in the fall-through arms when it has the constructor
    // equation for each component separately.
    match decl.s, decl.o with
    | S_BNode _, _ -> ()
    | S_IRI _, T_BNode _ -> ()
    | S_IRI _, T_Literal _ -> ()
    | S_IRI _, T_TripleTerm _ _ _ -> ()
    | S_IRI p, T_IRI q ->
      let matching = bucket_lookup ig.ig_pred p in
      let inner_step : rdf_graph -> triple -> rdf_graph = rdfs7_emit ig q in
      introduce forall (acc2 : rdf_graph) (t : triple).
          (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with introduce (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with _ . begin
        assert (memP t ig.ig_triples /\ t.p == p);
        let new_t : triple = { s = t.s; p = q; o = t.o } in
        assert (memP decl ig.ig_triples /\ decl.p == i_rdfs_subPropertyOf /\
                decl.s == S_IRI p /\ decl.o == T_IRI q);
        assert (memP t ig.ig_triples /\ t.p == p);
        assert (rdfs7_derives ig.ig_triples new_t)
      end;
      fold_left_inv inv inner_step matching acc;
      // PROOF-ENGINEERING NOTE (a new trap, not present at the simple
      // rung; recorded in the design note as pattern 8.2).
      //
      // rdfs7 is the only shipping rule whose INNER lambda closes over
      // a PATTERN-BOUND variable (`q`, bound by the outer rule's
      // `match decl.s, decl.o with | S_IRI p, T_IRI q ->`). The
      // fold_left_inv pattern that discharges every other rule fails
      // here: `fold_left_inv` yields `inv (fold_left inner_step acc
      // matching)`, and the SMT encoding gives the proof's copy of the
      // lambda and the one inside `outer_step` unrelated closure
      // symbols -- the F3 trap of the OWL pilot, in its higher-order
      // form. The `unfold let` answer of pattern 7.5 does not apply
      // (the lambda is not an argument of the shipping call, it is
      // inside a match arm).
      //
      // What does work: rebuild the scrutinee as a RECORD LITERAL so
      // the match iota-reduces, `assert_norm` the reduced form, then
      // transport along `decl == decl'` by congruence. Verified
      // minimal reproduction and fix in the session scratch; both
      // steps are needed.
      let decl' : triple = { s = S_IRI p; p = decl.p; o = T_IRI q } in
      assert (decl == decl');
      assert_norm (outer_step acc decl' == fold_left inner_step acc
                     (bucket_lookup ig.ig_pred p))
  end;
  fold_left_inv inv outer_step decls g;
  assert_norm (rdfs_rule_subPropertyOf g ig == fold_left outer_step g decls)

// ===================================================================
// 5. The ig_sp-driven rules: rdfs9, rdfs11, rdfs5.
//
// These consult `find_objects_indexed`, i.e. the COMPOSITE-key bucket
// ig_sp, so they carry `ig_wf_sp` -- the hypothesis the OWL pilot
// could only prove in its weak form against `build_indexed` (finding
// F1 there: recovering the components from `sp_key s p` needs sp_key
// injectivity, which needs "U+001F never occurs in a blank-node
// label"). The hypothesis is kept explicit rather than assumed, as in
// the pilot.
// ===================================================================

let lemma_find_objects_elim (ig : indexed_graph) (s : subject) (p : wf_iri) (x : rdf_term)
  : Lemma (requires ig_wf_sp ig /\ memP x (find_objects_indexed ig s p))
          (ensures exists (u : triple).
                     memP u ig.ig_triples /\ u.s == s /\ u.p == p /\ u.o == x) =
  let bucket = bucket_lookup ig.ig_sp (sp_key s p) in
  memP_map_elim (fun (t : triple) -> t.o) x bucket

val rdfs_rule_subClassOf_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig)
          (ensures licensed_by2 (rdfs9_derives2 g) ig.ig_triples g
                     (rdfs_rule_subClassOf g ig))

let rdfs_rule_subClassOf_licensed g ig =
  let inv = licensed_by2 (rdfs9_derives2 g) ig.ig_triples g in
  let step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdf_type then
        match t.o with
        | T_IRI class_iri ->
          let super_classes = find_objects_indexed ig (S_IRI class_iri) rdfs_subClassOf in
          fold_left
            (fun (acc2 : rdf_graph) (b_term : rdf_term) ->
              emit_once_term ig acc2 t.s rdf_type b_term)
            acc super_classes
        | _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    if t.p = rdf_type then
      match t.o with
      | T_IRI class_iri ->
        let super_classes = find_objects_indexed ig (S_IRI class_iri) rdfs_subClassOf in
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (b_term : rdf_term) ->
            emit_once_term ig acc2 t.s rdf_type b_term in
        introduce forall (acc2 : rdf_graph) (b_term : rdf_term).
            (memP b_term super_classes /\ inv acc2) ==> inv (inner_step acc2 b_term)
        with introduce (memP b_term super_classes /\ inv acc2) ==>
                       inv (inner_step acc2 b_term)
        with _ . begin
          lemma_find_objects_elim ig (S_IRI class_iri) rdfs_subClassOf b_term;
          let new_t : triple = { s = t.s; p = rdf_type; o = b_term } in
          eliminate exists (u : triple).
              memP u ig.ig_triples /\ u.s == S_IRI class_iri /\
              u.p == rdfs_subClassOf /\ u.o == b_term
          returns inv (inner_step acc2 b_term)
          with _ . begin
            assert (memP u ig.ig_triples /\ u.p == i_rdfs_subClassOf /\
                    u.s == S_IRI class_iri);
            assert (memP t g /\ t.p == i_rdf_type /\
                    t.o == subj_term (S_IRI class_iri));
            assert (new_t == ({ s = t.s; p = i_rdf_type; o = u.o } <: triple));
            assert (rdfs9_derives2 g ig.ig_triples new_t)
          end
        end;
        fold_left_inv inv inner_step super_classes acc
      | _ -> ()
    else ()
  end;
  fold_left_inv inv step g g;
  assert_norm (rdfs_rule_subClassOf g ig == fold_left step g g)

val rdfs_rule_subClassOf_trans_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig)
          (ensures licensed_by2 (rdfs11_derives2 g) ig.ig_triples g
                     (rdfs_rule_subClassOf_trans g ig))

let rdfs_rule_subClassOf_trans_licensed g ig =
  let inv = licensed_by2 (rdfs11_derives2 g) ig.ig_triples g in
  let step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subClassOf then
        match term_to_subject t.o with
        | Some b_subj ->
          let supers = find_objects_indexed ig b_subj rdfs_subClassOf in
          fold_left
            (fun (acc2 : rdf_graph) (c_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = rdfs_subClassOf; o = c_term } in
              add_triple_unchecked acc2 new_t)
            acc supers
        | None -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    if t.p = rdfs_subClassOf then
      match term_to_subject t.o with
      | Some b_subj ->
        lemma_term_to_subject_subj_term t.o b_subj;
        let supers = find_objects_indexed ig b_subj rdfs_subClassOf in
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (c_term : rdf_term) ->
            let new_t : triple = { s = t.s; p = rdfs_subClassOf; o = c_term } in
            add_triple_unchecked acc2 new_t in
        introduce forall (acc2 : rdf_graph) (c_term : rdf_term).
            (memP c_term supers /\ inv acc2) ==> inv (inner_step acc2 c_term)
        with introduce (memP c_term supers /\ inv acc2) ==> inv (inner_step acc2 c_term)
        with _ . begin
          lemma_find_objects_elim ig b_subj rdfs_subClassOf c_term;
          let new_t : triple = { s = t.s; p = rdfs_subClassOf; o = c_term } in
          eliminate exists (u : triple).
              memP u ig.ig_triples /\ u.s == b_subj /\
              u.p == rdfs_subClassOf /\ u.o == c_term
          returns inv (inner_step acc2 c_term)
          with _ . begin
            assert (memP t g /\ t.p == i_rdfs_subClassOf);
            assert (memP u ig.ig_triples /\ u.p == i_rdfs_subClassOf /\ u.s == b_subj);
            assert (subj_term b_subj == t.o);
            assert (new_t == ({ s = t.s; p = i_rdfs_subClassOf; o = u.o } <: triple));
            assert (rdfs11_derives2 g ig.ig_triples new_t)
          end
        end;
        fold_left_inv inv inner_step supers acc
      | None -> ()
    else ()
  end;
  fold_left_inv inv step g g;
  assert_norm (rdfs_rule_subClassOf_trans g ig == fold_left step g g)

val rdfs_rule_subPropertyOf_trans_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig)
          (ensures licensed_by2 (rdfs5_derives2 g) ig.ig_triples g
                     (rdfs_rule_subPropertyOf_trans g ig))

let rdfs_rule_subPropertyOf_trans_licensed g ig =
  let inv = licensed_by2 (rdfs5_derives2 g) ig.ig_triples g in
  let step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subPropertyOf then
        match term_to_subject t.o with
        | Some q_subj ->
          let supers = find_objects_indexed ig q_subj rdfs_subPropertyOf in
          fold_left
            (fun (acc2 : rdf_graph) (r_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = rdfs_subPropertyOf; o = r_term } in
              add_triple_unchecked acc2 new_t)
            acc supers
        | None -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    if t.p = rdfs_subPropertyOf then
      match term_to_subject t.o with
      | Some q_subj ->
        lemma_term_to_subject_subj_term t.o q_subj;
        let supers = find_objects_indexed ig q_subj rdfs_subPropertyOf in
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (r_term : rdf_term) ->
            let new_t : triple = { s = t.s; p = rdfs_subPropertyOf; o = r_term } in
            add_triple_unchecked acc2 new_t in
        introduce forall (acc2 : rdf_graph) (r_term : rdf_term).
            (memP r_term supers /\ inv acc2) ==> inv (inner_step acc2 r_term)
        with introduce (memP r_term supers /\ inv acc2) ==> inv (inner_step acc2 r_term)
        with _ . begin
          lemma_find_objects_elim ig q_subj rdfs_subPropertyOf r_term;
          let new_t : triple = { s = t.s; p = rdfs_subPropertyOf; o = r_term } in
          eliminate exists (u : triple).
              memP u ig.ig_triples /\ u.s == q_subj /\
              u.p == rdfs_subPropertyOf /\ u.o == r_term
          returns inv (inner_step acc2 r_term)
          with _ . begin
            assert (memP t g /\ t.p == i_rdfs_subPropertyOf);
            assert (memP u ig.ig_triples /\ u.p == i_rdfs_subPropertyOf /\ u.s == q_subj);
            assert (subj_term q_subj == t.o);
            assert (new_t == ({ s = t.s; p = i_rdfs_subPropertyOf; o = u.o } <: triple));
            assert (rdfs5_derives2 g ig.ig_triples new_t)
          end
        end;
        fold_left_inv inv inner_step supers acc
      | None -> ()
    else ()
  end;
  fold_left_inv inv step g g;
  assert_norm (rdfs_rule_subPropertyOf_trans g ig == fold_left step g g)

// ===================================================================
// 6. `rdfs_rule_container_membership`.
//
// The rule emits, unconditionally, for each of rdf:_1 .. rdf:_5:
//     rdf:_n rdfs:subPropertyOf rdfs:member .
//     rdf:_n rdf:type rdfs:ContainerMembershipProperty .
// Both are RDFS AXIOMATIC TRIPLES (RDF 1.1 Semantics section 9, the
// infinite rdf:_n rows), so the rule is sound with no premises at all
// -- it is an axiom emitter, not an inference rule. The name in
// RDFS.Closure.fsti's banner ("container membership axioms") is
// accurate; the rule-table row it is sometimes filed under (rdfs12)
// would need the rdf:type premise this rule does not read.
//
// The finite rdf:_1..rdf:_5 slice is an INCOMPLETENESS with respect to
// the infinite family (RS-2), never an unsoundness.
// ===================================================================

let lemma_rdf_member_iris ()
  : Lemma (is_rdf_member_iri RDFS.Closure.rdf_1 /\ is_rdf_member_iri RDFS.Closure.rdf_2 /\
           is_rdf_member_iri RDFS.Closure.rdf_3 /\ is_rdf_member_iri RDFS.Closure.rdf_4 /\
           is_rdf_member_iri RDFS.Closure.rdf_5) =
  assert_norm (RDFS.Closure.rdf_1 == rdf_member_iri_str "1");
  assert_norm (RDFS.Closure.rdf_2 == rdf_member_iri_str "2");
  assert_norm (RDFS.Closure.rdf_3 == rdf_member_iri_str "3");
  assert_norm (RDFS.Closure.rdf_4 == rdf_member_iri_str "4");
  assert_norm (RDFS.Closure.rdf_5 == rdf_member_iri_str "5");
  introduce exists (n : string). (RDFS.Closure.rdf_1 <: string) == rdf_member_iri_str n
  with "1" and ();
  introduce exists (n : string). (RDFS.Closure.rdf_2 <: string) == rdf_member_iri_str n
  with "2" and ();
  introduce exists (n : string). (RDFS.Closure.rdf_3 <: string) == rdf_member_iri_str n
  with "3" and ();
  introduce exists (n : string). (RDFS.Closure.rdf_4 <: string) == rdf_member_iri_str n
  with "4" and ();
  introduce exists (n : string). (RDFS.Closure.rdf_5 <: string) == rdf_member_iri_str n
  with "5" and ()

// --fuel 8: `memP cmp container_membership_properties` has to unfold
// five cons cells to become the five-way disjunction the five
// `is_rdf_member_iri` facts discharge. Default fuel is 2. A budget
// bump, not a logic change; no --lax, no --admit_smt_queries.
#push-options "--fuel 8 --z3rlimit 60"
val rdfs_rule_container_membership_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures forall (t : triple).
             memP t (rdfs_rule_container_membership g ig) ==>
             (memP t g \/ rdfs_axiomatic t \/ rdfs_member_subproperty t))

let rdfs_rule_container_membership_licensed g ig =
  lemma_rdf_member_iris ();
  let inv : rdf_graph -> prop =
    fun (acc : rdf_graph) ->
      forall (t : triple). memP t acc ==>
        (memP t g \/ rdfs_axiomatic t \/ rdfs_member_subproperty t) in
  let step : rdf_graph -> wf_iri -> rdf_graph =
    fun (acc : rdf_graph) (cmp : wf_iri) ->
      let t1 : triple = { s = S_IRI cmp; p = rdfs_subPropertyOf; o = T_IRI rdfs_member } in
      let t2 : triple = { s = S_IRI cmp; p = rdf_type;
                          o = T_IRI rdfs_ContainerMembershipProperty } in
      add_triple_unchecked (add_triple_unchecked acc t1) t2 in
  introduce forall (acc : rdf_graph) (cmp : wf_iri).
      (memP cmp container_membership_properties /\ inv acc) ==> inv (step acc cmp)
  with introduce (memP cmp container_membership_properties /\ inv acc) ==> inv (step acc cmp)
  with _ . begin
    assert_norm (container_membership_properties ==
                 [RDFS.Closure.rdf_1; RDFS.Closure.rdf_2; RDFS.Closure.rdf_3;
                  RDFS.Closure.rdf_4; RDFS.Closure.rdf_5]);
    assert (cmp == RDFS.Closure.rdf_1 \/ cmp == RDFS.Closure.rdf_2 \/
            cmp == RDFS.Closure.rdf_3 \/ cmp == RDFS.Closure.rdf_4 \/
            cmp == RDFS.Closure.rdf_5);
    assert (is_rdf_member_iri cmp);
    let t1 : triple = { s = S_IRI cmp; p = rdfs_subPropertyOf; o = T_IRI rdfs_member } in
    let t2 : triple = { s = S_IRI cmp; p = rdf_type;
                        o = T_IRI rdfs_ContainerMembershipProperty } in
    assert (t2 == ({ s = S_IRI cmp; p = i_rdf_type;
                     o = T_IRI i_rdfs_ContainerMembershipProperty } <: triple));
    assert (rdfs_axiomatic t2);
    assert (t1 == ({ s = S_IRI cmp; p = i_rdfs_subPropertyOf;
                     o = T_IRI i_rdfs_member } <: triple));
    assert (rdfs_member_subproperty t1);
    assert (step acc cmp == t2 :: t1 :: acc);
    assert (forall (t : triple). memP t (t2 :: t1 :: acc) ==>
              (t == t2 \/ t == t1 \/ memP t acc));
    assert (inv (t2 :: t1 :: acc))
  end;
  fold_left_inv inv step container_membership_properties g;
  assert_norm (rdfs_rule_container_membership g ig ==
               fold_left step g container_membership_properties)
#pop-options

let owl_class_graph (c : wf_iri) : rdf_graph =
  [ ({ s = S_IRI c; p = rdf_type; o = T_IRI owl_Class } <: triple) ]

let owl_class_refl_triple (c : wf_iri) : triple =
  { s = S_IRI c; p = rdfs_subClassOf; o = T_IRI c }

// The witness graph and the self-loop triple finding RS-1 is about.
// They sit HERE, above section 6b, rather than in section 7 with the
// rest of RS-1: `selfloop_not_axiomatic` below is a 50-fuel enumeration
// of the axiomatic tables and its query is sensitive to how much else
// is in scope.
//
// `owl_class_refl_triple c` is not an axiomatic triple of either
// vocabulary. Every axiomatic `rdfs:subClassOf` row has distinct
// endpoints; every other row has a different predicate.
//
// --split_queries always (2026-07-31): the RS-2 rows enlarged
// RDFS.Closure's SMT encoding enough that z3 returned "unknown because
// (incomplete quantifiers)" on the conjoined goal -- at 75 of a 240
// rlimit, so it was quantifier saturation, not budget. Splitting the
// three conjuncts into three queries recovers it. A proof-splitting
// flag, not an escape hatch: no --lax, no --admit_smt_queries.
// Budget raised 600 -> 1200 on 2026-08-02. Nothing in this lemma
// changed; RDFS.Closure.fsti gained `emit_once_term` (the guard the
// rdfs2/3/7/9 rows now use), and the extra definition in scope shifts
// the SMT context enough to tip an already-borderline assert_norm
// block. A resource bump, the same idiom this tree uses elsewhere --
// no --admit_smt_queries, no --lax.
// `emit_once_term` (added to RDFS.Closure.fsti 2026-08-02 for the
// rdfs2/3/7/9 duplicate-emission fix) tips this block when its
// definition equation sits in the SMT context: raising rlimit to 1200
// and fuel to 100 did NOT recover it, so it is context noise, not a
// resource shortage. Excluding that one symbol's facts restores the
// original budget. The four rule-refinement proofs above do need the
// definition and are unaffected by this per-block exclusion.
#push-options "--fuel 50 --ifuel 2 --z3rlimit 600 --split_queries always --using_facts_from '*,-RDFS.Closure.emit_once_term'"
val selfloop_not_axiomatic (c : wf_iri)
  : Lemma (~(rdf_axiomatic (owl_class_refl_triple c)) /\
           ~(rdfs_axiomatic (owl_class_refl_triple c)) /\
           ~(rdfs_member_subproperty (owl_class_refl_triple c)))

let selfloop_not_axiomatic c =
  lemma_vocab_agree ();
  assert_norm (i_rdfs_subClassOf =!= i_rdf_type);
  assert_norm (i_rdfs_subClassOf =!= i_rdfs_domain);
  assert_norm (i_rdfs_subClassOf =!= i_rdfs_range);
  assert_norm (i_rdfs_subClassOf =!= i_rdfs_subPropertyOf);
  assert_norm (i_rdf_Alt =!= i_rdfs_Container);
  assert_norm (i_rdf_Bag =!= i_rdfs_Container);
  assert_norm (i_rdf_Seq =!= i_rdfs_Container);
  assert_norm (i_rdfs_ContainerMembershipProperty =!= i_rdf_Property);
  assert_norm (i_rdfs_Datatype =!= i_rdfs_Class)
#pop-options

// ===================================================================
// 6b. THE ROWS ADDED 2026-07-31 (finding RS-2 closed for the buildable
// rows): rdfs1, rdfs4a, rdfs4b, rdfs8, rdfs13.
//
// Each rule reads its premises from the graph it folds over, so the
// source graph and the seed graph coincide and the statements use the
// diagonal `licensed_by`. rdfs1 has no premise at all and is stated
// like the container rule.
// ===================================================================

// rdfs1. The rule emits, unconditionally, one triple per recognized
// datatype IRI. `RDFS.Closure.recognized_datatypes` is the minimum D of
// RDF 1.1 Semantics section 8, so the licence is stated at `d_minimal`.
#push-options "--fuel 8 --z3rlimit 60"
val rdfs_rule_recognized_datatypes_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures forall (t : triple).
             memP t (rdfs_rule_recognized_datatypes g ig) ==>
             (memP t g \/ rdfs1_derives d_minimal t))

let rdfs_rule_recognized_datatypes_licensed g ig =
  lemma_vocab_agree ();
  lemma_vocab_agree_rs2 ();
  let inv : rdf_graph -> prop =
    fun (acc : rdf_graph) ->
      forall (t : triple). memP t acc ==> (memP t g \/ rdfs1_derives d_minimal t) in
  let step : rdf_graph -> wf_iri -> rdf_graph = rdfs1_step ig in
  introduce forall (acc : rdf_graph) (d : wf_iri).
      (memP d recognized_datatypes /\ inv acc) ==> inv (step acc d)
  with introduce (memP d recognized_datatypes /\ inv acc) ==> inv (step acc d)
  with _ . begin
    // The emit-once guard's `then` branch returns the accumulator
    // untouched, so the invariant is carried across it for free.
    if snapshot_carries ig (S_IRI d) rdf_type rdfs_Datatype then ()
    else begin
      assert_norm (recognized_datatypes == [rdf_lang_string; xsd_string]);
      assert (d == rdf_lang_string \/ d == xsd_string);
      assert (d_minimal d);
      let new_t : triple = { s = S_IRI d; p = rdf_type; o = T_IRI rdfs_Datatype } in
      assert (new_t == ({ s = S_IRI d; p = i_rdf_type; o = T_IRI i_rdfs_Datatype } <: triple));
      assert (rdfs1_derives d_minimal new_t);
      assert (step acc d == new_t :: acc)
    end
  end;
  fold_left_inv inv step recognized_datatypes g;
  assert_norm (rdfs_rule_recognized_datatypes g ig ==
               fold_left step g recognized_datatypes)
#pop-options

// rdfs4a. The premise's subject stays a subject, so the rule fires on
// every triple with no escape.
val rdfs_rule_resource_subject_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures licensed_by rdfs4a_derives g (rdfs_rule_resource_subject g ig))

let rdfs_rule_resource_subject_licensed g ig =
  lemma_vocab_agree ();
  lemma_vocab_agree_rs2 ();
  let inv = licensed_by rdfs4a_derives g in
  let step : rdf_graph -> triple -> rdf_graph = rdfs4a_step ig in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    if snapshot_carries ig t.s rdf_type rdfs_Resource then ()
    else begin
      let new_t : triple = { s = t.s; p = rdf_type; o = T_IRI rdfs_Resource } in
      assert (new_t == ({ s = t.s; p = i_rdf_type; o = T_IRI i_rdfs_Resource } <: triple));
      assert (rdfs4a_derives g new_t);
      assert (step acc t == new_t :: acc)
    end
  end;
  fold_left_inv inv step g g;
  assert_norm (rdfs_rule_resource_subject g ig == fold_left step g g)

// rdfs4b. FINDING RS-3 applies here exactly as it does to rdfs3: the
// object moves into subject position, so the rule cannot fire on a
// literal or triple-term object. `rdfs4b_derives` carries the same
// `subj_term ys == u.o` premise, so the refinement is EXACT.
val rdfs_rule_resource_object_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures licensed_by rdfs4b_derives g (rdfs_rule_resource_object g ig))

let rdfs_rule_resource_object_licensed g ig =
  lemma_vocab_agree ();
  lemma_vocab_agree_rs2 ();
  let inv = licensed_by rdfs4b_derives g in
  let step : rdf_graph -> triple -> rdf_graph = rdfs4b_step ig in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    match term_to_subject t.o with
    | Some y_subj ->
      if snapshot_carries ig y_subj rdf_type rdfs_Resource then ()
      else begin
        lemma_term_to_subject_subj_term t.o y_subj;
        let new_t : triple = { s = y_subj; p = rdf_type; o = T_IRI rdfs_Resource } in
        assert (memP t g /\ subj_term y_subj == t.o);
        assert (new_t == ({ s = y_subj; p = i_rdf_type; o = T_IRI i_rdfs_Resource } <: triple));
        assert (rdfs4b_derives g new_t)
      end
    | None -> ()
  end;
  fold_left_inv inv step g g;
  assert_norm (rdfs_rule_resource_object g ig == fold_left step g g)

// rdfs8.
val rdfs_rule_class_subclass_resource_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures licensed_by rdfs8_derives g
                     (rdfs_rule_class_subclass_resource g ig))

let rdfs_rule_class_subclass_resource_licensed g ig =
  lemma_vocab_agree ();
  lemma_vocab_agree_rs2 ();
  let inv = licensed_by rdfs8_derives g in
  let step : rdf_graph -> triple -> rdf_graph = rdfs8_step ig in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    if is_typed_as t rdfs_Class &&
       not (snapshot_carries ig t.s rdfs_subClassOf rdfs_Resource) then begin
      match t.o with
      | T_IRI i ->
        let new_t : triple =
          { s = t.s; p = rdfs_subClassOf; o = T_IRI rdfs_Resource } in
        assert (t.p == i_rdf_type /\ t.o == T_IRI i_rdfs_Class);
        assert (new_t ==
                ({ s = t.s; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Resource } <: triple));
        assert (rdfs8_derives g new_t)
      | _ -> ()
    end else ()
  end;
  fold_left_inv inv step g g;
  assert_norm (rdfs_rule_class_subclass_resource g ig == fold_left step g g)

// rdfs13.
val rdfs_rule_datatype_subclass_literal_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures licensed_by rdfs13_derives g
                     (rdfs_rule_datatype_subclass_literal g ig))

let rdfs_rule_datatype_subclass_literal_licensed g ig =
  lemma_vocab_agree ();
  lemma_vocab_agree_rs2 ();
  let inv = licensed_by rdfs13_derives g in
  let step : rdf_graph -> triple -> rdf_graph = rdfs13_step ig in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    if is_typed_as t rdfs_Datatype &&
       not (snapshot_carries ig t.s rdfs_subClassOf rdfs_Literal) then begin
      match t.o with
      | T_IRI i ->
        let new_t : triple =
          { s = t.s; p = rdfs_subClassOf; o = T_IRI rdfs_Literal } in
        assert (t.p == i_rdf_type /\ t.o == T_IRI i_rdfs_Datatype);
        assert (new_t ==
                ({ s = t.s; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Literal } <: triple));
        assert (rdfs13_derives g new_t)
      | _ -> ()
    end else ()
  end;
  fold_left_inv inv step g g;
  assert_norm (rdfs_rule_datatype_subclass_literal g ig == fold_left step g g)

// ===================================================================
// 6c. THE EMIT-ONCE GUARD IS SET-NEUTRAL (issue #340 item 4).
//
// Each of the five rows above consults `snapshot_carries ig` and SKIPS
// its emission when the step's index snapshot already carries the
// identical triple. Section 6b's `_licensed` theorems bound each row's
// result from ABOVE and survive a skip for free (skipping only removes
// triples). What has to be re-established is the bound from BELOW: the
// row must still contain every conclusion its rule row licenses on `g`.
//
// Two lemmas per row:
//   `_monotone` -- the fold's seed survives, so anything the guard
//                  skipped (which is in the snapshot, hence in the
//                  seed) is still in the result;
//   `_complete` -- every conclusion the row draws on `g` is in the
//                  result.
// `_licensed` and `_complete` together pin the result's element set to
// exactly (elements of `g`) union (conclusions of the row on `g`), and
// that is also the element set of the UNGUARDED row. So the guard
// cannot lose a derivation.
//
// `snapshot_subset ig g` -- every snapshot triple is in the fold's seed
// -- is the hypothesis `rdfs_closure_step` supplies by construction: it
// builds `ig` from the step's input and seeds every row's fold with an
// accumulator that already contains that input.
//
// WHAT IS NOT PROVED HERE. Set equality of each row is proved; list
// equality of `rdfs_closure_step`'s output is not. Closing that gap
// needs "graph_dedup_sort maps equal element sets to equal lists",
// which is a canonicity result about `List.Tot.sortWith triple_cmp`
// plus `dedup_sorted_aux` that this tree does not have. `triple_to_key`
// is injective on triples and `triple_cmp` is `String.compare` on it,
// so the fact is true; it is stated as prose in section 10.5 of
// docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md and
// backed by a byte-for-byte differential run of `factoidal entail` over
// the suite corpora rather than by a theorem.
// ===================================================================

let snapshot_subset (ig : indexed_graph) (g : rdf_graph) : prop =
  forall (u : triple). memP u ig.ig_triples ==> memP u g

let rec lemma_existsb_elim (#a : Type) (f : a -> bool) (l : list a)
  : Lemma (requires existsb f l)
          (ensures  exists (x : a). memP x l /\ f x)
          (decreases l) =
  match l with
  | [] -> ()
  | h :: t -> if f h then () else lemma_existsb_elim f t

// A snapshot HIT is a real snapshot triple. This is the same ig_wf_sp
// hypothesis the ig_sp-driven rules of section 5 carry, used in the
// same direction.
let lemma_snapshot_carries_elim (ig : indexed_graph) (sub : subject) (prd cls : wf_iri)
  : Lemma (requires ig_wf_sp ig /\ snapshot_carries ig sub prd cls)
          (ensures  memP ({ s = sub; p = prd; o = T_IRI cls } <: triple) ig.ig_triples) =
  let f : rdf_term -> bool =
    (fun (o : rdf_term) -> match o with | T_IRI i -> i = cls | _ -> false) in
  lemma_existsb_elim f (find_objects_indexed ig sub prd);
  eliminate exists (x : rdf_term). memP x (find_objects_indexed ig sub prd) /\ f x
  returns memP ({ s = sub; p = prd; o = T_IRI cls } <: triple) ig.ig_triples
  with _ . begin
    assert (x == T_IRI cls);
    lemma_find_objects_elim ig sub prd x;
    eliminate exists (u : triple).
      memP u ig.ig_triples /\ u.s == sub /\ u.p == prd /\ u.o == x
    returns memP ({ s = sub; p = prd; o = T_IRI cls } <: triple) ig.ig_triples
    with _ . assert (u == ({ s = sub; p = prd; o = T_IRI cls } <: triple))
  end

// `emit_once` never drops anything, and always yields its conclusion
// when the accumulator already covers the snapshot.
let lemma_emit_once (ig : indexed_graph) (acc : rdf_graph)
                    (sub : subject) (prd cls : wf_iri)
  : Lemma (requires ig_wf_sp ig /\ snapshot_subset ig acc)
          (ensures (forall (t : triple).
                      memP t acc ==> memP t (emit_once ig acc sub prd cls)) /\
                   memP ({ s = sub; p = prd; o = T_IRI cls } <: triple)
                        (emit_once ig acc sub prd cls)) =
  if snapshot_carries ig sub prd cls
  then lemma_snapshot_carries_elim ig sub prd cls
  else ()

// The two facts above in the quantified shape the fold lemmas need.
let lemma_emit_once_grows_all (ig : indexed_graph)
  : Lemma (forall (acc : rdf_graph) (sub : subject) (prd : wf_iri) (cls : wf_iri)
                  (t : triple).
             memP t acc ==> memP t (emit_once ig acc sub prd cls)) = ()

let lemma_emit_once_all (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig)
          (ensures forall (acc : rdf_graph) (sub : subject) (prd : wf_iri) (cls : wf_iri).
             snapshot_subset ig acc ==>
             memP ({ s = sub; p = prd; o = T_IRI cls } <: triple)
                  (emit_once ig acc sub prd cls)) =
  introduce forall (acc : rdf_graph) (sub : subject) (prd : wf_iri) (cls : wf_iri).
      snapshot_subset ig acc ==>
      memP ({ s = sub; p = prd; o = T_IRI cls } <: triple) (emit_once ig acc sub prd cls)
  with introduce snapshot_subset ig acc ==>
                 memP ({ s = sub; p = prd; o = T_IRI cls } <: triple)
                      (emit_once ig acc sub prd cls)
  with _ . lemma_emit_once ig acc sub prd cls

// ---- the two generic fold lemmas ----

let rec fold_left_grows (#b : Type) (f : rdf_graph -> b -> rdf_graph)
                        (l : list b) (acc : rdf_graph)
  : Lemma (requires forall (x : rdf_graph) (y : b) (t : triple).
                      memP t x ==> memP t (f x y))
          (ensures  forall (t : triple). memP t acc ==> memP t (fold_left f acc l))
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl -> fold_left_grows f tl (f acc hd)

// Every element of `l` whose step yields a conclusion has that
// conclusion in the fold. `keep` is the invariant that lets the step
// obligation be discharged only for reachable accumulators.
let rec fold_left_reaches (#b : Type) (f : rdf_graph -> b -> rdf_graph)
                          (concl : b -> option triple)
                          (keep : rdf_graph -> prop)
                          (l : list b) (acc : rdf_graph)
  : Lemma (requires keep acc /\
                    (forall (x : rdf_graph) (y : b). keep x ==> keep (f x y)) /\
                    (forall (x : rdf_graph) (y : b) (t : triple).
                       memP t x ==> memP t (f x y)) /\
                    (forall (x : rdf_graph) (y : b) (t : triple).
                       (keep x /\ concl y == Some t) ==> memP t (f x y)))
          (ensures  forall (y : b) (t : triple).
                      (memP y l /\ concl y == Some t) ==> memP t (fold_left f acc l))
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    fold_left_grows f tl (f acc hd);
    fold_left_reaches f concl keep tl (f acc hd)

// ---- the per-row instances ----

// The conclusion each row draws from one input element, as a partial
// function. `None` = the row does not fire on that element.
let rdfs1_concl (d : wf_iri) : option triple =
  Some ({ s = S_IRI d; p = rdf_type; o = T_IRI rdfs_Datatype } <: triple)

let rdfs4a_concl (t : triple) : option triple =
  Some ({ s = t.s; p = rdf_type; o = T_IRI rdfs_Resource } <: triple)

let rdfs4b_concl (t : triple) : option triple =
  match term_to_subject t.o with
  | Some y_subj -> Some ({ s = y_subj; p = rdf_type; o = T_IRI rdfs_Resource } <: triple)
  | None -> None

let rdfs8_concl (t : triple) : option triple =
  if is_typed_as t rdfs_Class
  then Some ({ s = t.s; p = rdfs_subClassOf; o = T_IRI rdfs_Resource } <: triple)
  else None

let rdfs13_concl (t : triple) : option triple =
  if is_typed_as t rdfs_Datatype
  then Some ({ s = t.s; p = rdfs_subClassOf; o = T_IRI rdfs_Literal } <: triple)
  else None

#push-options "--z3rlimit 60"

// -- rdfs1 --
val rdfs_rule_recognized_datatypes_monotone (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures forall (t : triple).
             memP t g ==> memP t (rdfs_rule_recognized_datatypes g ig))

let rdfs_rule_recognized_datatypes_monotone g ig =
  lemma_emit_once_grows_all ig;
  fold_left_grows (rdfs1_step ig) recognized_datatypes g

val rdfs_rule_recognized_datatypes_complete (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ snapshot_subset ig g)
          (ensures forall (d : wf_iri) (t : triple).
             (memP d recognized_datatypes /\ rdfs1_concl d == Some t) ==>
             memP t (rdfs_rule_recognized_datatypes g ig))

let rdfs_rule_recognized_datatypes_complete g ig =
  lemma_emit_once_grows_all ig;
  lemma_emit_once_all ig;
  fold_left_reaches (rdfs1_step ig) rdfs1_concl (fun x -> snapshot_subset ig x)
                    recognized_datatypes g

// -- rdfs4a --
val rdfs_rule_resource_subject_monotone (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures forall (t : triple).
             memP t g ==> memP t (rdfs_rule_resource_subject g ig))

let rdfs_rule_resource_subject_monotone g ig =
  lemma_emit_once_grows_all ig;
  fold_left_grows (rdfs4a_step ig) g g

val rdfs_rule_resource_subject_complete (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ snapshot_subset ig g)
          (ensures forall (u : triple) (t : triple).
             (memP u g /\ rdfs4a_concl u == Some t) ==>
             memP t (rdfs_rule_resource_subject g ig))

let rdfs_rule_resource_subject_complete g ig =
  lemma_emit_once_grows_all ig;
  lemma_emit_once_all ig;
  fold_left_reaches (rdfs4a_step ig) rdfs4a_concl (fun x -> snapshot_subset ig x) g g

// -- rdfs4b --
val rdfs_rule_resource_object_monotone (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures forall (t : triple).
             memP t g ==> memP t (rdfs_rule_resource_object g ig))

let rdfs_rule_resource_object_monotone g ig =
  lemma_emit_once_grows_all ig;
  fold_left_grows (rdfs4b_step ig) g g

val rdfs_rule_resource_object_complete (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ snapshot_subset ig g)
          (ensures forall (u : triple) (t : triple).
             (memP u g /\ rdfs4b_concl u == Some t) ==>
             memP t (rdfs_rule_resource_object g ig))

let rdfs_rule_resource_object_complete g ig =
  lemma_emit_once_grows_all ig;
  lemma_emit_once_all ig;
  fold_left_reaches (rdfs4b_step ig) rdfs4b_concl (fun x -> snapshot_subset ig x) g g

// -- rdfs8 --
val rdfs_rule_class_subclass_resource_monotone (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures forall (t : triple).
             memP t g ==> memP t (rdfs_rule_class_subclass_resource g ig))

let rdfs_rule_class_subclass_resource_monotone g ig =
  lemma_emit_once_grows_all ig;
  fold_left_grows (rdfs8_step ig) g g

val rdfs_rule_class_subclass_resource_complete (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ snapshot_subset ig g)
          (ensures forall (u : triple) (t : triple).
             (memP u g /\ rdfs8_concl u == Some t) ==>
             memP t (rdfs_rule_class_subclass_resource g ig))

let rdfs_rule_class_subclass_resource_complete g ig =
  lemma_emit_once_grows_all ig;
  lemma_emit_once_all ig;
  fold_left_reaches (rdfs8_step ig) rdfs8_concl (fun x -> snapshot_subset ig x) g g

// -- rdfs13 --
val rdfs_rule_datatype_subclass_literal_monotone (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures forall (t : triple).
             memP t g ==> memP t (rdfs_rule_datatype_subclass_literal g ig))

let rdfs_rule_datatype_subclass_literal_monotone g ig =
  lemma_emit_once_grows_all ig;
  fold_left_grows (rdfs13_step ig) g g

val rdfs_rule_datatype_subclass_literal_complete (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ snapshot_subset ig g)
          (ensures forall (u : triple) (t : triple).
             (memP u g /\ rdfs13_concl u == Some t) ==>
             memP t (rdfs_rule_datatype_subclass_literal g ig))

let rdfs_rule_datatype_subclass_literal_complete g ig =
  lemma_emit_once_grows_all ig;
  lemma_emit_once_all ig;
  fold_left_reaches (rdfs13_step ig) rdfs13_concl (fun x -> snapshot_subset ig x) g g

// -------------------------------------------------------------------
// COROLLARY at the shape `rdfs_closure_step` actually uses.
//
// The step builds `ig` as `build_indexed g` and seeds every row's fold
// with an accumulator that contains `g`, so `snapshot_subset` is
// discharged outright and only `ig_wf_sp (build_indexed g)` remains --
// the SAME hypothesis `rdfs_closure_step_sound` already carries. This
// corollary is also the anti-vacuity check on the five lemmas above:
// its hypothesis set is one the tree already treats as satisfiable
// (see ModelTheory's `closure_chain_wf` banner), and its conclusion
// names concrete conclusion triples.
// -------------------------------------------------------------------
val rs2_rows_complete_at_build_indexed (g : rdf_graph)
  : Lemma (requires ig_wf_sp (build_indexed g))
          (ensures
            (forall (d : wf_iri). memP d recognized_datatypes ==>
               memP ({ s = S_IRI d; p = rdf_type; o = T_IRI rdfs_Datatype } <: triple)
                    (rdfs_rule_recognized_datatypes g (build_indexed g))) /\
            (forall (u : triple). memP u g ==>
               memP ({ s = u.s; p = rdf_type; o = T_IRI rdfs_Resource } <: triple)
                    (rdfs_rule_resource_subject g (build_indexed g))) /\
            (forall (u : triple) (y : subject).
               (memP u g /\ term_to_subject u.o == Some y) ==>
               memP ({ s = y; p = rdf_type; o = T_IRI rdfs_Resource } <: triple)
                    (rdfs_rule_resource_object g (build_indexed g))) /\
            (forall (u : triple). (memP u g /\ is_typed_as u rdfs_Class) ==>
               memP ({ s = u.s; p = rdfs_subClassOf; o = T_IRI rdfs_Resource } <: triple)
                    (rdfs_rule_class_subclass_resource g (build_indexed g))) /\
            (forall (u : triple). (memP u g /\ is_typed_as u rdfs_Datatype) ==>
               memP ({ s = u.s; p = rdfs_subClassOf; o = T_IRI rdfs_Literal } <: triple)
                    (rdfs_rule_datatype_subclass_literal g (build_indexed g))))

let rs2_rows_complete_at_build_indexed g =
  let ig = build_indexed g in
  assert (ig.ig_triples == g);
  assert (snapshot_subset ig g);
  rdfs_rule_recognized_datatypes_complete g ig;
  rdfs_rule_resource_subject_complete g ig;
  rdfs_rule_resource_object_complete g ig;
  rdfs_rule_class_subclass_resource_complete g ig;
  rdfs_rule_datatype_subclass_literal_complete g ig;
  // The five `_complete` lemmas are stated over the `_concl` partial
  // functions; the corollary is stated over the rule-row premises the
  // reader cares about. Bridge each one explicitly so the `option`
  // matches do not have to be guessed under the default ifuel.
  introduce forall (d : wf_iri). memP d recognized_datatypes ==>
      memP ({ s = S_IRI d; p = rdf_type; o = T_IRI rdfs_Datatype } <: triple)
           (rdfs_rule_recognized_datatypes g ig)
  with introduce _ ==> _
  with _ . assert (rdfs1_concl d ==
                   Some ({ s = S_IRI d; p = rdf_type; o = T_IRI rdfs_Datatype } <: triple));
  introduce forall (u : triple). memP u g ==>
      memP ({ s = u.s; p = rdf_type; o = T_IRI rdfs_Resource } <: triple)
           (rdfs_rule_resource_subject g ig)
  with introduce _ ==> _
  with _ . assert (rdfs4a_concl u ==
                   Some ({ s = u.s; p = rdf_type; o = T_IRI rdfs_Resource } <: triple));
  introduce forall (u : triple) (y : subject).
      (memP u g /\ term_to_subject u.o == Some y) ==>
      memP ({ s = y; p = rdf_type; o = T_IRI rdfs_Resource } <: triple)
           (rdfs_rule_resource_object g ig)
  with introduce _ ==> _
  with _ . assert (rdfs4b_concl u ==
                   Some ({ s = y; p = rdf_type; o = T_IRI rdfs_Resource } <: triple));
  introduce forall (u : triple). (memP u g /\ is_typed_as u rdfs_Class) ==>
      memP ({ s = u.s; p = rdfs_subClassOf; o = T_IRI rdfs_Resource } <: triple)
           (rdfs_rule_class_subclass_resource g ig)
  with introduce _ ==> _
  with _ . assert (rdfs8_concl u ==
                   Some ({ s = u.s; p = rdfs_subClassOf; o = T_IRI rdfs_Resource } <: triple));
  introduce forall (u : triple). (memP u g /\ is_typed_as u rdfs_Datatype) ==>
      memP ({ s = u.s; p = rdfs_subClassOf; o = T_IRI rdfs_Literal } <: triple)
           (rdfs_rule_datatype_subclass_literal g ig)
  with introduce _ ==> _
  with _ . assert (rdfs13_concl u ==
                   Some ({ s = u.s; p = rdfs_subClassOf; o = T_IRI rdfs_Literal } <: triple))

#pop-options

// ===================================================================
// 7. FINDING RS-1 -- FIXED 2026-07-31 (issue #335), and the witness
// re-stated against what remains.
//
// -------------------------------------------------------------------
// WHAT WAS WRONG
// -------------------------------------------------------------------
// There used to be ONE class/property harvest, shared by the RDFS
// regime and the OWL-RL regime. It treated an IRI as a class if it was
// the subject or IRI-object of an `rdfs:subClassOf` triple, OR the
// subject of `rdf:type rdfs:Class`, OR the subject of `rdf:type
// owl:Class`; the property harvest was the dual and additionally
// accepted `owl:ObjectProperty` / `owl:DatatypeProperty`.
//
// The first three sources are licensed: RDF 1.1 Semantics section 9's
// conditions put the subject and object of an `rdfs:subClassOf` triple
// in IC, ICEXT(I(rdfs:Class)) IS IC, and rdfs10 emits exactly
// `xxx rdfs:subClassOf xxx` from `xxx rdf:type rdfs:Class`.
//
// The OWL sources are NOT. `owl:Class` is an ordinary IRI to an RDFS
// interpretation; no RDFS condition relates ICEXT(I(owl:Class)) to
// ICEXT(I(rdfs:Class)). (Under the OWL 2 RDF-Based Semantics it IS
// related -- Table 5.3 -- which is why the same code is sound in the
// OWL-RL regime.) `entailment_closure`'s "RDFS" branch dispatched into
// that shared function, so one regime's licence was being spent in the
// other: a shipping-code unsoundness.
//
// -------------------------------------------------------------------
// THE FIX
// -------------------------------------------------------------------
// RDFS.Closure.fsti now carries two harvests. `collect_classes_rdfs` /
// `collect_properties_rdfs` read only the RDFS-licensed sources and
// feed `rdfs_reflexivity_axioms`, which is what
// `rdfs_closure_with_reflexivity` -- the RDFS regime's entry point --
// uses. `collect_classes` / `collect_properties` keep the wider OWL
// reading and feed `owl_reflexivity_axioms`, which
// `owl_rdfs_closure_with_reflexivity` uses and OWL.Closure calls; the
// OWL-RL regime is therefore unchanged.
//
// Two theorems below make that precise:
//
//   * `rdfs_reflexivity_axioms_licensed` -- POSITIVE. Every triple the
//     RDFS-regime harvest emits is `rdfs_licensed`. This is the fix,
//     machine-checked, and it is what the pre-fix function could not
//     have.
//   * `owl_reflexivity_axioms_not_rdfs_sound` -- the old witness,
//     re-stated. It now names the OWL-regime function, where the same
//     fact is a REGIME-SCOPE statement (do not run this in the RDFS
//     regime) rather than a bug report. `rdfs_reflexivity_axioms_owl_class_empty`
//     records that the RDFS-regime function no longer emits the triple
//     at all, so the old statement of the witness is now FALSE and has
//     been removed rather than left pointing at fixed code.
//
// The full non-entailment (no MULTI-step derivation reaches
// `c rdfs:subClassOf c` either) is argued rather than machine-checked,
// and the argument is short: from `c rdf:type owl:Class` the reachable
// conclusions are `c rdf:type rdfs:Resource` (rdfs4a / rdfs2 through
// the axiomatic `rdf:type rdfs:domain rdfs:Resource`), `owl:Class
// rdf:type rdfs:Class` (rdfs3 through the axiomatic `rdf:type
// rdfs:range rdfs:Class`), and `rdf:type rdf:type rdf:Property`
// (rdfD2). None puts `c` in ICEXT(rdfs:Class), and rdfs10 is the only
// rule whose conclusion has the shape `X rdfs:subClassOf X` from a
// single premise. See the design note.
// ===================================================================

// -------------------------------------------------------------------
// 7a. THE FIX, machine-checked: the RDFS-regime harvest emits only
// RDFS-licensed triples.
// -------------------------------------------------------------------

// Membership through the three "cons if new" helpers.
let cons_if_new_iri_memP (i : wf_iri) (acc : list wf_iri) (x : wf_iri)
  : Lemma (memP x (cons_if_new_iri i acc) ==> x == i \/ memP x acc) = ()

let cons_subject_iri_if_new_memP (s : subject) (acc : list wf_iri) (x : wf_iri)
  : Lemma (memP x (cons_subject_iri_if_new s acc) ==> s == S_IRI x \/ memP x acc) =
  match s with
  | S_IRI i -> cons_if_new_iri_memP i acc x
  | S_BNode _ -> ()

let cons_term_iri_if_new_memP (o : rdf_term) (acc : list wf_iri) (x : wf_iri)
  : Lemma (memP x (cons_term_iri_if_new o acc) ==> o == T_IRI x \/ memP x acc) =
  match o with
  | T_IRI i -> cons_if_new_iri_memP i acc x
  | T_BNode _ -> ()
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

// The two sources `collect_related_iris` reads.
let harvest_source (typing_ok : rdf_term -> bool) (rel : wf_iri)
                   (g : rdf_graph) (c : wf_iri) : prop =
  (exists (u : triple). memP u g /\ u.p == rel /\
     (u.s == S_IRI c \/ u.o == T_IRI c)) \/
  (exists (u : triple). memP u g /\ u.p == RDFS.Closure.rdf_type /\
     typing_ok u.o /\ u.s == S_IRI c)

#push-options "--z3rlimit 60"
val collect_related_iris_source (typing_ok : rdf_term -> bool) (rel : wf_iri)
                                (g : rdf_graph)
  : Lemma (ensures forall (c : wf_iri).
             memP c (collect_related_iris typing_ok rel g) ==>
             harvest_source typing_ok rel g c)

let collect_related_iris_source typing_ok rel g =
  let inv : list wf_iri -> prop =
    fun (acc : list wf_iri) ->
      forall (c : wf_iri). memP c acc ==> harvest_source typing_ok rel g c in
  let step : list wf_iri -> triple -> list wf_iri =
    fun (acc : list wf_iri) (t : triple) ->
      let acc1 =
        if t.p = rel
        then cons_term_iri_if_new t.o (cons_subject_iri_if_new t.s acc)
        else acc
      in
      if t.p = rdf_type && typing_ok t.o
      then cons_subject_iri_if_new t.s acc1
      else acc1 in
  introduce forall (acc : list wf_iri) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    let acc1 =
      if t.p = rel
      then cons_term_iri_if_new t.o (cons_subject_iri_if_new t.s acc)
      else acc in
    introduce forall (c : wf_iri). memP c acc1 ==> harvest_source typing_ok rel g c
    with introduce memP c acc1 ==> harvest_source typing_ok rel g c
    with _ . begin
      if t.p = rel then begin
        cons_term_iri_if_new_memP t.o (cons_subject_iri_if_new t.s acc) c;
        cons_subject_iri_if_new_memP t.s acc c
      end else ()
    end;
    introduce forall (c : wf_iri).
        memP c (step acc t) ==> harvest_source typing_ok rel g c
    with introduce memP c (step acc t) ==> harvest_source typing_ok rel g c
    with _ . begin
      if t.p = rdf_type && typing_ok t.o
      then cons_subject_iri_if_new_memP t.s acc1 c
      else ()
    end
  end;
  fold_left_inv inv step g [];
  assert_norm (collect_related_iris typing_ok rel g == fold_left step [] g)
#pop-options

let lemma_class_typing_rdfs (o : rdf_term)
  : Lemma (requires is_class_type_object_rdfs o)
          (ensures o == T_IRI RDFS.Closure.rdfs_Class) =
  match o with
  | T_IRI _ -> ()
  | T_BNode _ -> ()
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

let lemma_property_typing_rdfs (o : rdf_term)
  : Lemma (requires is_property_type_object_rdfs o)
          (ensures o == T_IRI RDFS.Closure.rdf_Property) =
  match o with
  | T_IRI _ -> ()
  | T_BNode _ -> ()
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

// One harvested class is licensed: either it is an endpoint of a
// subClassOf triple (the section 9 IC condition plus reflexivity on IC
// -- `rdfs_subClassOf_endpoint_refl`), or it is the subject of
// `rdf:type rdfs:Class` (rule rdfs10).
#push-options "--z3rlimit 120"
let lemma_class_refl_licensed (g : rdf_graph) (c : wf_iri)
  : Lemma (requires harvest_source is_class_type_object_rdfs rdfs_subClassOf g c)
          (ensures rdfs_licensed d_minimal g
                     ({ s = S_IRI c; p = rdfs_subClassOf; o = T_IRI c } <: triple)) =
  lemma_vocab_agree ();
  let t : triple = { s = S_IRI c; p = rdfs_subClassOf; o = T_IRI c } in
  assert (subj_term (S_IRI c) == T_IRI c);
  eliminate
    (exists (u : triple). memP u g /\ u.p == rdfs_subClassOf /\
       (u.s == S_IRI c \/ u.o == T_IRI c))
    \/
    (exists (u : triple). memP u g /\ u.p == RDFS.Closure.rdf_type /\
       is_class_type_object_rdfs u.o /\ u.s == S_IRI c)
  returns rdfs_licensed d_minimal g t
  with _ . begin
    eliminate exists (u : triple). memP u g /\ u.p == rdfs_subClassOf /\
                (u.s == S_IRI c \/ u.o == T_IRI c)
    returns rdfs_licensed d_minimal g t
    with _ . assert (rdfs_subClassOf_endpoint_refl g t)
  end
  and _ . begin
    eliminate exists (u : triple). memP u g /\ u.p == RDFS.Closure.rdf_type /\
                is_class_type_object_rdfs u.o /\ u.s == S_IRI c
    returns rdfs_licensed d_minimal g t
    with _ . begin
      lemma_class_typing_rdfs u.o;
      assert (rdfs10_derives g t)
    end
  end

let lemma_property_refl_licensed (g : rdf_graph) (p : wf_iri)
  : Lemma (requires harvest_source is_property_type_object_rdfs rdfs_subPropertyOf g p)
          (ensures rdfs_licensed d_minimal g
                     ({ s = S_IRI p; p = rdfs_subPropertyOf; o = T_IRI p } <: triple)) =
  lemma_vocab_agree ();
  let t : triple = { s = S_IRI p; p = rdfs_subPropertyOf; o = T_IRI p } in
  assert (subj_term (S_IRI p) == T_IRI p);
  eliminate
    (exists (u : triple). memP u g /\ u.p == rdfs_subPropertyOf /\
       (u.s == S_IRI p \/ u.o == T_IRI p))
    \/
    (exists (u : triple). memP u g /\ u.p == RDFS.Closure.rdf_type /\
       is_property_type_object_rdfs u.o /\ u.s == S_IRI p)
  returns rdfs_licensed d_minimal g t
  with _ . begin
    eliminate exists (u : triple). memP u g /\ u.p == rdfs_subPropertyOf /\
                (u.s == S_IRI p \/ u.o == T_IRI p)
    returns rdfs_licensed d_minimal g t
    with _ . assert (rdfs_subPropertyOf_endpoint_refl g t)
  end
  and _ . begin
    eliminate exists (u : triple). memP u g /\ u.p == RDFS.Closure.rdf_type /\
                is_property_type_object_rdfs u.o /\ u.s == S_IRI p
    returns rdfs_licensed d_minimal g t
    with _ . begin
      lemma_property_typing_rdfs u.o;
      assert (rdfs6_derives g t)
    end
  end
#pop-options

// THE FIX, stated. Every triple the RDFS-regime reflexivity harvest
// emits is licensed by RDF 1.1 Semantics section 9.
#push-options "--z3rlimit 180"
val rdfs_reflexivity_axioms_licensed (g : rdf_graph)
  : Lemma (ensures forall (t : triple).
             memP t (rdfs_reflexivity_axioms g) ==> rdfs_licensed d_minimal g t)

let rdfs_reflexivity_axioms_licensed g =
  let classes = collect_classes_rdfs g in
  let properties = collect_properties_rdfs g in
  let class_f : wf_iri -> triple =
    fun (c : wf_iri) -> ({ s = S_IRI c; p = rdfs_subClassOf; o = T_IRI c } <: triple) in
  let prop_f : wf_iri -> triple =
    fun (p : wf_iri) -> ({ s = S_IRI p; p = rdfs_subPropertyOf; o = T_IRI p } <: triple) in
  let class_triples : rdf_graph = map class_f classes in
  let property_triples : rdf_graph = map prop_f properties in
  collect_related_iris_source is_class_type_object_rdfs rdfs_subClassOf g;
  collect_related_iris_source is_property_type_object_rdfs rdfs_subPropertyOf g;
  assert (rdfs_reflexivity_axioms g == class_triples @ property_triples);
  introduce forall (t : triple).
      memP t (rdfs_reflexivity_axioms g) ==> rdfs_licensed d_minimal g t
  with introduce memP t (rdfs_reflexivity_axioms g) ==> rdfs_licensed d_minimal g t
  with _ . begin
    append_memP class_triples property_triples t;
    let from_classes () : Lemma (requires memP t class_triples)
                                (ensures rdfs_licensed d_minimal g t) =
      memP_map_elim class_f t classes;
      eliminate exists (c : wf_iri). memP c classes /\ class_f c == t
      returns rdfs_licensed d_minimal g t
      with _ . lemma_class_refl_licensed g c
    in
    let from_properties () : Lemma (requires memP t property_triples)
                                   (ensures rdfs_licensed d_minimal g t) =
      memP_map_elim prop_f t properties;
      eliminate exists (p : wf_iri). memP p properties /\ prop_f p == t
      returns rdfs_licensed d_minimal g t
      with _ . lemma_property_refl_licensed g p
    in
    FStar.Classical.move_requires from_classes ();
    FStar.Classical.move_requires from_properties ()
  end
#pop-options

// -------------------------------------------------------------------
// 7b. The old witness, re-stated. The RDFS-regime harvest is now
// EMPTY on the witness graph.
// -------------------------------------------------------------------
#push-options "--fuel 8 --z3rlimit 60"
val rdfs_reflexivity_axioms_owl_class_empty (c : wf_iri)
  : Lemma (rdfs_reflexivity_axioms (owl_class_graph c) == [])

let rdfs_reflexivity_axioms_owl_class_empty c =
  assert_norm (collect_classes_rdfs (owl_class_graph c) == []);
  assert_norm (collect_properties_rdfs (owl_class_graph c) == []);
  assert_norm (rdfs_reflexivity_axioms (owl_class_graph c) == [])
#pop-options

// The OWL-regime harvest still emits it.
#push-options "--fuel 8 --z3rlimit 60"
val owl_reflexivity_axioms_emit_owl_class (c : wf_iri)
  : Lemma (memP (owl_class_refl_triple c)
                (owl_reflexivity_axioms (owl_class_graph c)))

let owl_reflexivity_axioms_emit_owl_class c =
  assert_norm (collect_classes (owl_class_graph c) == [c]);
  assert_norm (collect_properties (owl_class_graph c) == []);
  assert_norm (owl_reflexivity_axioms (owl_class_graph c) ==
               [ owl_class_refl_triple c ])
#pop-options


// -------------------------------------------------------------------
// THE WITNESS, re-stated against the OWL-regime function. Not licensed
// by any row of either rule table -- which is exactly why the RDFS
// regime must not call it, and no longer does.
// -------------------------------------------------------------------
#push-options "--fuel 8 --ifuel 2 --z3rlimit 240"
val owl_reflexivity_axioms_not_rdfs_sound (c : wf_iri)
  : Lemma (memP (owl_class_refl_triple c)
                (owl_reflexivity_axioms (owl_class_graph c)) /\
           ~(rdfs_licensed d_minimal (owl_class_graph c) (owl_class_refl_triple c)))

let owl_reflexivity_axioms_not_rdfs_sound c =
  owl_reflexivity_axioms_emit_owl_class c;
  selfloop_not_axiomatic c;
  lemma_vocab_agree ();
  assert_norm (i_rdfs_subClassOf =!= i_rdf_type);
  assert_norm (i_rdfs_subClassOf =!= i_rdfs_subPropertyOf);
  assert_norm (owl_Class =!= i_rdfs_Class);
  assert_norm (owl_Class =!= i_rdf_Property);
  assert_norm (owl_Class =!= i_rdfs_Datatype);
  assert_norm (owl_Class =!= i_rdfs_ContainerMembershipProperty);
  // The graph's single triple has predicate rdf:type, so every rule
  // whose premise demands rdfs:domain / rdfs:range / rdfs:subClassOf /
  // rdfs:subPropertyOf has no premise to fire on; every rule whose
  // conclusion has predicate rdf:type or rdfs:subPropertyOf produces a
  // differently-shaped triple; and the four rules that CAN conclude an
  // rdfs:subClassOf triple (rdfs8, rdfs10, rdfs11, rdfs13) all demand
  // an object that is rdfs:Class or rdfs:Datatype, not owl:Class.
  assert (~(rdfs_licensed d_minimal (owl_class_graph c) (owl_class_refl_triple c)))
#pop-options
