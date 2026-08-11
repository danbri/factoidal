module RDF.Entailment.Simple.Refinement

// ===================================================================
// REFINEMENT: the shipping backtracking search in
// RDF.Entailment.Simple.fst is SOUND and COMPLETE with respect to the
// independent declarative specification in
// RDF.Entailment.Simple.Spec.fst.
//
// Every theorem below names the SHIPPING function `simple_entails`
// (and the shipping matchers it is built from) -- there is no model of
// the algorithm here, only the algorithm.
//
// Issue #318 / epic #313. Design doc:
// docs/designissues/2026-07-29-simple-entailment-refinement.md.
//
// -------------------------------------------------------------------
// RESULT SUMMARY
// -------------------------------------------------------------------
//   simple_entails_complete   UNCONDITIONAL.
//       simple_entailment_spec a b ==> simple_entails a b == true
//
//   simple_entails_sound      CONDITIONAL on `graph_exact` (both
//       graphs). simple_entails a b == true ==> spec a b
//
//   simple_entails_not_sound_unconditionally
//       A machine-checked WITNESS that the `graph_exact` side
//       condition on soundness cannot be dropped: two graphs the
//       shipping engine says entail, which do NOT stand in the simple
//       entailment relation. See finding SE-1 in the design doc.
//
// The asymmetry has one cause: the shipping literal test `literal_eq`
// is strictly COARSER than RDF literal term equality (case-insensitive
// language tags; exclusive-canonical-XML comparison of two
// rdf:XMLLiteral-typed literals). A coarser test accepts everything
// the specification demands -- hence unconditional completeness -- and
// also accepts some things it does not -- hence the side condition on
// soundness. `graph_exact` (Spec module) names exactly the literals on
// which the two coincide.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph.Executable
open RDF.Entailment.Simple
open RDF.Entailment.Simple.Spec

// ===================================================================
// 0. Bridging the two `subject`-as-term spellings.
// ===================================================================

let lemma_subj_terms_agree (s : subject)
  : Lemma (subj_term s == subj_as_term s) =
  match s with
  | S_IRI _ -> ()
  | S_BNode _ -> ()

// ===================================================================
// 1. Where the shipping boolean equalities ARE term identity.
// ===================================================================

// `literal_eq` decides literal term identity on the `lit_exact`
// fragment: neither the exclusive-canonical-XML branch (needs BOTH
// operands rdf:XMLLiteral-typed) nor the case-folding language-tag
// branch (needs a tag that is not already lowercase) can fire.
let lemma_literal_eq_exact (l1 l2 : literal)
  : Lemma (requires lit_exact l1 /\ lit_exact l2 /\ literal_eq l1 l2 == true)
          (ensures l1 == l2) =
  assert (l1.lexical_form == l2.lexical_form);
  assert (l1.datatype == l2.datatype);
  assert (l1.direction == l2.direction);
  (match l1.lang_tag, l2.lang_tag with
   | None, None -> ()
   | Some t1, Some t2 ->
     assert (FStar.String.lowercase t1 == t1);
     assert (FStar.String.lowercase t2 == t2);
     assert (FStar.String.lowercase t1 == FStar.String.lowercase t2)
   | _, _ -> ());
  assert (l1.lang_tag == l2.lang_tag)

let lemma_subject_eq_identity (s1 s2 : subject)
  : Lemma (requires subject_eq s1 s2 == true) (ensures s1 == s2) =
  match s1, s2 with
  | S_IRI _, S_IRI _ -> ()
  | S_BNode _, S_BNode _ -> ()
  | _, _ -> ()

let rec lemma_rdf_term_eq_exact_identity (t1 t2 : rdf_term)
  : Lemma (requires term_exact t1 /\ term_exact t2 /\ rdf_term_eq t1 t2 == true)
          (ensures t1 == t2)
          (decreases t1) =
  match t1, t2 with
  | T_IRI _, T_IRI _ -> ()
  | T_BNode _, T_BNode _ -> ()
  | T_Literal l1, T_Literal l2 -> lemma_literal_eq_exact l1 l2
  | T_TripleTerm s1 _ o1, T_TripleTerm s2 _ o2 ->
    lemma_subject_eq_identity s1 s2;
    lemma_rdf_term_eq_exact_identity o1 o2
  | _, _ -> ()

// ===================================================================
// 2. Bindings viewed as substitutions.
//
// The search threads a `binding` (an association list built by
// consing). `bsubst` reads it as a spec-level `bnode_subst`;
// `binding_extends` is the growth relation the search maintains
// (never rebinding a bound label, because `assoc` returns the first
// hit and the matchers only cons when `assoc` returned `None`).
// ===================================================================

let bsubst (bd : binding) : bnode_subst =
  fun l -> match assoc l bd with
        | Some t -> t
        | None   -> T_BNode l

// `bd2` preserves every binding of `bd1`.
let binding_extends (bd2 bd1 : binding) : prop =
  forall (l : bnode_id). Some? (assoc l bd1) ==> assoc l bd2 == assoc l bd1

// `bd` never contradicts the substitution `m`.
let binding_compat (m : bnode_subst) (bd : binding) : prop =
  forall (l : bnode_id) (t : rdf_term). assoc l bd == Some t ==> m l == t

// Every term the binding holds lies in the exact-literal fragment.
// Maintained because the matchers only ever bind terms drawn from the
// ENTAILING graph `a`.
let binding_exact (bd : binding) : prop =
  forall (l : bnode_id) (t : rdf_term). assoc l bd == Some t ==> term_exact t

let lemma_binding_extends_refl (bd : binding)
  : Lemma (binding_extends bd bd) = ()

let lemma_binding_extends_trans (bd3 bd2 bd1 : binding)
  : Lemma (requires binding_extends bd3 bd2 /\ binding_extends bd2 bd1)
          (ensures binding_extends bd3 bd1) = ()

// ===================================================================
// 3. Hypotheses on the two predicate parameters of the shipping
// engine (`entails_with` is parameterized by a literal test `leq` and
// a blank-node-range test `bnd`; `simple_entails` instantiates them at
// `literal_eq` and "always"). Stating the proofs against the
// parameters means the RDF/RDFS D-entailment layer in
// RDF.Entailment.Regime.fst can reuse them by discharging these
// hypotheses for its own instantiation.
// ===================================================================

let leq_reflexive (leq : bool -> literal -> literal -> bool) : prop =
  forall (ins : bool) (l : literal). leq ins l l == true

let leq_exact_identity (leq : bool -> literal -> literal -> bool) : prop =
  forall (ins : bool) (l1 l2 : literal).
    lit_exact l1 ==> lit_exact l2 ==> leq ins l1 l2 == true ==> l1 == l2

// Strictly stronger than `leq_exact_identity`: decides literal identity
// with NO side condition on literal content at all (drops the
// `lit_exact` antecedents). `literal_term_eq` (issue #324 / SE-1)
// satisfies this; `literal_eq` does not (that gap is exactly the SE-1
// defect). Used below for the ground-fragment soundness corollary,
// which needs no `graph_exact` hypothesis at all.
let leq_always_identity (leq : bool -> literal -> literal -> bool) : prop =
  forall (ins : bool) (l1 l2 : literal). leq ins l1 l2 == true ==> l1 == l2

let bnd_total (bnd : rdf_term -> bool) : prop =
  forall (t : rdf_term). bnd t == true

// ===================================================================
// 4. COMPLETENESS.
//
// Given a substitution M witnessing the specification, the search
// finds SOME solution -- not necessarily M's. The invariant carried
// down the search is `binding_compat m bd`: the partial binding built
// so far agrees with M. Under that invariant the "right" candidate
// (the M-image of the pattern triple) always matches, so the
// alternatives loop cannot exhaust before reaching it.
// ===================================================================

let lemma_match_subj_complete (m : bnode_subst) (bd : binding)
                              (ps : subject) (gs : subject)
  : Lemma (requires binding_compat m bd /\ subj_inst m ps gs)
          (ensures (match match_subj bd ps gs with
                    | Some bd1 -> binding_compat m bd1
                    | None     -> False)) =
  lemma_subj_terms_agree gs;
  match ps with
  | S_IRI _ -> ()
  | S_BNode lbl ->
    (match assoc lbl bd with
     | Some t -> lemma_rdf_term_eq_refl t
     | None   -> ())

let rec lemma_match_term_complete (leq : bool -> literal -> literal -> bool)
                                  (bnd : rdf_term -> bool)
                                  (m : bnode_subst) (inside : bool)
                                  (bd : binding) (pat : rdf_term) (g : rdf_term)
  : Lemma (requires leq_reflexive leq /\ bnd_total bnd /\
                    binding_compat m bd /\ term_inst m pat g)
          (ensures (match match_term leq bnd inside bd pat g with
                    | Some bd1 -> binding_compat m bd1
                    | None     -> False))
          (decreases pat) =
  match pat with
  | T_BNode lbl ->
    (match assoc lbl bd with
     | Some t -> lemma_rdf_term_eq_refl t
     | None   -> ())
  | T_IRI _ -> ()
  | T_Literal _ -> ()
  | T_TripleTerm ps pp po ->
    eliminate exists (gs : subject) (go : rdf_term).
        g == T_TripleTerm gs pp go /\ subj_inst m ps gs /\ term_inst m po go
    returns (match match_term leq bnd inside bd pat g with
             | Some bd1 -> binding_compat m bd1
             | None     -> False)
    with _pf.
      (lemma_match_subj_complete m bd ps gs;
       match match_subj bd ps gs with
       | Some bd1 -> lemma_match_term_complete leq bnd m true bd1 po go
       | None     -> ())

let lemma_match_triple_complete (leq : bool -> literal -> literal -> bool)
                                (bnd : rdf_term -> bool)
                                (m : bnode_subst) (bd : binding)
                                (tb : triple) (ta : triple)
  : Lemma (requires leq_reflexive leq /\ bnd_total bnd /\
                    binding_compat m bd /\ triple_inst m tb ta)
          (ensures (match match_triple leq bnd bd tb ta with
                    | Some bd1 -> binding_compat m bd1
                    | None     -> False)) =
  lemma_match_subj_complete m bd tb.s ta.s;
  match match_subj bd tb.s ta.s with
  | Some bd1 -> lemma_match_term_complete leq bnd m false bd1 tb.o ta.o
  | None     -> ()

// The B-side obligation carried by the search, phrased once.
let all_matched (m : bnode_subst) (bs : list triple) (a : list triple) : prop =
  forall (tb : triple). memP tb bs ==>
    (exists (ta : triple). memP ta a /\ triple_inst m tb ta)

let rec lemma_try_match_complete (leq : bool -> literal -> literal -> bool)
                                 (bnd : rdf_term -> bool)
                                 (m : bnode_subst)
                                 (bs : list triple) (bd : binding) (a : list triple)
  : Lemma (requires leq_reflexive leq /\ bnd_total bnd /\
                    binding_compat m bd /\ all_matched m bs a)
          (ensures try_match leq bnd bs bd a == true)
          (decreases %[length bs; 1 + length a]) =
  match bs with
  | [] -> ()
  | tb :: rest ->
    assert (memP tb bs);
    lemma_try_alts_complete leq bnd m bs tb rest bd a a

and lemma_try_alts_complete (leq : bool -> literal -> literal -> bool)
                            (bnd : rdf_term -> bool)
                            (m : bnode_subst)
                            (bs : list triple) (tb : triple)
                            (rest : list triple { length rest < length bs })
                            (bd : binding) (a : list triple) (cand : list triple)
  : Lemma (requires leq_reflexive leq /\ bnd_total bnd /\
                    binding_compat m bd /\ all_matched m rest a /\
                    (exists (ta : triple). memP ta cand /\ triple_inst m tb ta))
          (ensures try_alts leq bnd bs tb rest bd a cand == true)
          (decreases %[length bs; length cand]) =
  match cand with
  | [] -> ()
  | ta0 :: more ->
    eliminate exists (ta : triple). memP ta cand /\ triple_inst m tb ta
    returns (try_alts leq bnd bs tb rest bd a cand == true)
    with _pf.
      (eliminate (ta == ta0) \/ (memP ta more)
       returns (try_alts leq bnd bs tb rest bd a cand == true)
       with _hd.
         (lemma_match_triple_complete leq bnd m bd tb ta0;
          match match_triple leq bnd bd tb ta0 with
          | Some bd1 -> lemma_try_match_complete leq bnd m rest bd1 a
          | None     -> ())
       and _tl.
         lemma_try_alts_complete leq bnd m bs tb rest bd a more)

// -------------------------------------------------------------------
// The shipping instantiation: `simple_entails` passes
// `fun _ l m -> literal_term_eq l m` and `fun _ -> true` (issue #324 /
// SE-1 -- was `literal_eq`, the D-entailment-flavoured coarsening;
// see RDF.Entailment.Simple.fst's banner).
// -------------------------------------------------------------------

// `unfold` (not a plain `let`): the theorems below must be about the
// EXACT text `simple_entails` runs, so these two names have to melt
// away at typechecking rather than stand as opaque symbols the SMT
// encoding cannot relate to the shipping lambdas (design-doc finding
// F3 in the OWL pilot, same trap).
unfold let simple_leq : bool -> literal -> literal -> bool =
  fun _ l m -> literal_term_eq l m

unfold let simple_bnd : rdf_term -> bool = fun _ -> true

let lemma_simple_leq_reflexive (_ : unit) : Lemma (leq_reflexive simple_leq) =
  FStar.Classical.forall_intro lemma_literal_term_eq_refl

let lemma_simple_bnd_total (_ : unit) : Lemma (bnd_total simple_bnd) = ()

// `literal_term_eq` decides literal term identity UNCONDITIONALLY, so
// `simple_leq` satisfies the stronger `leq_always_identity` (below) and
// hence the weaker `leq_exact_identity` the shared refinement lemmas
// ask for -- no `lit_exact` hypotheses needed on either side.
let lemma_simple_leq_always_identity (_ : unit) : Lemma (leq_always_identity simple_leq) =
  let aux (l1 l2 : literal) : Lemma (literal_term_eq l1 l2 == true ==> l1 == l2) =
    FStar.Classical.move_requires_2
      (fun (x : literal) (y : literal) -> lemma_literal_term_eq_identity x y)
      l1 l2
  in
  FStar.Classical.forall_intro_2 aux

let lemma_simple_leq_exact_identity (_ : unit) : Lemma (leq_exact_identity simple_leq) =
  lemma_simple_leq_always_identity ()

// `simple_entails` unfolds to the parameterized engine at these two
// arguments. Pinned by `assert_norm` so the theorems below are about
// the exact shipping text, not a restatement of it.
let lemma_simple_entails_unfold (a b : list triple)
  : Lemma (simple_entails a b == try_match simple_leq simple_bnd b [] a) = ()

// ===================================================================
// THEOREM (completeness). If graph A simply entails graph B in the
// declarative sense of RDF.Entailment.Simple.Spec, the shipping
// search returns true. No side conditions.
// ===================================================================
let simple_entails_complete (a b : list triple)
  : Lemma (requires simple_entailment_spec a b)
          (ensures  simple_entails a b == true) =
  lemma_simple_leq_reflexive ();
  lemma_simple_bnd_total ();
  lemma_simple_entails_unfold a b;
  eliminate exists (m : bnode_subst).
      (forall (tb : triple). memP tb b ==>
         (exists (ta : triple). memP ta a /\ triple_inst m tb ta))
  returns (simple_entails a b == true)
  with _pf.
    (assert (binding_compat m []);
     assert (all_matched m b a);
     lemma_try_match_complete simple_leq simple_bnd m b [] a)

// ===================================================================
// 5. SOUNDNESS.
//
// The search returns only a boolean, so the witnessing substitution
// has to be RECONSTRUCTED from the binding the successful branch
// built. The reconstruction is `bsubst`, and the statement that makes
// the induction go through is the second conjunct below: the match
// result is stable under ANY later extension of the binding, so the
// substitution read off the FINAL binding of the whole search still
// explains every triple matched earlier.
// ===================================================================

let lemma_match_subj_sound (bd : binding) (ps : subject) (gs : subject)
  : Lemma (requires binding_exact bd /\ Some? (match_subj bd ps gs))
          (ensures (let bd1 = Some?.v (match_subj bd ps gs) in
                    binding_extends bd1 bd /\ binding_exact bd1 /\
                    (forall (bd2 : binding). binding_extends bd2 bd1 ==>
                       subj_inst (bsubst bd2) ps gs))) =
  lemma_subj_terms_agree gs;
  match ps with
  | S_IRI _ -> ()
  | S_BNode lbl ->
    (match assoc lbl bd with
     | Some t ->
       assert (term_exact t);
       assert (term_exact (subj_as_term gs));
       lemma_rdf_term_eq_exact_identity t (subj_as_term gs)
     | None -> ())

let rec lemma_match_term_sound (leq : bool -> literal -> literal -> bool)
                               (bnd : rdf_term -> bool)
                               (inside : bool) (bd : binding)
                               (pat : rdf_term) (g : rdf_term)
  : Lemma (requires leq_exact_identity leq /\ binding_exact bd /\
                    term_exact pat /\ term_exact g /\
                    Some? (match_term leq bnd inside bd pat g))
          (ensures (let bd1 = Some?.v (match_term leq bnd inside bd pat g) in
                    binding_extends bd1 bd /\ binding_exact bd1 /\
                    (forall (bd2 : binding). binding_extends bd2 bd1 ==>
                       term_inst (bsubst bd2) pat g)))
          (decreases pat) =
  match pat with
  | T_BNode lbl ->
    (match assoc lbl bd with
     | Some t -> lemma_rdf_term_eq_exact_identity t g
     | None   -> ())
  | T_IRI _ -> ()
  | T_Literal l ->
    (match g with
     | T_Literal mlit -> assert (leq inside l mlit == true)
     | _ -> ())
  | T_TripleTerm ps pp po ->
    (match g with
     | T_TripleTerm gs gp go ->
       if pp = gp then
         (lemma_match_subj_sound bd ps gs;
          match match_subj bd ps gs with
          | Some bdS ->
            lemma_match_term_sound leq bnd true bdS po go;
            (match match_term leq bnd true bdS po go with
             | Some bd1 ->
               let aux (bd2 : binding)
                 : Lemma (requires binding_extends bd2 bd1)
                         (ensures term_inst (bsubst bd2) pat g) =
                 lemma_binding_extends_trans bd2 bd1 bdS;
                 assert (subj_inst (bsubst bd2) ps gs);
                 assert (term_inst (bsubst bd2) po go);
                 assert (g == T_TripleTerm gs pp go)
               in
               FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
             | None -> ())
          | None -> ())
       else ()
     | _ -> ())

let lemma_match_triple_sound (leq : bool -> literal -> literal -> bool)
                             (bnd : rdf_term -> bool)
                             (bd : binding) (tb : triple) (ta : triple)
  : Lemma (requires leq_exact_identity leq /\ binding_exact bd /\
                    triple_exact tb /\ triple_exact ta /\
                    Some? (match_triple leq bnd bd tb ta))
          (ensures (let bd1 = Some?.v (match_triple leq bnd bd tb ta) in
                    binding_extends bd1 bd /\ binding_exact bd1 /\
                    (forall (bd2 : binding). binding_extends bd2 bd1 ==>
                       triple_inst (bsubst bd2) tb ta))) =
  lemma_match_subj_sound bd tb.s ta.s;
  match match_subj bd tb.s ta.s with
  | Some bdS ->
    lemma_match_term_sound leq bnd false bdS tb.o ta.o;
    (match match_term leq bnd false bdS tb.o ta.o with
     | Some bd1 ->
       let aux (bd2 : binding)
         : Lemma (requires binding_extends bd2 bd1)
                 (ensures triple_inst (bsubst bd2) tb ta) =
         lemma_binding_extends_trans bd2 bd1 bdS
       in
       FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
     | None -> ())
  | None -> ()

// The post-condition of a successful search: some final binding that
// extends the one we started from and explains every remaining
// B-triple by a real A-triple.
let search_witness (bs : list triple) (bd : binding) (a : list triple) : prop =
  exists (bd' : binding).
    binding_extends bd' bd /\ binding_exact bd' /\ all_matched (bsubst bd') bs a

let rec lemma_try_match_sound (leq : bool -> literal -> literal -> bool)
                              (bnd : rdf_term -> bool)
                              (bs : list triple) (bd : binding) (a : list triple)
  : Lemma (requires leq_exact_identity leq /\ binding_exact bd /\
                    graph_exact a /\ graph_exact bs /\
                    try_match leq bnd bs bd a == true)
          (ensures search_witness bs bd a)
          (decreases %[length bs; 1 + length a]) =
  match bs with
  | [] -> assert (all_matched (bsubst bd) [] a)
  | tb :: rest ->
    assert (memP tb bs);
    assert (forall (t : triple). memP t rest ==> memP t bs);
    lemma_try_alts_sound leq bnd bs tb rest bd a a

and lemma_try_alts_sound (leq : bool -> literal -> literal -> bool)
                         (bnd : rdf_term -> bool)
                         (bs : list triple) (tb : triple)
                         (rest : list triple { length rest < length bs })
                         (bd : binding) (a : list triple) (cand : list triple)
  : Lemma (requires leq_exact_identity leq /\ binding_exact bd /\
                    graph_exact a /\ triple_exact tb /\ graph_exact rest /\
                    is_subgraph cand a /\
                    try_alts leq bnd bs tb rest bd a cand == true)
          (ensures search_witness (tb :: rest) bd a)
          (decreases %[length bs; length cand]) =
  match cand with
  | [] -> ()
  | ta0 :: more ->
    assert (memP ta0 a);
    assert (triple_exact ta0);
    assert (is_subgraph more a);
    (match match_triple leq bnd bd tb ta0 with
     | Some bd1 ->
       if try_match leq bnd rest bd1 a then begin
         lemma_match_triple_sound leq bnd bd tb ta0;
         lemma_try_match_sound leq bnd rest bd1 a;
         eliminate exists (bd' : binding).
             binding_extends bd' bd1 /\ binding_exact bd' /\
             all_matched (bsubst bd') rest a
         returns (search_witness (tb :: rest) bd a)
         with _pf.
           (lemma_binding_extends_trans bd' bd1 bd;
            assert (triple_inst (bsubst bd') tb ta0);
            assert (all_matched (bsubst bd') (tb :: rest) a))
       end
       else lemma_try_alts_sound leq bnd bs tb rest bd a more
     | None -> lemma_try_alts_sound leq bnd bs tb rest bd a more)

// ===================================================================
// THEOREM (soundness, on the exact-literal fragment). If the shipping
// search returns true on graphs whose literals are outside the two
// coarsening branches of `literal_eq`, then graph A simply entails
// graph B in the declarative sense.
//
// SCOPE OF THE SIDE CONDITION: `graph_exact g` says no literal in `g`
// is rdf:XMLLiteral-typed and every language tag is already lowercase.
// It is NOT vacuous and it is NOT removable -- see
// `simple_entails_not_sound_unconditionally` below.
// ===================================================================
let simple_entails_sound (a b : list triple)
  : Lemma (requires simple_entails a b == true /\ graph_exact a /\ graph_exact b)
          (ensures  simple_entailment_spec a b) =
  lemma_simple_leq_exact_identity ();
  lemma_simple_entails_unfold a b;
  assert (binding_exact []);
  lemma_try_match_sound simple_leq simple_bnd b [] a;
  eliminate exists (bd' : binding).
      binding_extends bd' [] /\ binding_exact bd' /\ all_matched (bsubst bd') b a
  returns (simple_entailment_spec a b)
  with _pf.
    assert (simple_entailment_spec a b)

// ===================================================================
// THEOREMS at the PARAMETERIZED engine `entails_with`.
//
// `simple_entails` is one instantiation of `entails_with`. The W3C
// runner's entailment path goes through OTHER instantiations
// (RDF.Entailment.Regime's `entails_rdf` / `entails_rdfs` /
// `entails_rdfs_plus`, which pass `dt_value_leq` and `bnd_rdf`) -- see
// finding SE-3 in the design doc. These two theorems are the same
// refinement result stated for ANY instantiation, so a follow-up only
// has to discharge the three hypotheses for its own predicates.
// ===================================================================

let entails_with_complete (leq : bool -> literal -> literal -> bool)
                          (bnd : rdf_term -> bool) (a b : list triple)
  : Lemma (requires leq_reflexive leq /\ bnd_total bnd /\ simple_entailment_spec a b)
          (ensures  entails_with leq bnd a b == true) =
  eliminate exists (m : bnode_subst).
      (forall (tb : triple). memP tb b ==>
         (exists (ta : triple). memP ta a /\ triple_inst m tb ta))
  returns (entails_with leq bnd a b == true)
  with _pf.
    (assert (binding_compat m []);
     assert (all_matched m b a);
     lemma_try_match_complete leq bnd m b [] a)

let entails_with_sound (leq : bool -> literal -> literal -> bool)
                       (bnd : rdf_term -> bool) (a b : list triple)
  : Lemma (requires leq_exact_identity leq /\ graph_exact a /\ graph_exact b /\
                    entails_with leq bnd a b == true)
          (ensures  simple_entailment_spec a b) =
  assert (binding_exact []);
  lemma_try_match_sound leq bnd b [] a;
  eliminate exists (bd' : binding).
      binding_extends bd' [] /\ binding_exact bd' /\ all_matched (bsubst bd') b a
  returns (simple_entailment_spec a b)
  with _pf.
    assert (simple_entailment_spec a b)

// ===================================================================
// COROLLARY (decision procedure, on the exact-literal fragment).
// ===================================================================
let simple_entails_iff_spec (a b : list triple)
  : Lemma (requires graph_exact a /\ graph_exact b)
          (ensures  (simple_entails a b == true) <==> simple_entailment_spec a b) =
  FStar.Classical.move_requires_2
    (fun (x : list triple) (y : list triple) -> simple_entails_sound x y) a b;
  FStar.Classical.move_requires_2
    (fun (x : list triple) (y : list triple) -> simple_entails_complete x y) a b

// ===================================================================
// 6. FINDING SE-1 -- FIXED (issue #324).
//
// HISTORY. `simple_entails` used to instantiate `entails_with`'s `leq`
// parameter with `literal_eq`, which compares language tags
// case-insensitively (`lang_tag_eq t1 t2 = lowercase t1 = lowercase
// t2`) and canonicalizes rdf:XMLLiteral pairs via exclusive c14n. RDF
// 1.1 Concepts section 3.3 makes literal TERM equality character-by-
// character, so `"x"@en` and `"x"@EN` are DIFFERENT literal terms with
// the same value; simple interpretations (RDF 1.1 Semantics section 5)
// place no constraint tying the two denotations together -- value
// equality of language-tagged strings is an RDF-interpretation
// (D-entailment) condition, not a simple one. So a graph asserting
// `"x"@en` does NOT simply entail the same graph with `"x"@EN`, but the
// old shipping engine said it did -- a soundness bug, machine-checked
// below at `simple_entails_se1_regression`, which used to prove the
// ACCEPTING direction (`simple_entails ga gb == true`) alongside the
// spec-side refutation; it now proves the REJECTING direction, because
// `simple_entails` passes strict `literal_term_eq` (RDF 1.1 Concepts
// section 3.3 literal term equality -- lexical form, datatype,
// language tag, and direction all compare exactly) instead.
//
// The same divergence existed for rdf:XMLLiteral (`literal_eq` routes
// two XMLLiteral-typed literals through `xmlc_canonicalize`); not
// separately witnessed here (same shape, same fix), and closed by the
// same swap since `literal_term_eq` does not canonicalize XMLLiteral
// either.
//
// RESIDUAL (documented, not closed by this fix -- see
// RDF.Entailment.Simple.fst's banner): blank-node REBIND consistency
// (a pattern blank node seen twice must denote the SAME ground term)
// is checked by `match_term`'s hardcoded `rdf_term_eq`, which still
// routes literal comparison through the coarser `literal_eq` -- that
// call site is not parameterized by `leq` at all. So a pattern that
// reuses one blank node across two literal ground terms differing only
// by language-tag case or XMLLiteral canonical form could still be
// accepted wrongly. No fixture in the tree exercises this (rdf-mt/
// W3C suites do not reuse a blank node across differently-cased
// literals), and fixing it would mean threading a THIRD predicate
// through `match_term`/`match_subj`/`try_match`/`try_alts` (shared
// with `RDF.Entailment.Regime`'s D-entailment instantiation, which
// deliberately wants the coarser test) -- out of scope for this
// change; tracked as a residual note against #324, not a separate
// issue, until it has a witness. `simple_entails_sound` below keeps
// its `graph_exact` side condition for exactly this reason: it is
// the ONLY reason left, now that the literal-ACCEPTANCE test
// (`leq`) is unconditionally exact -- see the ground-fragment
// corollary (section 8) for the class of graphs (`graph_ground b`,
// which never exercises the bnode-rebind path at all) where the
// side condition is now provably unnecessary.
// ===================================================================

let se1_lit (lex : string) (tag : string) : literal =
  { lexical_form = lex; datatype = rdf_lang_string;
    lang_tag = Some tag; direction = None }

let lemma_se1_lit_wf (lex tag : string) : Lemma (literal_wf (se1_lit lex tag)) = ()

// REGRESSION PIN (issue #324 / SE-1). Same graphs as the original
// witness (a language tag differing only by case -- "EN" vs "en" is
// the reader-facing instance the `lowercase` hypothesis lets us keep
// stating without F* reducing string constants); the outcome is now
// the CORRECT one on both sides, and they AGREE:
//   - `simple_entails ga gb == false`: the shipping engine now
//     rejects the pair it used to wrongly accept.
//   - `~(simple_entailment_spec ga gb)`: the declarative spec always
//     said this pair does not entail (unchanged by this fix -- the
//     spec was never the buggy side).
// `tag1 =!= tag2` alone already makes the two literals distinct terms
// (case-insensitivity is not needed for the disproof); the `lowercase`
// hypothesis is kept only to pin the exact historical counterexample
// shape on record.
let simple_entails_se1_regression
      (s : wf_iri) (p : wf_iri) (tag1 tag2 : string)
  : Lemma (requires FStar.String.lowercase tag1 == FStar.String.lowercase tag2 /\
                    tag1 =!= tag2)
          (ensures (
            let l1 = se1_lit "x" tag1 in
            let l2 = se1_lit "x" tag2 in
            let ga = [ { s = S_IRI s; p = p; o = T_Literal l1 } ] in
            let gb = [ { s = S_IRI s; p = p; o = T_Literal l2 } ] in
            simple_entails ga gb == false /\ ~(simple_entailment_spec ga gb))) =
  let l1 = se1_lit "x" tag1 in
  let l2 = se1_lit "x" tag2 in
  let ga = [ { s = S_IRI s; p = p; o = T_Literal l1 } ] in
  let gb = [ { s = S_IRI s; p = p; o = T_Literal l2 } ] in
  lemma_simple_entails_unfold ga gb;
  assert (l1.lang_tag =!= l2.lang_tag);
  assert (l1 =!= l2);
  assert (literal_term_eq l2 l1 == false);
  assert (simple_entails ga gb == false);
  // The spec side: gb's only triple is ground, so no substitution can
  // help; `term_inst m (T_Literal l2) (T_Literal l1)` demands
  // T_Literal l1 == T_Literal l2, i.e. l1 == l2, i.e. tag1 == tag2 --
  // still false, exactly as before this fix.
  let no_spec (m : bnode_subst)
    : Lemma (requires (forall (tbx : triple). memP tbx gb ==>
                         (exists (ta : triple). memP ta ga /\ triple_inst m tbx ta)))
            (ensures False) =
    let tb = { s = S_IRI s; p = p; o = T_Literal l2 } in
    assert (memP tb gb);
    eliminate exists (ta : triple). memP ta ga /\ triple_inst m tb ta
    returns False
    with _pf.
      (assert (ta == { s = S_IRI s; p = p; o = T_Literal l1 });
       assert (term_inst m (T_Literal l2) (T_Literal l1));
       assert (T_Literal l1 == T_Literal l2);
       assert (l1 == l2))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_spec)

// POSITIVE REGRESSION (measuring-inference discipline: a green
// negative test alone proves nothing was exercised -- confirm the
// fixed literal-match branch actually FIRES and accepts on a genuine
// match). Same-case tags, same literal in both graphs: `literal_term_eq`
// must still say yes, and the search must still find it.
let simple_entails_se1_positive_regression (s : wf_iri) (p : wf_iri) (tag : string)
  : Lemma (ensures (
             let l = se1_lit "x" tag in
             let ga = [ { s = S_IRI s; p = p; o = T_Literal l } ] in
             let gb = [ { s = S_IRI s; p = p; o = T_Literal l } ] in
             simple_entails ga gb == true /\ simple_entailment_spec ga gb)) =
  let l = se1_lit "x" tag in
  let ga = [ { s = S_IRI s; p = p; o = T_Literal l } ] in
  let gb = [ { s = S_IRI s; p = p; o = T_Literal l } ] in
  lemma_simple_entails_unfold ga gb;
  assert (literal_term_eq l l == true);
  assert (simple_entails ga gb == true);
  let m : bnode_subst = fun lbl -> T_BNode lbl in
  let aux (tb : triple)
    : Lemma (requires memP tb gb)
            (ensures (exists (ta : triple). memP ta ga /\ triple_inst m tb ta)) =
    assert (tb == { s = S_IRI s; p = p; o = T_Literal l });
    assert (memP tb ga)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

// ===================================================================
// 7. The spec's own shape: "a subgraph of A is an instance of B".
//
// `simple_entailment_spec` collapses the intermediate instance graph.
// This section checks that the collapse is faithful in the direction
// that matters for the transcription argument: the spec-text form
// implies the collapsed form (so the collapsed form is not STRONGER
// than the text). The converse needs a choice-based construction of
// the image graph; see the design doc, "what is not proved".
// ===================================================================
let lemma_spec_is_instance_subgraph (a b : list triple)
  : Lemma (requires instance_subgraph_form a b)
          (ensures  simple_entailment_spec a b) =
  eliminate exists (m : bnode_subst) (g_inst : list triple).
      is_subgraph g_inst a /\ is_instance_of m g_inst b
  returns (simple_entailment_spec a b)
  with _pf.
    assert (forall (tb : triple). memP tb b ==>
              (exists (ta : triple). memP ta a /\ triple_inst m tb ta))

// ===================================================================
// 8. GROUND-FRAGMENT SOUNDNESS (issue #324 follow-up). UNCONDITIONAL:
// no `graph_exact` hypothesis on EITHER graph, only `graph_ground b`.
//
// Why this is available now and was not before: a bnode-free pattern
// triple never drives `match_term`/`match_subj`'s T_BNode branches --
// the ONLY place the shipping engine's literal comparison still routes
// through `rdf_term_eq` (hence `literal_eq`) rather than the caller's
// `leq` (see section 6's residual note). So for `graph_ground b`,
// soundness needs nothing from `graph_exact` at all -- only that `leq`
// itself decides literal identity (`leq_always_identity`), which
// `simple_leq` now does. This is exactly the shape of the SE-1 witness
// (ground graphs, no blank nodes) generalized to a full soundness
// corollary: for THIS fragment, `graph_exact`'s remaining role (the
// bnode-rebind residual) provably does not apply.
// ===================================================================

let lemma_match_subj_ground_sound (b : binding) (ps gs : subject)
  : Lemma (requires subj_ground ps == true /\ Some? (match_subj b ps gs))
          (ensures Some?.v (match_subj b ps gs) == b /\ ps == gs) =
  match ps with
  | S_IRI _   -> ()
  | S_BNode _ -> ()

let rec lemma_match_term_ground_sound (leq : bool -> literal -> literal -> bool)
                                      (bnd : rdf_term -> bool)
                                      (inside : bool) (b : binding)
                                      (pat g : rdf_term)
  : Lemma (requires leq_always_identity leq /\ term_ground pat == true /\
                    Some? (match_term leq bnd inside b pat g))
          (ensures Some?.v (match_term leq bnd inside b pat g) == b /\ pat == g)
          (decreases pat) =
  match pat with
  | T_IRI _   -> ()
  | T_BNode _ -> ()
  | T_Literal l ->
    (match g with
     | T_Literal m -> ()
     | _ -> ())
  | T_TripleTerm ps pp po ->
    (match g with
     | T_TripleTerm gs gp go ->
       if pp = gp then
         (match match_subj b ps gs with
          | Some b1 ->
            lemma_match_subj_ground_sound b ps gs;
            lemma_match_term_ground_sound leq bnd true b1 po go
          | None -> ())
       else ()
     | _ -> ())

let lemma_match_triple_ground_sound (leq : bool -> literal -> literal -> bool)
                                    (bnd : rdf_term -> bool)
                                    (b : binding) (tb ta : triple)
  : Lemma (requires leq_always_identity leq /\ triple_ground tb == true /\
                    Some? (match_triple leq bnd b tb ta))
          (ensures Some?.v (match_triple leq bnd b tb ta) == b /\ tb == ta) =
  assert (tb.p == ta.p);
  lemma_match_subj_ground_sound b tb.s ta.s;
  (match match_subj b tb.s ta.s with
   | Some b1 -> lemma_match_term_ground_sound leq bnd false b1 tb.o ta.o
   | None    -> ());
  assert (tb.s == ta.s);
  assert (tb.o == ta.o)

let rec lemma_try_match_ground_sound (leq : bool -> literal -> literal -> bool)
                                     (bnd : rdf_term -> bool)
                                     (bs : list triple) (b : binding) (a : list triple)
  : Lemma (requires leq_always_identity leq /\ graph_ground bs /\
                    try_match leq bnd bs b a == true)
          (ensures is_subgraph bs a)
          (decreases %[length bs; 1 + length a]) =
  match bs with
  | []        -> ()
  | tb :: rest -> lemma_try_alts_ground_sound leq bnd bs tb rest b a a

and lemma_try_alts_ground_sound (leq : bool -> literal -> literal -> bool)
                                (bnd : rdf_term -> bool)
                                (bs : list triple) (tb : triple)
                                (rest : list triple { length rest < length bs })
                                (b : binding) (a : list triple) (cand : list triple)
  : Lemma (requires leq_always_identity leq /\ triple_ground tb == true /\
                    graph_ground rest /\ is_subgraph cand a /\
                    try_alts leq bnd bs tb rest b a cand == true)
          (ensures is_subgraph (tb :: rest) a)
          (decreases %[length bs; length cand]) =
  match cand with
  | [] -> ()
  | ta0 :: more ->
    assert (memP ta0 cand);
    assert (memP ta0 a);
    (match match_triple leq bnd b tb ta0 with
     | Some b1 ->
       if try_match leq bnd rest b1 a then begin
         lemma_match_triple_ground_sound leq bnd b tb ta0;
         assert (tb == ta0);
         assert (memP tb a);
         lemma_try_match_ground_sound leq bnd rest b1 a;
         assert (is_subgraph rest a)
       end
       else lemma_try_alts_ground_sound leq bnd bs tb rest b a more
     | None -> lemma_try_alts_ground_sound leq bnd bs tb rest b a more)

// Ground terms match themselves under any instance mapping M -- there
// is nothing for M to substitute, so `term_inst`/`subj_inst`/
// `triple_inst` hold reflexively for any total M.
let lemma_subj_inst_ground_refl (m : bnode_subst) (s : subject)
  : Lemma (requires subj_ground s == true) (ensures subj_inst m s s) =
  match s with
  | S_IRI _   -> ()
  | S_BNode _ -> ()

let rec lemma_term_inst_ground_refl (m : bnode_subst) (t : rdf_term)
  : Lemma (requires term_ground t == true) (ensures term_inst m t t) (decreases t) =
  match t with
  | T_IRI _     -> ()
  | T_BNode _   -> ()
  | T_Literal _ -> ()
  | T_TripleTerm ps pp po ->
    lemma_subj_inst_ground_refl m ps;
    lemma_term_inst_ground_refl m po;
    assert (subj_inst m ps ps);
    assert (term_inst m po po);
    assert (t == T_TripleTerm ps pp po)

let lemma_triple_inst_ground_refl (m : bnode_subst) (t : triple)
  : Lemma (requires triple_ground t == true) (ensures triple_inst m t t) =
  lemma_subj_inst_ground_refl m t.s;
  lemma_term_inst_ground_refl m t.o

// ===================================================================
// THEOREM (ground-fragment soundness, UNCONDITIONAL). If the shipping
// search returns true and B has no blank node anywhere, then A simply
// entails B in the declarative sense -- with NO side condition on
// literal content in either graph. This is strictly stronger, on this
// fragment, than `simple_entails_sound` above, and it is exactly the
// fragment the SE-1 witness lived in.
// ===================================================================
let simple_entails_sound_ground (a b : list triple)
  : Lemma (requires simple_entails a b == true /\ graph_ground b)
          (ensures  simple_entailment_spec a b) =
  lemma_simple_leq_always_identity ();
  lemma_simple_entails_unfold a b;
  lemma_try_match_ground_sound simple_leq simple_bnd b [] a;
  let m : bnode_subst = fun l -> T_BNode l in
  let aux (tb : triple)
    : Lemma (requires memP tb b)
            (ensures (exists (ta : triple). memP ta a /\ triple_inst m tb ta)) =
    assert (memP tb a);
    assert (triple_ground tb == true);
    lemma_triple_inst_ground_refl m tb;
    assert (triple_inst m tb tb)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
