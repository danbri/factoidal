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
// `fun _ l m -> literal_eq l m` and `fun _ -> true`.
// -------------------------------------------------------------------

// `unfold` (not a plain `let`): the theorems below must be about the
// EXACT text `simple_entails` runs, so these two names have to melt
// away at typechecking rather than stand as opaque symbols the SMT
// encoding cannot relate to the shipping lambdas (design-doc finding
// F3 in the OWL pilot, same trap).
unfold let simple_leq : bool -> literal -> literal -> bool =
  fun _ l m -> literal_eq l m

unfold let simple_bnd : rdf_term -> bool = fun _ -> true

let lemma_simple_leq_reflexive (_ : unit) : Lemma (leq_reflexive simple_leq) =
  FStar.Classical.forall_intro lemma_literal_eq_refl

let lemma_simple_bnd_total (_ : unit) : Lemma (bnd_total simple_bnd) = ()

let lemma_simple_leq_exact_identity (_ : unit) : Lemma (leq_exact_identity simple_leq) =
  let aux (l1 l2 : literal)
    : Lemma (lit_exact l1 ==> lit_exact l2 ==> literal_eq l1 l2 == true ==> l1 == l2) =
    FStar.Classical.move_requires_3
      (fun (x : literal) (y : literal) (_ : unit) -> lemma_literal_eq_exact x y)
      l1 l2 ()
  in
  FStar.Classical.forall_intro_2 aux

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
// 6. FINDING SE-1: soundness is NOT unconditional.
//
// `literal_eq` compares language tags case-insensitively
// (`lang_tag_eq t1 t2 = lowercase t1 = lowercase t2`). RDF 1.1
// Concepts section 3.3 makes literal term equality character-by-
// character, so `"x"@en` and `"x"@EN` are DIFFERENT literal terms with
// the same value. Simple interpretations (RDF 1.1 Semantics section 5)
// place no constraint tying the two denotations together -- value
// equality of language-tagged strings is an RDF-interpretation
// condition, not a simple one. So a graph asserting `"x"@en` does NOT
// simply entail the same graph with `"x"@EN`; the shipping engine says
// it does.
//
// The lemma below proves exactly that, for any two language tags that
// differ but lowercase alike (e.g. "EN" and "en"). It is stated with
// the tag pair as a hypothesis rather than with literal strings
// because F* does not reduce `FStar.String.lowercase` on string
// constants; the hypothesis is trivially satisfiable and the reader
// can instantiate it mentally at ("EN","en").
//
// The same divergence exists for rdf:XMLLiteral (`literal_eq` routes
// two XMLLiteral-typed literals through `xmlc_canonicalize`): in RDF
// 2004 the XMLLiteral value space is a condition on RDF-
// interpretations (section 3.1), not simple ones, and in RDF 1.1
// rdf:XMLLiteral is not even a normative datatype (Concepts section
// 5.3 is non-normative). Not separately witnessed here; same shape.
//
// PRACTICAL IMPACT: the divergence is in the "accepts more" direction
// only, so no test that expects entailment can fail because of it, and
// the RDF 1.2 entailment suite (which is where `simple_entails` is
// exercised) contains no language-tag-case or XMLLiteral negative
// case. The fix, if wanted, is to give `entails_with` a THIRD
// parameter for the simple-regime literal test (strict term identity)
// and keep `literal_eq` for the D-entailment regime -- the engine is
// already parameterized in exactly that shape.
// ===================================================================

let se1_lit (lex : string) (tag : string) : literal =
  { lexical_form = lex; datatype = rdf_lang_string;
    lang_tag = Some tag; direction = None }

let lemma_se1_lit_wf (lex tag : string) : Lemma (literal_wf (se1_lit lex tag)) = ()

let simple_entails_not_sound_unconditionally
      (s : wf_iri) (p : wf_iri) (tag1 tag2 : string)
  : Lemma (requires FStar.String.lowercase tag1 == FStar.String.lowercase tag2 /\
                    tag1 =!= tag2)
          (ensures (
            let l1 = se1_lit "x" tag1 in
            let l2 = se1_lit "x" tag2 in
            let ga = [ { s = S_IRI s; p = p; o = T_Literal l1 } ] in
            let gb = [ { s = S_IRI s; p = p; o = T_Literal l2 } ] in
            simple_entails ga gb == true /\ ~(simple_entailment_spec ga gb))) =
  let l1 = se1_lit "x" tag1 in
  let l2 = se1_lit "x" tag2 in
  let ga = [ { s = S_IRI s; p = p; o = T_Literal l1 } ] in
  let gb = [ { s = S_IRI s; p = p; o = T_Literal l2 } ] in
  lemma_simple_entails_unfold ga gb;
  assert (literal_eq l2 l1 == true);
  assert (simple_entails ga gb == true);
  // The spec side: gb's only triple is ground, so no substitution can
  // help; `term_inst m (T_Literal l2) (T_Literal l1)` demands
  // T_Literal l1 == T_Literal l2, i.e. l1 == l2, i.e. tag1 == tag2.
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
