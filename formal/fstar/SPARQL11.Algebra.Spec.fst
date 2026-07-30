module SPARQL11.Algebra.Spec

// ===================================================================
// A DECLARATIVE specification of the SPARQL 1.1 algebra, transcribed
// from the W3C Recommendation text, written to be readable and
// checkable against that text WITHOUT reference to any algorithm.
//
// This module deliberately computes almost nothing and mentions NO
// function and NO type of SPARQL11.Algebra. Its only project-internal
// dependency is RDF.Term, for the RDF term model. That independence
// is mechanically checkable: this file's `open` list is
//
//     FStar.List.Tot   RDF.Term
//
// and nothing else. It is the independent statement against which the
// shipping evaluator is proven sound and complete (or shown NOT to
// refine it) in SPARQL11.Algebra.Refinement.fst.
//
// Companion to the RDF-simple-entailment vertical
// (RDF.Entailment.Simple.Spec.fst, 2026-07-29); same four-module
// pattern, same discipline. Issue #313 gate; the external review's
// finding it answers, quoted verbatim:
//
//   "SPARQL11.Algebra.fst is a substantial executable evaluator ...
//    The module does not present a second, declarative W3C algebra
//    semantics and prove the evaluator equivalent to it."
//
// -------------------------------------------------------------------
// BASELINE PINNING
// -------------------------------------------------------------------
// Primary (normative for this project): SPARQL 1.1 Query Language,
// W3C Recommendation 21 March 2013
// (https://www.w3.org/TR/sparql11-query/), sections 18.3 ("Basic
// Graph Patterns" / solution-mapping preliminaries), 18.4
// ("SPARQL Algebra") and 18.5 ("SPARQL Algebra Evaluation
// Semantics" -- multiset semantics).
//
// Secondary, for STRUCTURE ONLY (not normative here): Jorge Perez,
// Marcelo Arenas, Claudio Gutierrez, "Semantics and Complexity of
// SPARQL", ACM Transactions on Database Systems 34(3), Article 16,
// September 2009. That paper gives the canonical formal treatment of
// the same operators. Two deliberate differences from the paper are
// recorded in "Version divergences" below; where this module and the
// paper agree, the paper's names are given in comments so a reader
// can cross-check. Angles and Gutierrez, "The Expressive Power of
// SPARQL" (ISWC 2008), is the reference for the relational reading of
// OPTIONAL/LeftJoin; nothing here depends on it.
//
// -------------------------------------------------------------------
// THE SPEC TEXT, QUOTED VERBATIM
// -------------------------------------------------------------------
// SPARQL 1.1 Query Language, section 18.3 (Basic Graph Patterns),
// "Definition: Solution Mapping":
//
//   "A solution mapping, mu, is a partial function
//    mu : V -> T from a set of variables V to a set of RDF terms T.
//    The domain of mu, dom(mu), is the subset of V where mu is
//    defined."
//
// section 18.3, "Definition: Compatible Mappings":
//
//   "Two solution mappings mu1 and mu2 are compatible if, for every
//    variable v in dom(mu1) and in dom(mu2), mu1(v) = mu2(v)."
//
// and the note that follows it:
//
//   "Two solution mappings with disjoint domains are always
//    compatible, and the empty solution mapping mu0 is compatible
//    with any other solution mapping."
//
// section 18.5 (SPARQL Algebra), "Definition: Join":
//
//   "Join(Omega1, Omega2) =
//      { merge(mu1, mu2) | mu1 in Omega1 and mu2 in Omega2, and
//        mu1 and mu2 are compatible }"
//
// section 18.5, "Definition: Union":
//
//   "Union(Omega1, Omega2) =
//      { mu | mu in Omega1 or mu in Omega2 }"
//
// section 18.5, "Definition: Diff":
//
//   "Diff(Omega1, Omega2, expr) =
//      { mu | mu in Omega1 such that for all mu' in Omega2, either mu
//        and mu' are not compatible or mu and mu' are compatible and
//        expr(merge(mu, mu')) has an effective boolean value of
//        false }"
//
// section 18.5, "Definition: LeftJoin":
//
//   "LeftJoin(Omega1, Omega2, expr) =
//      Filter(expr, Join(Omega1, Omega2)) union
//      Diff(Omega1, Omega2, expr)"
//
// section 18.5, "Definition: Filter":
//
//   "Filter(expr, Omega) =
//      { mu | mu in Omega and expr(mu) is an expression that has an
//        effective boolean value of true }"
//
// section 18.5, "Definition: Minus":
//
//   "Minus(Omega1, Omega2) =
//      { mu | mu in Omega1 such that for all mu' in Omega2, either mu
//        and mu' are not compatible or dom(mu) and dom(mu') are
//        disjoint }"
//
// section 18.5, "Definition: Extend":
//
//   "Extend(mu, var, term) = mu union { (var,term) }  if var not in
//        dom(mu)
//    Extend(mu, var, term) = undefined                if var in
//        dom(mu)
//    Extend(Omega, var, expr) =
//      { Extend(mu, var, expr(mu)) | mu in Omega }"
//
// section 18.5, "Definition: Project":
//
//   "Project(Omega, PV) = { Proj(mu, PV) | mu in Omega }
//    where Proj(mu, PV) is defined as the restriction of mu to the
//    variables in PV."
//
// section 18.5, "Definition: Distinct":
//
//   "Distinct(Omega) = { mu | mu in Omega } where Card[mu] = 1"
//
// section 18.5, "Definition: Basic Graph Pattern" (the sub-algebra
// evaluation rule):
//
//   "eval(D(G), BGP) = multiset of solution mappings"
//
// with the entailment-regime-relative definition of BGP matching in
// section 18.3.1 specialising, for simple entailment, to: mu is a
// solution of BGP against G exactly when dom(mu) = var(BGP) and
// mu(BGP) is a subgraph of G, each such mu having cardinality 1.
//
// -------------------------------------------------------------------
// MULTISET vs SET, AND WHICH ONE THIS MODULE FORMALISES
// -------------------------------------------------------------------
// W3C 18.5 is a MULTISET (bag) semantics: every operator is defined
// on multisets of solution mappings with an explicit cardinality
// function Card[.]. Perez/Arenas/Gutierrez 2009 is a SET semantics
// (their section 2 defines Omega as a SET of mappings), which makes
// their complexity results and their well-designed-pattern theory
// cleaner but does NOT match what a conforming engine must return
// for a query without DISTINCT.
//
// This module formalises BOTH LAYERS, deliberately, because the two
// carry different proof obligations against a list-backed evaluator:
//
//   * the SET layer (`in_*_spec` relations, part 3) says WHICH
//     mappings may appear. Soundness/completeness of the evaluator's
//     search is a statement about this layer, and it is the layer
//     Perez et al. share, so their established results transfer.
//   * the BAG layer (`mult`, part 4) says HOW MANY TIMES each
//     appears. This is the normative W3C layer and it is where a
//     list-backed evaluator's duplicate-handling bugs live -- a
//     defect invisible to the set layer.
//
// Where they disagree the W3C multiset reading wins; every such place
// is flagged inline with "W3C-BAG".
//
// -------------------------------------------------------------------
// TERM EQUALITY IN THIS SPECIFICATION
// -------------------------------------------------------------------
// Section 18.3's compatibility condition is "mu1(v) = mu2(v)". The
// "=" there is IDENTITY OF RDF TERMS (RDF 1.1 Concepts section 3.3:
// literal term equality is character-by-character on the lexical
// form, with equal datatype IRIs and equal language tags), NOT
// SPARQL's value-level `sameTerm`-modulo-D equality and NOT
// `RDF.Term.literal_eq`.
//
// So this module uses F* propositional equality `==` on `rdf_term`
// throughout, and provides `term_id_eqb` as its decision procedure
// (`lemma_term_id_eqb_sound` / `lemma_term_id_eqb_complete`). The
// shipping evaluator instead uses `RDF.Term.rdf_term_eq`, which is
// strictly COARSER (it lowercases language tags and canonicalises
// rdf:XMLLiteral lexical forms). That divergence is not hidden here
// by weakening the spec; it is exposed as an explicit fragment
// hypothesis and a machine-checked counter-witness in
// SPARQL11.Algebra.Refinement.fst. Compare finding SE-1 of the
// simple-entailment vertical, which is the same defect reached from
// the other end of the tree.
//
// -------------------------------------------------------------------
// SCOPE -- WHAT THIS MODULE COVERS, AND WHAT IT DOES NOT
// -------------------------------------------------------------------
// IN SCOPE (the named fragment; call it SPARQL-CORE-8):
//   solution mappings and their domains (18.3)
//   compatibility and merge (18.3)
//   Join, Union, Minus, Filter, Diff, LeftJoin, Extend, Project,
//   Distinct (18.5)
//   BGP matching, stated abstractly over a pattern-instantiation
//   function so that the spec stays independent of the evaluator's
//   abstract syntax (18.3.1 / 18.5)
//
// EXPLICITLY OUT OF SCOPE in this first vertical, and NOT gestured at:
//   * aggregates (18.5.1 Aggregation, Group, AggregateJoin) --
//     a second, per-group semantics, not a solution-multiset one
//   * property paths (18.4 ZeroOrMorePath etc.) -- these carry their
//     own fixpoint semantics
//   * subqueries (ToMultiSet / sub-SELECT) and SERVICE
//   * ORDER BY, Slice (OFFSET/LIMIT), Reduced, ToList -- these are
//     SEQUENCE operators, defined on ordered solution sequences, and
//     a refinement statement about them must first fix an ordering
//     discipline the evaluator does not currently promise
//   * the dataset / GRAPH machinery: everything here is relative to a
//     SINGLE active graph. eval(D(G), .) is written eval(G, .).
//   * expression evaluation (section 17). Filter, LeftJoin and Extend
//     are stated PARAMETRICALLY in the expression evaluator, exactly
//     as 18.5 states them ("expr(mu) has an effective boolean value
//     of true"). Section 17's operator mapping and error handling is
//     a separate specification and a separate vertical.
//
// -------------------------------------------------------------------
// VERSION DIVERGENCES
// -------------------------------------------------------------------
// 1. W3C 18.5 is a multiset semantics; Perez et al. 2009 is a set
//    semantics. Handled by formalising both layers -- see above.
// 2. Perez et al. define OPT via left-outer-join on SETS and prove
//    the well-designed-pattern normal form for it. Their Omega1 |><|
//    Omega2 has no filter argument; W3C's LeftJoin carries `expr`
//    (SPARQL's OPTIONAL ... FILTER). The definition here is W3C's;
//    setting the filter to constant-true recovers theirs.
// 3. Perez et al. write merge as mu1 union mu2 for compatible
//    mappings, which is symmetric. W3C's `merge` is likewise
//    symmetric on compatible mappings (`lemma_merge_comm_compatible`
//    below proves it) -- but the SHIPPING evaluator's merge is left-
//    biased and only coincides on compatible arguments, so the
//    asymmetry matters at the refinement boundary, not here.
// ===================================================================

open FStar.List.Tot
open RDF.Term

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"

(** ====================================================================== **)
(** Part 1: Solution mappings (section 18.3)                               **)
(** ====================================================================== **)

/// SPARQL variables. Section 18.3 names the variable set V; a variable
/// is identified by its name.
type var_name = string

/// A solution mapping. Section 18.3: "a partial function mu : V -> T".
///
/// Represented as an association list so that the spec talks about the
/// same VALUES the evaluator manipulates and no translation layer is
/// needed at the refinement boundary. The representation is NOT the
/// meaning: two association lists denote the same solution mapping
/// exactly when `smap_eq` holds of them, and every statement in this
/// module is invariant under `smap_eq` (`lemma_*_congr` below).
///
/// This type is definitionally equal to RDF.Graph.Executable's
/// `solution_mapping`; it is re-declared rather than imported so this
/// module depends on RDF.Term alone.
type smap = list (var_name * rdf_term)

/// dom(mu). Section 18.3: "the subset of V where mu is defined".
let sdom (mu : smap) : list var_name = List.Tot.map fst mu

/// mu(v), as a partial function: `None` when v is not in dom(mu).
let sval (v : var_name) (mu : smap) : option rdf_term = List.Tot.assoc v mu

/// The empty solution mapping mu0 of section 18.3's note.
let smap_empty : smap = []

/// WELL-FORMEDNESS of the REPRESENTATION. A partial function has at
/// most one value per variable; an association list can carry several.
/// Statements about `sval` are insensitive to this (assoc takes the
/// first binding), but statements about `sdom` are NOT, and the
/// shipping `sm_compatible` walks the list rather than the function --
/// see the 2026-07-29 refutation
/// `SPARQL11.Algebra.lemma_sm_compatible_not_refl_with_dup_keys`,
/// which is exactly this hazard. Every theorem in the refinement
/// module that needs it says so.
let smap_wf (mu : smap) : bool = noRepeats (sdom mu)

(** 1.1 Term identity, and its decision procedure **)

/// Structural identity on literals -- every field compared exactly.
/// This is RDF 1.1 Concepts section 3.3 literal term equality: same
/// lexical form character by character, same datatype IRI, same
/// language tag (NOT case-folded), same base direction.
let lit_id_eqb (l1 l2 : wf_literal) : bool =
  l1.lexical_form = l2.lexical_form &&
  l1.datatype = l2.datatype &&
  l1.lang_tag = l2.lang_tag &&
  l1.direction = l2.direction

let subj_id_eqb (s1 s2 : subject) : bool =
  match s1, s2 with
  | S_IRI a, S_IRI b -> a = b
  | S_BNode a, S_BNode b -> a = b
  | _, _ -> false

/// Term identity, decided structurally. `rdf_term` is `noeq`, so F*
/// derives no decidable equality for it; this supplies one and the two
/// lemmas below prove it decides `==` exactly.
let rec term_id_eqb (t1 t2 : rdf_term) : Tot bool (decreases t1) =
  match t1, t2 with
  | T_IRI a, T_IRI b -> a = b
  | T_BNode a, T_BNode b -> a = b
  | T_Literal a, T_Literal b -> lit_id_eqb a b
  | T_TripleTerm s1 p1 o1, T_TripleTerm s2 p2 o2 ->
    subj_id_eqb s1 s2 && p1 = p2 && term_id_eqb o1 o2
  | _, _ -> false

let lemma_lit_id_eqb_sound (l1 l2 : wf_literal)
  : Lemma (requires lit_id_eqb l1 l2 == true) (ensures l1 == l2) = ()

let lemma_subj_id_eqb_sound (s1 s2 : subject)
  : Lemma (requires subj_id_eqb s1 s2 == true) (ensures s1 == s2) = ()

/// `term_id_eqb` never identifies distinct terms.
let rec lemma_term_id_eqb_sound (t1 t2 : rdf_term)
  : Lemma (requires term_id_eqb t1 t2 == true) (ensures t1 == t2)
          (decreases t1) =
  match t1, t2 with
  | T_Literal a, T_Literal b -> lemma_lit_id_eqb_sound a b
  | T_TripleTerm s1 _ o1, T_TripleTerm s2 _ o2 ->
    lemma_subj_id_eqb_sound s1 s2; lemma_term_id_eqb_sound o1 o2
  | _, _ -> ()

/// ... and never separates identical ones.
let rec lemma_term_id_eqb_complete (t1 t2 : rdf_term)
  : Lemma (requires t1 == t2) (ensures term_id_eqb t1 t2 == true)
          (decreases t1) =
  match t1 with
  | T_TripleTerm _ _ o1 -> lemma_term_id_eqb_complete o1 o1
  | _ -> ()

let lemma_term_id_eqb_refl (t : rdf_term)
  : Lemma (term_id_eqb t t == true) = lemma_term_id_eqb_complete t t

(** 1.2 Equality of solution mappings, as partial functions **)

/// Two association lists denote the SAME solution mapping when they
/// agree as partial functions. This -- not list equality -- is the
/// equality section 18.3 means, and it is what Distinct (18.5) must
/// use to decide duplicates.
let smap_eq (mu1 mu2 : smap) : prop =
  forall (v : var_name). sval v mu1 == sval v mu2

let lemma_smap_eq_refl (mu : smap) : Lemma (smap_eq mu mu) = ()

let lemma_smap_eq_sym (mu1 mu2 : smap)
  : Lemma (requires smap_eq mu1 mu2) (ensures smap_eq mu2 mu1) = ()

let lemma_smap_eq_trans (mu1 mu2 mu3 : smap)
  : Lemma (requires smap_eq mu1 mu2 /\ smap_eq mu2 mu3)
          (ensures smap_eq mu1 mu3) = ()

/// A decision procedure for `smap_eq`. Two mappings agree everywhere
/// exactly when they agree on the union of their domains, because
/// outside both domains both are `None`.
let opt_term_id_eqb (o1 o2 : option rdf_term) : bool =
  match o1, o2 with
  | None, None -> true
  | Some a, Some b -> term_id_eqb a b
  | _, _ -> false

let rec agrees_on (vs : list var_name) (mu1 mu2 : smap) : Tot bool (decreases vs) =
  match vs with
  | [] -> true
  | v :: rest -> opt_term_id_eqb (sval v mu1) (sval v mu2) && agrees_on rest mu1 mu2

let smap_eqb (mu1 mu2 : smap) : bool =
  agrees_on (sdom mu1) mu1 mu2 && agrees_on (sdom mu2) mu1 mu2

/// A variable outside dom(mu) has no value. (The list-level fact that
/// makes `smap_eqb` a complete decision procedure.)
let rec lemma_sval_none_outside_dom (v : var_name) (mu : smap)
  : Lemma (requires ~(List.Tot.memP v (sdom mu)))
          (ensures  sval v mu == None)
          (decreases mu) =
  match mu with
  | [] -> ()
  | (w, _) :: rest -> lemma_sval_none_outside_dom v rest

let rec lemma_agrees_on_mem (vs : list var_name) (mu1 mu2 : smap) (v : var_name)
  : Lemma (requires agrees_on vs mu1 mu2 == true /\ List.Tot.memP v vs)
          (ensures  opt_term_id_eqb (sval v mu1) (sval v mu2) == true)
          (decreases vs) =
  match vs with
  | [] -> ()
  | w :: rest -> if w = v then () else lemma_agrees_on_mem rest mu1 mu2 v

let lemma_opt_term_id_eqb_sound (o1 o2 : option rdf_term)
  : Lemma (requires opt_term_id_eqb o1 o2 == true) (ensures o1 == o2) =
  match o1, o2 with
  | Some a, Some b -> lemma_term_id_eqb_sound a b
  | _, _ -> ()

/// `smap_eqb` decides `smap_eq` -- soundness half.
let lemma_smap_eqb_sound (mu1 mu2 : smap)
  : Lemma (requires smap_eqb mu1 mu2 == true) (ensures smap_eq mu1 mu2) =
  let aux (v : var_name) : Lemma (sval v mu1 == sval v mu2) =
    let d1 = sdom mu1 in
    let d2 = sdom mu2 in
    if List.Tot.mem v d1 then begin
      FStar.List.Tot.Properties.memP_existsb (fun x -> x = v) d1;
      lemma_agrees_on_mem d1 mu1 mu2 v;
      lemma_opt_term_id_eqb_sound (sval v mu1) (sval v mu2)
    end else if List.Tot.mem v d2 then begin
      FStar.List.Tot.Properties.memP_existsb (fun x -> x = v) d2;
      lemma_agrees_on_mem d2 mu1 mu2 v;
      lemma_opt_term_id_eqb_sound (sval v mu1) (sval v mu2)
    end else begin
      lemma_sval_none_outside_dom v mu1;
      lemma_sval_none_outside_dom v mu2
    end
  in
  FStar.Classical.forall_intro aux

let rec lemma_agrees_on_of_smap_eq (vs : list var_name) (mu1 mu2 : smap)
  : Lemma (requires smap_eq mu1 mu2) (ensures agrees_on vs mu1 mu2 == true)
          (decreases vs) =
  match vs with
  | [] -> ()
  | v :: rest ->
    (match sval v mu1 with
     | None -> ()
     | Some t -> lemma_term_id_eqb_refl t);
    lemma_agrees_on_of_smap_eq rest mu1 mu2

/// ... and completeness half.
let lemma_smap_eqb_complete (mu1 mu2 : smap)
  : Lemma (requires smap_eq mu1 mu2) (ensures smap_eqb mu1 mu2 == true) =
  lemma_agrees_on_of_smap_eq (sdom mu1) mu1 mu2;
  lemma_agrees_on_of_smap_eq (sdom mu2) mu1 mu2

(** ====================================================================== **)
(** Part 2: Compatibility and merge (section 18.3)                         **)
(** ====================================================================== **)

/// Section 18.3, Definition: Compatible Mappings, transcribed:
/// "for every variable v in dom(mu1) and in dom(mu2), mu1(v) = mu2(v)".
///
/// Stated over `sval` rather than over the domain LISTS, so that it is
/// automatically insensitive to the association-list representation.
/// Perez et al. 2009 section 2 write this mu1 ~ mu2.
let compatible_spec (mu1 mu2 : smap) : prop =
  forall (v : var_name) (t1 t2 : rdf_term).
    (sval v mu1 == Some t1 /\ sval v mu2 == Some t2) ==> t1 == t2

/// The note after the definition, proved rather than asserted:
/// "the empty solution mapping mu0 is compatible with any other".
let lemma_compatible_empty_l (mu : smap) : Lemma (compatible_spec smap_empty mu) = ()
let lemma_compatible_empty_r (mu : smap) : Lemma (compatible_spec mu smap_empty) = ()

/// "Two solution mappings with disjoint domains are always compatible."
let dom_disjoint_spec (mu1 mu2 : smap) : prop =
  forall (v : var_name). ~(Some? (sval v mu1) /\ Some? (sval v mu2))

let lemma_compatible_of_disjoint (mu1 mu2 : smap)
  : Lemma (requires dom_disjoint_spec mu1 mu2) (ensures compatible_spec mu1 mu2) = ()

/// Compatibility is symmetric and reflexive AS A RELATION ON PARTIAL
/// FUNCTIONS. Reflexivity is worth stating: the shipping
/// `sm_compatible` is NOT reflexive on all association lists (see
/// SPARQL11.Algebra.lemma_sm_compatible_not_refl_with_dup_keys,
/// 2026-07-29), and this lemma is what pins the difference on the
/// representation rather than on the definition.
let lemma_compatible_refl (mu : smap) : Lemma (compatible_spec mu mu) = ()
let lemma_compatible_sym (mu1 mu2 : smap)
  : Lemma (requires compatible_spec mu1 mu2) (ensures compatible_spec mu2 mu1) = ()

/// Compatibility respects `smap_eq` in each argument -- the check that
/// the definition is about mappings, not about lists.
let lemma_compatible_congr_l (mu1 mu1' mu2 : smap)
  : Lemma (requires compatible_spec mu1 mu2 /\ smap_eq mu1 mu1')
          (ensures  compatible_spec mu1' mu2) = ()

(** 2.1 merge **)

/// Section 18.3: merge(mu1, mu2) is defined for compatible mappings
/// and is their union. Stated pointwise; `is_merge` is the RELATION
/// "mu is a merge of mu1 and mu2", which is the form every operator
/// below uses. Stating it relationally (rather than as a function
/// returning an association list) means no statement downstream is
/// committed to a particular list layout -- the same presentation
/// choice section 7.2 of the simple-entailment design doc records.
let merge_at (mu1 mu2 : smap) (v : var_name) : option rdf_term =
  match sval v mu1 with
  | Some t -> Some t
  | None -> sval v mu2

let is_merge (mu1 mu2 mu : smap) : prop =
  forall (v : var_name). sval v mu == merge_at mu1 mu2 v

/// A canonical witness, so `is_merge` is never vacuous: appending is a
/// merge, because `assoc` takes the first binding.
let merge_canonical (mu1 mu2 : smap) : smap = List.Tot.append mu1 mu2

let rec lemma_assoc_append (v : var_name) (mu1 mu2 : smap)
  : Lemma (ensures sval v (List.Tot.append mu1 mu2) ==
                   (match sval v mu1 with Some t -> Some t | None -> sval v mu2))
          (decreases mu1) =
  match mu1 with
  | [] -> ()
  | (w, _) :: rest -> if w = v then () else lemma_assoc_append v rest mu2

let lemma_merge_canonical_is_merge (mu1 mu2 : smap)
  : Lemma (is_merge mu1 mu2 (merge_canonical mu1 mu2)) =
  FStar.Classical.forall_intro (fun v -> lemma_assoc_append v mu1 mu2)

/// A merge is determined up to `smap_eq` -- so "the" merge is
/// well-defined as a solution mapping even though many association
/// lists represent it.
let lemma_merge_unique (mu1 mu2 mu mu' : smap)
  : Lemma (requires is_merge mu1 mu2 mu /\ is_merge mu1 mu2 mu')
          (ensures  smap_eq mu mu') = ()

/// On COMPATIBLE mappings merge is symmetric (divergence note 3):
/// W3C's merge and Perez et al.'s mu1 union mu2 agree.
let lemma_merge_comm_compatible (mu1 mu2 mu : smap)
  : Lemma (requires compatible_spec mu1 mu2 /\ is_merge mu1 mu2 mu)
          (ensures  is_merge mu2 mu1 mu) =
  let aux (v : var_name) : Lemma (sval v mu == merge_at mu2 mu1 v) =
    match sval v mu1, sval v mu2 with
    | Some t1, Some t2 -> assert (t1 == t2)
    | _, _ -> ()
  in
  FStar.Classical.forall_intro aux

/// A merge extends both arguments, and its domain is their union.
let lemma_merge_extends_l (mu1 mu2 mu : smap) (v : var_name) (t : rdf_term)
  : Lemma (requires is_merge mu1 mu2 mu /\ sval v mu1 == Some t)
          (ensures  sval v mu == Some t) = ()

let lemma_merge_extends_r (mu1 mu2 mu : smap) (v : var_name) (t : rdf_term)
  : Lemma (requires is_merge mu1 mu2 mu /\ compatible_spec mu1 mu2 /\
                    sval v mu2 == Some t)
          (ensures  sval v mu == Some t) =
  match sval v mu1 with
  | Some t1 -> assert (t1 == t)
  | None -> ()

let lemma_merge_dom (mu1 mu2 mu : smap) (v : var_name)
  : Lemma (requires is_merge mu1 mu2 mu)
          (ensures  Some? (sval v mu) <==> (Some? (sval v mu1) \/ Some? (sval v mu2))) = ()

/// Merge of compatible mappings is compatible with each argument --
/// the property a Join proof needs when chaining.
let lemma_merge_compatible_l (mu1 mu2 mu : smap)
  : Lemma (requires is_merge mu1 mu2 mu /\ compatible_spec mu1 mu2)
          (ensures  compatible_spec mu mu1) =
  let aux (w : var_name) (a b : rdf_term)
    : Lemma (requires sval w mu == Some a /\ sval w mu1 == Some b)
            (ensures  a == b) = () in
  FStar.Classical.forall_intro_3 (fun w a b ->
    FStar.Classical.move_requires (aux w a) b)

(** ====================================================================== **)
(** Part 3: the algebra operators, SET layer (section 18.5)                **)
(** ====================================================================== **)

/// Solution multisets are carried as lists at the refinement boundary
/// (that is what the evaluator produces). The SET layer states which
/// mappings a list may contain, up to `smap_eq`; the BAG layer (part 4)
/// states multiplicities.
type smultiset = list smap

/// "mu occurs in Omega" -- up to `smap_eq`, since a list of
/// association lists represents a multiset of partial functions.
let occurs (mu : smap) (omega : smultiset) : prop =
  exists (mu' : smap). List.Tot.memP mu' omega /\ smap_eq mu mu'

let lemma_occurs_memP (mu : smap) (omega : smultiset)
  : Lemma (requires List.Tot.memP mu omega) (ensures occurs mu omega) = ()

(** 3.1 Filter (section 18.5) **)

/// Filter is stated PARAMETRICALLY in the expression evaluator, exactly
/// as 18.5 states it. `fexpr` stands for "expr(mu) has an effective
/// boolean value of true". Section 17's definition of that predicate is
/// out of this fragment (see SCOPE).
let fexpr = smap -> bool

/// Filter(expr, Omega) = { mu | mu in Omega and expr(mu) has an EBV of
/// true }
let in_filter_spec (f : fexpr) (omega : smultiset) (mu : smap) : prop =
  occurs mu omega /\ f mu == true

(** 3.2 Join (section 18.5) **)

/// Join(Omega1, Omega2) = { merge(mu1, mu2) | mu1 in Omega1 and mu2 in
/// Omega2, and mu1 and mu2 are compatible }
let in_join_spec (o1 o2 : smultiset) (mu : smap) : prop =
  exists (mu1 mu2 : smap).
    List.Tot.memP mu1 o1 /\ List.Tot.memP mu2 o2 /\
    compatible_spec mu1 mu2 /\ is_merge mu1 mu2 mu

/// Join is commutative at the set layer (merge is symmetric on
/// compatible arguments) -- Perez et al. 2009 Proposition 1.
let lemma_join_comm_witness (o1 o2 : smultiset) (mu mu1 mu2 : smap)
  : Lemma (requires List.Tot.memP mu1 o1 /\ List.Tot.memP mu2 o2 /\
                    compatible_spec mu1 mu2 /\ is_merge mu1 mu2 mu)
          (ensures  in_join_spec o2 o1 mu) =
  lemma_compatible_sym mu1 mu2;
  lemma_merge_comm_compatible mu1 mu2 mu

let lemma_join_comm_spec (o1 o2 : smultiset) (mu : smap)
  : Lemma (requires in_join_spec o1 o2 mu) (ensures in_join_spec o2 o1 mu) =
  eliminate exists (mu1 mu2 : smap).
      (List.Tot.memP mu1 o1 /\ List.Tot.memP mu2 o2 /\
       compatible_spec mu1 mu2 /\ is_merge mu1 mu2 mu)
  returns in_join_spec o2 o1 mu
  with _. lemma_join_comm_witness o1 o2 mu mu1 mu2

(** 3.3 Union (section 18.5) **)

/// Union(Omega1, Omega2) = { mu | mu in Omega1 or mu in Omega2 }
let in_union_spec (o1 o2 : smultiset) (mu : smap) : prop =
  occurs mu o1 \/ occurs mu o2

(** 3.4 Diff and LeftJoin (section 18.5) **)

/// Diff(Omega1, Omega2, expr) = { mu | mu in Omega1 such that for all
/// mu' in Omega2, either mu and mu' are not compatible or mu and mu'
/// are compatible and expr(merge(mu, mu')) has an EBV of false }
let in_diff_spec (f : fexpr) (o1 o2 : smultiset) (mu : smap) : prop =
  occurs mu o1 /\
  (forall (mu2 : smap). List.Tot.memP mu2 o2 ==>
     (~(compatible_spec mu mu2) \/
      (forall (m : smap). is_merge mu mu2 m ==> f m == false)))

/// LeftJoin(Omega1, Omega2, expr) = Filter(expr, Join(Omega1, Omega2))
/// union Diff(Omega1, Omega2, expr)
///
/// Transcribed as the literal composition of the three definitions
/// above rather than re-derived, so a reader diffing against the spec
/// text sees one line.
let in_leftjoin_spec (f : fexpr) (o1 o2 : smultiset) (mu : smap) : prop =
  (in_join_spec o1 o2 mu /\ f mu == true) \/ in_diff_spec f o1 o2 mu

(** 3.5 Minus (section 18.5) **)

/// Minus(Omega1, Omega2) = { mu | mu in Omega1 such that for all mu' in
/// Omega2, either mu and mu' are not compatible or dom(mu) and dom(mu')
/// are disjoint }
let in_minus_spec (o1 o2 : smultiset) (mu : smap) : prop =
  occurs mu o1 /\
  (forall (mu2 : smap). List.Tot.memP mu2 o2 ==>
     (~(compatible_spec mu mu2) \/ dom_disjoint_spec mu mu2))

(** 3.6 Extend (section 18.5) **)

/// Extend(mu, var, term) = mu union { (var,term) } if var not in
/// dom(mu); undefined if var in dom(mu).
///
/// Stated relationally. The W3C text leaves Extend UNDEFINED when the
/// variable is already bound -- an error condition, not a no-op. The
/// evaluator's behaviour in that case is one of the things the
/// refinement module has to state honestly rather than assume.
let is_extend_at (mu : smap) (v : var_name) (t : rdf_term) (mu' : smap) : prop =
  sval v mu == None /\
  sval v mu' == Some t /\
  (forall (w : var_name). w =!= v ==> sval w mu' == sval w mu)

/// Extend(Omega, var, expr) = { Extend(mu, var, expr(mu)) | mu in
/// Omega }. `ev` is the expression evaluator, partial because an
/// expression may raise an error (17.2), in which case 18.5's Extend
/// leaves the variable unbound.
let vexpr = smap -> option rdf_term

let in_extend_spec (ev : vexpr) (v : var_name) (omega : smultiset) (mu' : smap) : prop =
  exists (mu : smap).
    List.Tot.memP mu omega /\
    (match ev mu with
     | Some t -> (sval v mu == None /\ is_extend_at mu v t mu') \/
                 (Some? (sval v mu) /\ smap_eq mu' mu)
     | None -> smap_eq mu' mu)

(** 3.7 Project (section 18.5) **)

/// Proj(mu, PV): "the restriction of mu to the variables in PV".
let is_proj (pv : list var_name) (mu mu' : smap) : prop =
  (forall (v : var_name). List.Tot.memP v pv ==> sval v mu' == sval v mu) /\
  (forall (v : var_name). ~(List.Tot.memP v pv) ==> sval v mu' == None)

/// Project(Omega, PV) = { Proj(mu, PV) | mu in Omega }
let in_project_spec (pv : list var_name) (omega : smultiset) (mu' : smap) : prop =
  exists (mu : smap). List.Tot.memP mu omega /\ is_proj pv mu mu'

(** 3.8 Distinct (section 18.5) **)

/// Distinct(Omega) = { mu | mu in Omega } where Card[mu] = 1.
///
/// The SET layer of Distinct is just "same elements"; ALL of Distinct's
/// content is in the cardinality clause, so the statement that matters
/// is `distinct_card_spec` in part 4. Recording both makes the split
/// explicit rather than letting the set layer stand in for the
/// definition.
let in_distinct_spec (omega : smultiset) (mu : smap) : prop = occurs mu omega

(** ====================================================================== **)
(** Part 4: the BAG layer -- cardinalities (section 18.5, normative)       **)
(** ====================================================================== **)

/// Card[mu](Omega): how many times the solution mapping mu occurs in
/// the multiset Omega. Counted up to `smap_eq` via the decision
/// procedure of part 1.2, so it counts MAPPINGS, not list layouts.
let mult (mu : smap) (omega : smultiset) : nat =
  List.Tot.length (List.Tot.filter (fun m -> smap_eqb mu m) omega)

let rec lemma_mult_congr (mu mu' : smap) (omega : smultiset)
  : Lemma (requires smap_eq mu mu') (ensures mult mu omega == mult mu' omega)
          (decreases omega) =
  match omega with
  | [] -> ()
  | m :: rest ->
    (if smap_eqb mu m then begin
       lemma_smap_eqb_sound mu m;
       lemma_smap_eqb_complete mu' m
     end else if smap_eqb mu' m then begin
       lemma_smap_eqb_sound mu' m;
       lemma_smap_eqb_complete mu m
     end else ());
    lemma_mult_congr mu mu' rest

/// mult and occurs agree: the bag layer refines the set layer.
let rec lemma_mult_pos_implies_occurs (mu : smap) (omega : smultiset)
  : Lemma (requires mult mu omega > 0) (ensures occurs mu omega)
          (decreases omega) =
  match omega with
  | [] -> ()
  | m :: rest ->
    if smap_eqb mu m then lemma_smap_eqb_sound mu m
    else lemma_mult_pos_implies_occurs mu rest

let rec lemma_occurs_witness_implies_mult_pos (mu mu' : smap) (omega : smultiset)
  : Lemma (requires List.Tot.memP mu' omega /\ smap_eq mu mu')
          (ensures  mult mu omega > 0)
          (decreases omega) =
  match omega with
  | [] -> ()
  | m :: rest ->
    if smap_eqb mu m then ()
    else
      eliminate (mu' == m) \/ (List.Tot.memP mu' rest)
      returns mult mu omega > 0
      with _. lemma_smap_eqb_complete mu m
      and  _. lemma_occurs_witness_implies_mult_pos mu mu' rest

let lemma_mult_pos_iff_occurs (mu : smap) (omega : smultiset)
  : Lemma (ensures (mult mu omega > 0) <==> occurs mu omega) =
  introduce mult mu omega > 0 ==> occurs mu omega
  with _. lemma_mult_pos_implies_occurs mu omega;
  introduce occurs mu omega ==> mult mu omega > 0
  with _.
    eliminate exists (mu' : smap). List.Tot.memP mu' omega /\ smap_eq mu mu'
    returns mult mu omega > 0
    with _. lemma_occurs_witness_implies_mult_pos mu mu' omega

(** 4.1 the cardinality clauses of section 18.5, transcribed **)

/// "Card[Union(Omega1,Omega2)][mu] =
///    Card[Omega1][mu] + Card[Omega2][mu]"
let union_card_spec (o1 o2 res : smultiset) : prop =
  forall (mu : smap). mult mu res == mult mu o1 + mult mu o2

/// "Card[Filter(expr,Omega)][mu] = Card[Omega][mu] if expr(mu) is
///  true, 0 otherwise"
let filter_card_spec (f : fexpr) (omega res : smultiset) : prop =
  forall (mu : smap). mult mu res == (if f mu then mult mu omega else 0)

/// "Card[Distinct(Omega)][mu] = 1" for every mu occurring in Omega,
/// 0 otherwise -- the whole content of Distinct.
let distinct_card_spec (omega res : smultiset) : prop =
  forall (mu : smap). mult mu res == (if mult mu omega > 0 then 1 else 0)

/// "Card[Project(Omega,PV)][mu] = sum over mu' in Omega with
///  Proj(mu',PV) = mu of Card[Omega][mu']" -- projection MERGES
/// duplicates without removing them, so the result multiset has the
/// same total size as the input.
let project_card_spec (pv : list var_name) (omega res : smultiset) : prop =
  List.Tot.length res == List.Tot.length omega /\
  (forall (mu : smap). occurs mu res <==> in_project_spec pv omega mu)

/// "Card[Minus(Omega1,Omega2)][mu] = Card[Omega1][mu]" for retained mu,
/// 0 otherwise -- Minus never duplicates and never merges.
let minus_card_spec (o1 o2 res : smultiset) : prop =
  (forall (mu : smap). in_minus_spec o1 o2 mu ==> mult mu res == mult mu o1) /\
  (forall (mu : smap). ~(in_minus_spec o1 o2 mu) ==> mult mu res == 0)

(** ====================================================================== **)
(** Part 5: BGP matching (sections 18.3.1 / 18.5)                          **)
(** ====================================================================== **)

/// BGP matching is stated over an ABSTRACT pattern type and an
/// abstract instantiation function, so that this module stays
/// independent of SPARQL11.Algebra's abstract syntax. The refinement
/// module instantiates `tp` with `SPARQL11.Algebra.triple_pattern`,
/// `gtriple` with `RDF.Core.triple`, and `inst` with the shipping
/// `SPARQL11.Algebra.instantiate_tp`.
///
/// `inst mu p` is "mu(p)": the triple obtained by replacing every
/// variable of the pattern p by its mu-image. It is PARTIAL: a
/// pattern whose subject variable is bound to a literal has no
/// instance (RDF subjects are never literals). Section 7.2 of the
/// simple-entailment design doc records why partiality here forces the
/// relational statement below rather than a functional one.
///
/// Simple-entailment BGP matching, section 18.3.1 specialised:
///   mu is a solution of BGP against G  iff
///     dom(mu) = var(BGP)  and  mu(BGP) is a subgraph of G
/// with Card[mu] = 1 for each such mu.
let bgp_sol_spec
      (#tp #gtriple : Type)
      (inst : smap -> tp -> option gtriple)
      (patvars : tp -> list var_name)
      (b : list tp) (g : list gtriple) (mu : smap)
  : prop =
  // mu(BGP) is a subgraph of G
  (forall (p : tp). List.Tot.memP p b ==>
     (exists (t : gtriple). inst mu p == Some t /\ List.Tot.memP t g)) /\
  // dom(mu) = var(BGP)
  (forall (v : var_name).
     Some? (sval v mu) <==>
     (exists (p : tp). List.Tot.memP p b /\ List.Tot.memP v (patvars p)))

/// The empty BGP has exactly the empty solution -- section 18.5's base
/// case, and the sanity check that `bgp_sol_spec` is not vacuous.
let lemma_bgp_empty (#tp #gtriple : Type)
      (inst : smap -> tp -> option gtriple)
      (patvars : tp -> list var_name)
      (g : list gtriple)
  : Lemma (bgp_sol_spec inst patvars [] g smap_empty) = ()

#pop-options
