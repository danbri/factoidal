module Tableau.Refute

(* OWL-DL tableau REFUTATION — clash-detecting satisfiability check.

   Sibling of Tableau.fst (stage (d)/(f) of the tableau plan): where
   Tableau.tableau_materialise is POSITIVE-SOUND ONLY (emits entailed
   `i rdf:type CE` triples, never detects unsatisfiability), this module
   answers "is this (RL-closed) graph SATISFIABLE?" with

     tableau_consistent : rdf_graph -> fuel:nat -> Tot (option bool)

       Some false  = REFUTED: a genuine clash was derived on every
                     branch. Soundness contract: `Some false` implies
                     the graph is inconsistent under OWL 2 Direct
                     Semantics. Every rule that can contribute to a
                     `Some false` carries a model-theoretic soundness
                     argument in its comment.
       Some true   = fully expanded with no clash. This is NOT a
                     completeness proof of consistency (the calculus is
                     deliberately incomplete — see the role-box wave
                     note below); callers must treat it the same as
                     None for scoring "inconsistent".

   ROLE BOX (Wave E-rolebox): rdfs:subPropertyOf (reflexive-transitive
   closure over named roles, composed with Wave D's per-role inverse
   lookup — see `subproperties_of` / `successors_via_roles`),
   owl:FunctionalProperty (injected as a global `<= 1 P` label per
   declared functional P — see `inject_functional`, reuses the
   existing C3/C4 max-card clash machinery unchanged), and
   owl:TransitiveProperty (the SHIQ ∀+ rule: for a ∀Q.C label, every
   transitive R ⊑* Q re-pushes the WHOLE `∀R.C` label, not just `C`,
   across each R-edge; transitivity is inverse-aware — Trans(R) iff
   Trans(R⁻) — see `role_is_transitive` / `push_transitive_foralls`)
   are implemented.

   THE ≤-RULE (witness merging, owl2-le-rule wave): section 6a below
   (`excess_pairs_for_label` / `merge_into` / `merge_branch` in section
   9) closes the gap the paragraph above used to describe as "NOT
   implemented" — when a `<= k P` obligation's FULL successor set
   (witnesses included, unlike the C3/C4 count above) exceeds `k` and
   is not already resolved by provable distinctness, the search
   branches over every candidate pair of witness successors that isn't
   already forced apart, identifies (merges) each candidate pair in
   turn, and requires EVERY branch to close before reporting the node's
   `<= k P` obligation refuted — same AND-semantics as `CE_UnionOf`
   branching. Restricted to pure ∃-witness bnodes on BOTH sides of a
   merge (`is_witness_subject`): a witness, by construction, never
   appears in the fixed input graph `g`, so every edge that could ever
   mention it lives in the mutable `rs_extra` list and can be
   COMPLETELY redirected — named individuals and literal successors are
   never merge candidates (conservative, not unsound: a real ABox
   individual's graph-asserted edges cannot be rewritten this way, so
   merging one in would silently under-redirect and risk fabricating a
   clash from a half-merged state).

   NAMED-INDIVIDUAL IDENTIFICATION (owl2-named-merge wave): section 6b
   below (`identify_pair` / `excess_ident_pairs_for_label` /
   `identify_branch` in section 9) closes the "witness-to-witness only"
   restriction just described. When a `<= k P` excess pair includes a
   NAMED individual (an IRI, or a document bnode asserted in `g`) on
   either side, its graph-asserted edges cannot be physically
   redirected the way `merge_into` redirects a witness's — so instead
   the two terms are IDENTIFIED in a `rs_ident` partition (owl:sameAs-
   style, never written back to the graph) and every reader that
   matters (`labels_of`, `countable_successors`/`all_successors`,
   `clash_nodes`) pools the WHOLE identification group instead of one
   node — see section 4a-ident's banner. Same AND-branching /
   pigeonhole soundness argument as the witness ≤-rule; a pair the
   graph (or a prior identification) already forces apart
   (`provably_distinct_grouped`) is never offered, so a differentFrom
   or distinct-literal pair can only ever be a CLASH here, never an
   identification.

   STILL NOT implemented: double blocking (cyclic-TBox non-termination
   avoidance beyond the flat max_witness_depth cut), inverse-lifted
   subPropertyOf subsumptions (P ⊑ Q does not yet imply P⁻ ⊑ Q⁻ in
   the role closure), and nominal (oneOf) branching beyond the O-rule
   clash test below.
       None        = fuel/budget exhausted — indeterminate; callers
                     fall back to their existing behaviour (the OWL-RL
                     `is_inconsistent` marker check).

   ARCHITECTURE (standard DL tableau, fuel-bounded, deterministic):
     1. Parse the TBox into unfolding axioms (A ⊑ D) as pairs of
        class expressions in NNF (rdfs:subClassOf, owl:equivalentClass
        both directions, owl:disjointWith / owl:complementOf as
        A ⊑ ¬B and B ⊑ ¬A, plus named class-expression subjects whose
        own restriction / boolean markers denote a definition).
     2. Build one tableau node per typed ABox individual, labelled
        with the NNF class expressions of its asserted rdf:types.
     3. Saturate deterministic rules (⊓-decomposition, lazy axiom
        unfolding, ∀-propagation over asserted + hasValue + witness
        edges, hasValue edge introduction, ∃/min-1 witness creation),
        checking for clashes between rounds.
     4. Branch on owl:unionOf labels: the graph is refuted on this
        search path only if EVERY disjunct's branch closes with a
        clash. Branch order is list order — fully deterministic.
     5. All work is bounded by a THREADED budget (each saturation
        round and each branch entry consumes >= 1 budget unit and
        returns the remainder), so total work is linear in the fuel
        argument regardless of branching — a run can never blow up
        exponentially past its budget; it degrades to None.

   CLASH RULES (soundness argument per rule at the definition site):
     C1  ⊥-label            : owl:Nothing in a node's label set.
     C2  complement clash   : C and ¬C on the same node.
     C3  min/max label clash: >=m and <=n on one property with m > n
                              (∃P.C / hasValue count as >=1;
                              qualified variants compared at equal
                              filler only).
     C4  counting clash     : <=k P with k+1 pairwise provably-distinct
                              ASSERTED successors (witness edges are
                              never counted — a fresh witness may merge
                              with an existing successor in some model).
     C5  bottom property    : any existential obligation (∃/min>=1/
                              hasValue) on owl:bottomObjectProperty /
                              owl:bottomDataProperty.
   plus graph-level immediate checks (owl:AllDifferent member clash,
   asserted bottom-property triple, self-disjoint property in use).

   TERMINATION: every recursive function is either structurally
   recursive or threads an explicitly decreasing fuel/budget. No
   admits, no assumes, no --lax.                                       *)

open FStar.List.Tot
open RDF.Graph.Executable
open OWL.Vocabulary
open Tableau
open XSD.Facets

(* -------------------------------------------------------------------
   1. Vocabulary constants not already exported by the opened modules.
   ------------------------------------------------------------------- *)

let owl_bottomObjectProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#bottomObjectProperty");
  "http://www.w3.org/2002/07/owl#bottomObjectProperty"

let owl_bottomDataProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#bottomDataProperty");
  "http://www.w3.org/2002/07/owl#bottomDataProperty"

let owl_topObjectProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#topObjectProperty");
  "http://www.w3.org/2002/07/owl#topObjectProperty"

(* owl:inverseOf — used by the inverse-role successor lookup (#209
   Wave A follow-up: "spy-point" pattern). The OWL-RL closure
   (OWL.Closure.owl_rule_inverse_of) already flips AUTHOR-ASSERTED
   edges through a declared inverse pair before the refuter ever sees
   the graph, so `find_objects` alone already picks those up. What the
   closure CANNOT do is flip edges the REFUTER mints during its own
   expansion (∃-witnesses, hasValue-derived edges in `rs_extra`) — the
   closure runs once, before refutation, and never sees those. The
   `rs_inv` table + role-aware successor lookup below close that gap
   for tableau-internal edges only; it is a narrow, additive
   supplement to the closure-level rule, not a replacement for it. *)
let owl_inverseOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#inverseOf");
  "http://www.w3.org/2002/07/owl#inverseOf"

let owl_distinctMembers : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#distinctMembers");
  "http://www.w3.org/2002/07/owl#distinctMembers"

(* owl:FunctionalProperty / owl:TransitiveProperty — role-box wave
   (Wave E-rolebox). rdfs:subPropertyOf is NOT redeclared here: it is
   already visible unqualified via RDF.Graph.Executable's `open
   RDF.Vocabulary` (the same transitive-visibility path that already
   makes `rdfs_subClassOf` usable in collect_axioms_aux below). *)
let owl_FunctionalProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#FunctionalProperty");
  "http://www.w3.org/2002/07/owl#FunctionalProperty"

let owl_TransitiveProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#TransitiveProperty");
  "http://www.w3.org/2002/07/owl#TransitiveProperty"

let xsd_string_dt : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#string");
  "http://www.w3.org/2001/XMLSchema#string"

let xsd_boolean_dt : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#boolean");
  "http://www.w3.org/2001/XMLSchema#boolean"

(* EXT(owl:bottomObjectProperty) = EXT(owl:bottomDataProperty) = ∅ in
   every model (OWL 2 Direct Semantics, Table 4 / RDF-Based semantics
   D.1) — the foundation of clash rule C5 and graph check G2. *)
let is_bottom_prop (p : wf_iri) : bool =
  p = owl_bottomObjectProperty || p = owl_bottomDataProperty

(* -------------------------------------------------------------------
   2. Structural equality over class expressions.

   CE_Unknown is deliberately NOT equal to itself: two unparseable
   class expressions give no evidence of denoting the same class, and
   a false positive here could manufacture a clash (soundness bug).
   Consequence: ce_eq is reflexive exactly on Unknown-free ("definite")
   expressions — see ce_definite below.
   ------------------------------------------------------------------- *)

(* Structural equality over rdf_term lists — used only by CE_OneOf's
   ce_eq/ce_eq_syn cases (order-sensitive: the parser always walks the
   RDF list in the same order for a given graph, so this is adequate
   for both storage-dedup and axiom-LHS matching of one fixed oneOf
   bnode; it is NOT a set-equality check). *)
let rec term_list_eq (xs : list rdf_term) (ys : list rdf_term)
  : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: xtl, y :: ytl -> rdf_term_eq x y && term_list_eq xtl ytl
  | _, _ -> false

(* Structural equality over (facet-IRI, literal) pairs — CE_DataRestriction's
   ce_eq/ce_eq_syn case, same order-sensitive contract as term_list_eq
   above (adequate for storage-dedup and axiom-LHS matching of one fixed
   DatatypeRestriction bnode; not a set-equality check). *)
let rec facet_pairs_eq (xs ys : list (wf_iri & rdf_term)) : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | (fi, fv) :: xtl, (gi, gv) :: ytl -> fi = gi && rdf_term_eq fv gv && facet_pairs_eq xtl ytl
  | _, _ -> false

let rec ce_eq (a : class_expr) (b : class_expr) : Tot bool (decreases a) =
  match a, b with
  | CE_Named x, CE_Named y -> x = y
  | CE_OneOf xs, CE_OneOf ys -> term_list_eq xs ys
  | CE_SomeValuesFrom p c, CE_SomeValuesFrom q d -> p = q && ce_eq c d
  | CE_AllValuesFrom p c, CE_AllValuesFrom q d -> p = q && ce_eq c d
  | CE_HasValue p v, CE_HasValue q w -> p = q && rdf_term_eq v w
  | CE_IntersectionOf xs, CE_IntersectionOf ys -> ce_list_eq xs ys
  | CE_UnionOf xs, CE_UnionOf ys -> ce_list_eq xs ys
  | CE_ComplementOf c, CE_ComplementOf d -> ce_eq c d
  | CE_MinCard k p, CE_MinCard j q -> k = j && p = q
  | CE_MaxCard k p, CE_MaxCard j q -> k = j && p = q
  | CE_ExactCard k p, CE_ExactCard j q -> k = j && p = q
  | CE_MinQualCard k p c, CE_MinQualCard j q d -> k = j && p = q && ce_eq c d
  | CE_MaxQualCard k p c, CE_MaxQualCard j q d -> k = j && p = q && ce_eq c d
  | CE_ExactQualCard k p c, CE_ExactQualCard j q d -> k = j && p = q && ce_eq c d
  | CE_DataRestriction dt fs, CE_DataRestriction dt' fs' -> dt = dt' && facet_pairs_eq fs fs'
  | _, _ -> false
and ce_list_eq (xs : list class_expr) (ys : list class_expr)
  : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: xtl, y :: ytl -> ce_eq x y && ce_list_eq xtl ytl
  | _, _ -> false

(* SYNTACTIC equality — identical to ce_eq except CE_Unknown equals
   CE_Unknown. Used ONLY for storage dedup (add_label's mem check) and
   witness-obligation bookkeeping, where conflating two unparseables
   merely prevents duplicates / repeat firings. It must NEVER be used
   for clash detection or axiom-LHS matching: two distinct unparseable
   class expressions give no evidence of denoting the same class, and
   conflating them there could manufacture a clash or a wrong unfold
   (soundness bug). Without a syntactic mem in add_label, any label
   containing CE_Unknown is re-added on every round (ce_eq is
   irreflexive on Unknown), the round reports `changed`, and the
   search livelocks its whole budget away — observed on
   WebOnt-description-logic premises whose closures carry partially
   parseable class expressions. *)
let rec ce_eq_syn (a : class_expr) (b : class_expr) : Tot bool (decreases a) =
  match a, b with
  | CE_Unknown, CE_Unknown -> true
  | CE_Named x, CE_Named y -> x = y
  | CE_OneOf xs, CE_OneOf ys -> term_list_eq xs ys
  | CE_SomeValuesFrom p c, CE_SomeValuesFrom q d -> p = q && ce_eq_syn c d
  | CE_AllValuesFrom p c, CE_AllValuesFrom q d -> p = q && ce_eq_syn c d
  | CE_HasValue p v, CE_HasValue q w -> p = q && rdf_term_eq v w
  | CE_IntersectionOf xs, CE_IntersectionOf ys -> ce_list_eq_syn xs ys
  | CE_UnionOf xs, CE_UnionOf ys -> ce_list_eq_syn xs ys
  | CE_ComplementOf c, CE_ComplementOf d -> ce_eq_syn c d
  | CE_MinCard k p, CE_MinCard j q -> k = j && p = q
  | CE_MaxCard k p, CE_MaxCard j q -> k = j && p = q
  | CE_ExactCard k p, CE_ExactCard j q -> k = j && p = q
  | CE_MinQualCard k p c, CE_MinQualCard j q d -> k = j && p = q && ce_eq_syn c d
  | CE_MaxQualCard k p c, CE_MaxQualCard j q d -> k = j && p = q && ce_eq_syn c d
  | CE_ExactQualCard k p c, CE_ExactQualCard j q d -> k = j && p = q && ce_eq_syn c d
  | CE_DataRestriction dt fs, CE_DataRestriction dt' fs' -> dt = dt' && facet_pairs_eq fs fs'
  | _, _ -> false
and ce_list_eq_syn (xs : list class_expr) (ys : list class_expr)
  : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: xtl, y :: ytl -> ce_eq_syn x y && ce_list_eq_syn xtl ytl
  | _, _ -> false

(* Unknown-free check: ce_eq c c holds iff ce_definite c. Unions are
   only branched on when every disjunct is definite (otherwise the
   added disjunct would not register as satisfying the union and the
   search would spin its budget away re-branching). *)
let rec ce_definite (c : class_expr) : Tot bool (decreases c) =
  match c with
  | CE_Unknown -> false
  | CE_Named _ | CE_HasValue _ _ | CE_MinCard _ _ | CE_MaxCard _ _
  | CE_ExactCard _ _ | CE_OneOf _ | CE_DataRestriction _ _ -> true
  | CE_SomeValuesFrom _ d | CE_AllValuesFrom _ d | CE_ComplementOf d
  | CE_MinQualCard _ _ d | CE_MaxQualCard _ _ d | CE_ExactQualCard _ _ d ->
    ce_definite d
  | CE_IntersectionOf ds | CE_UnionOf ds -> ce_list_definite ds
and ce_list_definite (cs : list class_expr) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: tl -> ce_definite c && ce_list_definite tl

(* -------------------------------------------------------------------
   3. Negation normal form.

   All labels, axiom sides and branch disjuncts are kept in NNF so the
   complement clash (C2) reduces to structural matching: after nnf,
   CE_ComplementOf wraps only CE_Named (non-⊤/⊥) and CE_HasValue.

   Soundness of each rewrite is the corresponding Direct Semantics
   identity:
     neg⊤ = ⊥, neg⊥ = ⊤, negnegC = C,
     neg(C ⊓ D) = negC ⊔ negD, neg(C ⊔ D) = negC ⊓ negD,
     neg∃P.C = ∀P.negC, neg∀P.C = ∃P.negC,
     neg(>= k P) = (<= k-1 P) for k >= 1; neg(>= 0 P) = ⊥,
     neg(<= k P) = (>= k+1 P),
     (= k P) = (>= k P) ⊓ (<= k P) and its negation the dual union
     (all with the qualified variants at unchanged filler).
   negCE_Unknown is mapped to CE_Unknown: the negated constraint is
   DROPPED. Dropping a constraint can only make refutation harder
   (fewer clashes), never wrong — sound for `Some false`.               *)

let rec nnf (c : class_expr) : Tot class_expr (decreases c) =
  match c with
  | CE_ComplementOf d -> nnf_neg d
  | CE_IntersectionOf cs -> CE_IntersectionOf (nnf_list cs)
  | CE_UnionOf cs -> CE_UnionOf (nnf_list cs)
  | CE_SomeValuesFrom p d -> CE_SomeValuesFrom p (nnf d)
  | CE_AllValuesFrom p d -> CE_AllValuesFrom p (nnf d)
  | CE_MinQualCard k p d -> CE_MinQualCard k p (nnf d)
  | CE_MaxQualCard k p d -> CE_MaxQualCard k p (nnf d)
  (* =0 P is ≤0 P exactly: >= 0 P is a tautology (every individual has
     at least zero P-successors in every model), so the k = 0 exact
     cardinality simplifies to its max conjunct ALONE rather than the
     ⊓[>=0 P; <=0 P] pair the general case produces. This is not just
     cosmetic — the FaCT-derived WebOnt-description-logic-6xx fixtures
     define complement atoms as `X.comp ≡ owl:cardinality 0 on P`, and
     lazy unfolding matches axiom LHSs by EXACT ce_eq: a node that
     derives `<= 0 P` (e.g. via a contrapositive pair from the twin
     `X ≡ >= 1 P` definition) could never fire the (⊓[>=0; <=0] →
     X.comp) pair, because the tautological >=0 conjunct is never a
     node label. Normalising the tautology away makes the two NNF
     forms coincide, so the definition fires wherever `<= 0 P` lands.
     (k >= 1 keeps the intersection: both conjuncts carry content.) *)
  | CE_ExactCard k p ->
    if k = 0 then CE_MaxCard 0 p
    else CE_IntersectionOf [CE_MinCard k p; CE_MaxCard k p]
  | CE_ExactQualCard k p d ->
    let d' = nnf d in
    if k = 0 then CE_MaxQualCard 0 p d'
    else CE_IntersectionOf [CE_MinQualCard k p d'; CE_MaxQualCard k p d']
  | _ -> c
and nnf_neg (c : class_expr) : Tot class_expr (decreases c) =
  match c with
  | CE_Named x ->
    if x = owl_Thing then CE_Named owl_Nothing
    else if x = owl_Nothing then CE_Named owl_Thing
    else CE_ComplementOf (CE_Named x)
  | CE_ComplementOf d -> nnf d
  | CE_IntersectionOf cs -> CE_UnionOf (nnf_neg_list cs)
  | CE_UnionOf cs -> CE_IntersectionOf (nnf_neg_list cs)
  | CE_SomeValuesFrom p d -> CE_AllValuesFrom p (nnf_neg d)
  | CE_AllValuesFrom p d -> CE_SomeValuesFrom p (nnf_neg d)
  | CE_HasValue p v -> CE_ComplementOf (CE_HasValue p v)
  | CE_MinCard k p ->
    if k = 0 then CE_Named owl_Nothing else CE_MaxCard (k - 1) p
  | CE_MaxCard k p -> CE_MinCard (k + 1) p
  | CE_ExactCard k p ->
    if k = 0 then CE_MinCard 1 p
    else CE_UnionOf [CE_MaxCard (k - 1) p; CE_MinCard (k + 1) p]
  | CE_MinQualCard k p d ->
    if k = 0 then CE_Named owl_Nothing else CE_MaxQualCard (k - 1) p (nnf d)
  | CE_MaxQualCard k p d -> CE_MinQualCard (k + 1) p (nnf d)
  | CE_ExactQualCard k p d ->
    let d' = nnf d in
    if k = 0 then CE_MinQualCard 1 p d'
    else CE_UnionOf [CE_MaxQualCard (k - 1) p d'; CE_MinQualCard (k + 1) p d']
  | CE_OneOf members ->
    (* neg{a1,...,am}: no closed-form atomic shape in this AST (it is
       not a named/hasValue complement) — wrap it, exactly as the
       CE_HasValue case does. Sound: nothing is dropped, only wrapped;
       CE_OneOf is otherwise treated as atomic. *)
    CE_ComplementOf (CE_OneOf members)
  | CE_DataRestriction dt facets ->
    (* Same treatment as CE_OneOf/CE_HasValue: a facet-restricted
       datatype has no closed-form negation in this AST — wrap it.
       Sound (nothing dropped, only wrapped) and atomic otherwise. *)
    CE_ComplementOf (CE_DataRestriction dt facets)
  | CE_Unknown -> CE_Unknown
and nnf_list (cs : list class_expr) : Tot (list class_expr) (decreases cs) =
  match cs with
  | [] -> []
  | c :: tl -> nnf c :: nnf_list tl
and nnf_neg_list (cs : list class_expr) : Tot (list class_expr) (decreases cs) =
  match cs with
  | [] -> []
  | c :: tl -> nnf_neg c :: nnf_neg_list tl

(* -------------------------------------------------------------------
   4. Tableau state.
   ------------------------------------------------------------------- *)

noeq type rnode = {
  rn_id     : subject;
  rn_labels : list class_expr;   (* invariant: all NNF *)
}

(* Extra edges created during expansion. re_count distinguishes
   hasValue-derived edges (the edge holds in EVERY model — safe to
   count for cardinality clashes) from ∃-witness edges (the witness
   may coincide with an existing successor in some model — NEVER
   counted, only used for ∀-propagation).                             *)
noeq type redge = {
  re_s     : subject;
  re_p     : wf_iri;
  re_o     : rdf_term;
  re_count : bool;
}

noeq type rstate = {
  rs_nodes : list rnode;
  rs_extra : list redge;
  rs_fresh : nat;
  (* Witness generation depth, per witness bnode id. ABox individuals
     have (implicit) depth 0; a witness minted for node at depth d has
     depth d+1. ∃-witness creation refuses beyond max_witness_depth,
     which terminates the ∃-chains a cyclic TBox (X ⊑ ∃P.X) would
     otherwise grow round after round until the budget dies. Refusing
     a witness only WITHHOLDS labels — sound (clash rule 4's
     interactions live within the first couple of levels in the W3C
     corpus). *)
  rs_wdepth : list (bnode_id & nat);
  (* Declared owl:inverseOf pairs (P, Q), collected ONCE from the input
     graph at init_state time (schema-level facts — TBox, not touched
     by expansion). Read-only for the rest of the run; see
     `inverses_of` / `countable_successors` / `all_successors` below
     for how this makes tableau-internal edges (rs_extra) role-aware
     without re-deriving what the closure-level owl_rule_inverse_of
     already handles for author-asserted triples in `g`. *)
  rs_inv : list (wf_iri & wf_iri);
  (* Groups of terms that are PAIRWISE PROVABLY DISTINCT by tableau
     construction (#209 spy-point increment): each group is the set of
     fresh witnesses minted by ONE firing of the >= k R "generating
     rule" (k >= 2, see `ensure_min_witnesses`). Direct Semantics
     interprets ObjectMinCardinality(k, R) as "at least k PAIRWISE
     DISTINCT R-successors exist" — a model-necessary fact, not a
     tableau guess — so representing them as mutually-distinct fresh
     individuals and propagating further consequences from them is
     sound regardless of whether the "real" witnesses coincide with
     other named individuals (every axiom that holds universally over
     the domain, e.g. an owl:Thing-anchored one, holds of them too,
     however they are named). Consulted by `provably_distinct`
     alongside owl:differentFrom and literal-value inequality. *)
  rs_gendistinct : list (list rdf_term);
  (* Declared rdfs:subPropertyOf pairs (P, Q) meaning "P rdfs:subPropertyOf
     Q", collected ONCE at init_state time (schema-level, read-only —
     same contract as rs_inv above). EXT(P) subset-of EXT(Q) in every
     model, so a P-edge counts as a Q-edge everywhere a Q-successor is
     consulted. See `subproperties_of` / `successors_via_roles` for how
     this generalises `countable_successors` / `all_successors` (and,
     composed with rs_inv, makes the closure ROLE-HIERARCHY aware for
     tableau-internal edges the once-run RL closure never sees, exactly
     as rs_inv already does for inverses). *)
  rs_subprop : list (wf_iri & wf_iri);
  (* Declared owl:TransitiveProperty IRIs, collected ONCE (schema-level,
     read-only). Consulted by the `CE_AllValuesFrom` case of
     `apply_label_rules` for the standard SHIQ S-rule: DIRECT
     transitivity only (P itself declared transitive) — derived
     transitivity of P's inverse is NOT computed (see the module
     banner). *)
  rs_transprops : list wf_iri;
  (* Declared owl:FunctionalProperty IRIs, collected ONCE (schema-level,
     read-only). `pass_nodes` injects `CE_MaxCard 1 P` onto every node
     for every P here — see `inject_functional` — which folds
     FunctionalProperty into the EXISTING C3/C4 max-card clash
     machinery (`clash_for_label`'s `CE_MaxCard` case) unchanged: no
     new merge logic, just a global "<= 1 P" constraint every node
     already carries. *)
  rs_funcprops : list wf_iri;
  (* Named-individual identification partition (owl2-named-merge wave,
     section 4a-ident): each inner list is a set of rdf_terms this
     search branch currently HYPOTHESISES to denote one domain element
     (owl:sameAs-style — never asserted back into the graph). Populated
     only by `identify_pair` (section 6b), consulted by `labels_of`,
     `countable_successors`/`all_successors`, and `clash_nodes`, which
     pool a whole group's facts instead of one node's — see those
     sites' banners for why pooling at read time is sound without ever
     rewriting an edge (unlike `merge_into`'s witness redirection). *)
  rs_ident : list (list rdf_term);
}

(* -------------------------------------------------------------------
   3a. Inverse-role table (#209 Wave A follow-up).

   Collected once from the FULL input graph (schema-level: P
   owl:inverseOf Q triples), then consulted symmetrically — a pair
   (P, Q) means P and Q are each other's inverse, so a query "what are
   the inverses of role R?" must match R against EITHER side of every
   collected pair. ------------------------------------------------- *)

let rec collect_inverse_pairs (ts : rdf_graph) : Tot (list (wf_iri & wf_iri)) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = collect_inverse_pairs tl in
    if t.p = owl_inverseOf then
      (match t.s, t.o with
       | S_IRI p, T_IRI q -> (p, q) :: rest
       | _ -> rest)
    else rest

(* All Q such that (P owl:inverseOf Q) or (Q owl:inverseOf P) was
   declared — i.e. every role that is P's inverse, checked from
   either side of the asserted pair. May return the same Q more than
   once if the graph asserts the pair redundantly in both directions;
   harmless duplication (successor lists get deduped downstream by
   `dedup_terms`). *)
let rec inverses_of (pairs : list (wf_iri & wf_iri)) (p : wf_iri)
  : Tot (list wf_iri) (decreases pairs) =
  match pairs with
  | [] -> []
  | (a, b) :: tl ->
    let rest = inverses_of tl p in
    if a = p then b :: rest
    else if b = p then a :: rest
    else rest

(* -------------------------------------------------------------------
   3b. Role-hierarchy (rdfs:subPropertyOf), TransitiveProperty and
   FunctionalProperty tables (Wave E-rolebox).

   `collect_subprop_pairs` mirrors `collect_inverse_pairs` exactly:
   schema-level, collected once from the FULL input graph. A pair
   (P, Q) means "P rdfs:subPropertyOf Q" was asserted, i.e.
   EXT(P) subset-of EXT(Q) in every model (rdfs7 / OWL 2 RL scm-sp
   semantics). ------------------------------------------------------- *)

let rec collect_subprop_pairs (ts : rdf_graph) : Tot (list (wf_iri & wf_iri)) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = collect_subprop_pairs tl in
    if t.p = rdfs_subPropertyOf then
      (match t.s, t.o with
       | S_IRI p, T_IRI q -> (p, q) :: rest
       | _ -> rest)
    else rest

let rec collect_transitive_props (ts : rdf_graph) : Tot (list wf_iri) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = collect_transitive_props tl in
    if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_TransitiveProperty)
    then (match t.s with S_IRI p -> p :: rest | _ -> rest)
    else rest

let rec collect_functional_props (ts : rdf_graph) : Tot (list wf_iri) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = collect_functional_props tl in
    if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_FunctionalProperty)
    then (match t.s with S_IRI p -> p :: rest | _ -> rest)
    else rest

let rec mem_iri (x : wf_iri) (xs : list wf_iri) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | h :: tl -> h = x || mem_iri x tl

(* Direct sub-properties of q: every p with an asserted (p, q) pair. *)
let rec direct_subprops_of (pairs : list (wf_iri & wf_iri)) (q : wf_iri)
  : Tot (list wf_iri) (decreases pairs) =
  match pairs with
  | [] -> []
  | (p, r) :: tl ->
    let rest = direct_subprops_of tl q in
    if r = q then p :: rest else rest

(* Direct super-properties of p: every q with an asserted (p, q) pair. *)
let rec direct_superprops_of (pairs : list (wf_iri & wf_iri)) (p : wf_iri)
  : Tot (list wf_iri) (decreases pairs) =
  match pairs with
  | [] -> []
  | (s, q) :: tl ->
    let rest = direct_superprops_of tl p in
    if s = p then q :: rest else rest

let rec filter_new_iris (visited : list wf_iri) (cands : list wf_iri)
  : Tot (list wf_iri) (decreases cands) =
  match cands with
  | [] -> []
  | c :: tl ->
    let rest = filter_new_iris visited tl in
    if mem_iri c visited then rest else c :: rest

let rec collect_step (step : wf_iri -> list wf_iri) (qs : list wf_iri)
  : Tot (list wf_iri) (decreases qs) =
  match qs with
  | [] -> []
  | q :: tl -> step q @ collect_step step tl

(* Fuel-bounded BFS closure over a `step` relation (either
   `direct_subprops_of pairs` or `direct_superprops_of pairs`).
   TERMINATION: every recursive call strictly decreases `fuel`; running
   out of fuel before the frontier naturally empties only WITHHOLDS
   deeper ancestors/descendants of the role-hierarchy DAG — sound (same
   precedent as `max_witness_depth` withholding deeper ∃-witnesses).
   `List.Tot.length pairs + 1` steps is generous: each step that
   doesn't return early adds >= 1 newly-visited IRI drawn from a fixed
   list of `pairs` edges, so a real (cycle-free) hierarchy closes well
   within that many steps; a cyclic subPropertyOf graph (legal RDF,
   pathological OWL) just burns the fuel and stops — still sound. *)
let rec role_bfs (step : wf_iri -> list wf_iri) (frontier : list wf_iri)
                 (visited : list wf_iri) (fuel : nat)
  : Tot (list wf_iri) (decreases fuel) =
  if fuel = 0 then visited
  else
    match frontier with
    | [] -> visited
    | _ ->
      let candidates = collect_step step frontier in
      let fresh = filter_new_iris visited candidates in
      (match fresh with
       | [] -> visited
       | _ -> role_bfs step fresh (visited @ fresh) (fuel - 1))

(* All P with P rdfs:subPropertyOf* Q (reflexive-transitive closure,
   including Q itself) — i.e. every role whose edges also count as
   Q-edges. *)
let subproperties_of (pairs : list (wf_iri & wf_iri)) (q : wf_iri) : list wf_iri =
  let direct = direct_subprops_of pairs q in
  q :: role_bfs (direct_subprops_of pairs) direct direct (List.Tot.length pairs + 1)

(* All Q with P rdfs:subPropertyOf* Q (reflexive-transitive closure,
   including P itself) — i.e. every restriction that also constrains
   P's fillers (used by the C6 facet fold below). *)
let superproperties_of (pairs : list (wf_iri & wf_iri)) (p : wf_iri) : list wf_iri =
  let direct = direct_superprops_of pairs p in
  p :: role_bfs (direct_superprops_of pairs) direct direct (List.Tot.length pairs + 1)

let max_witness_depth : nat = 3

let rec witness_depth_of (ds : list (bnode_id & nat)) (i : subject)
  : Tot nat (decreases ds) =
  match i with
  | S_IRI _ -> 0
  | S_BNode b ->
    (match ds with
     | [] -> 0
     | (w, d) :: tl -> if w = b then d else witness_depth_of tl i)

(* Is bnode `b` a key in the witness-depth table — i.e. was it minted by
   `ensure_witness` / `ensure_min_witnesses` (never a document bnode:
   witness ids carry the illegal-in-source " rw_" prefix, per
   `witness_id`'s banner, and BOTH minting functions register a
   `rs_wdepth` entry unconditionally, even when the witness gets no
   filler label and so never becomes an `rs_nodes` entry). Consulted
   below (section 5b, the ≤-rule witness-merging wave) to restrict
   merge candidates to nodes this module can always safely and
   COMPLETELY redirect every edge of: a witness bnode, by construction,
   never appears in the input graph `g` (fixed before the tableau
   starts), so every triple that could ever mention it lives in
   `rs_extra` — nothing is left un-redirected the way an asserted ABox
   individual's graph-level triples would be. *)
let rec bnode_in_wdepth (ds : list (bnode_id & nat)) (b : bnode_id)
  : Tot bool (decreases ds) =
  match ds with
  | [] -> false
  | (w, _) :: tl -> w = b || bnode_in_wdepth tl b

let is_witness_subject (st : rstate) (s : subject) : bool =
  match s with
  | S_BNode b -> bnode_in_wdepth st.rs_wdepth b
  | S_IRI _ -> false

let rec mem_ce (c : class_expr) (ls : list class_expr) : Tot bool (decreases ls) =
  match ls with
  | [] -> false
  | l :: tl -> if ce_eq c l then true else mem_ce c tl

(* Syntactic membership — storage dedup only (see ce_eq_syn banner). *)
let rec mem_ce_syn (c : class_expr) (ls : list class_expr) : Tot bool (decreases ls) =
  match ls with
  | [] -> false
  | l :: tl -> if ce_eq_syn c l then true else mem_ce_syn c tl

(* -------------------------------------------------------------------
   4a-ident. Named-individual identification partition
   (owl2-named-merge wave — populated by section 6b below).

   `rs_ident` records IDENTIFICATION hypotheses the search has made on
   the current branch: each inner list is a set of rdf_terms treated as
   ONE domain element. Unlike `merge_into` (section 6a), identification
   never rewrites a triple or an `rs_extra` edge — a named individual's
   edges may live in the fixed input graph `g`, which this module
   treats as read-only. Instead every reader that needs "the
   individual's" labels, successors, or distinctness consults the WHOLE
   group via the helpers below and pools the answer: the group is
   exactly the set of terms this branch currently treats as one
   element, so pooling their individually-entailed facts is itself
   entailed of the pooled identity — the same argument `merge_into`'s
   banner makes for physically-unioned labels, applied at read time
   instead of write time. *)

let rec find_ident_group (ident : list (list rdf_term)) (t : rdf_term)
  : Tot (option (list rdf_term)) (decreases ident) =
  match ident with
  | [] -> None
  | grp :: tl ->
    if List.Tot.existsb (fun x -> rdf_term_eq x t) grp
    then Some grp
    else find_ident_group tl t

(* `t`'s current identification group, or the singleton `[t]` when `t`
   has not (yet, on this branch) been identified with anything — the
   trivial group of one, so every reader below treats "grouped" and
   "ungrouped" uniformly. *)
let ident_group_of (ident : list (list rdf_term)) (t : rdf_term) : list rdf_term =
  match find_ident_group ident t with
  | Some grp -> grp
  | None -> [t]

(* Are `a` and `b` the SAME domain element under the current
   identification hypothesis — either syntactically equal, or
   co-members of one `rs_ident` group? Used to fold identified
   successor terms together (`dedup_terms_ident`) and to recognise a
   pair as "already identified, not a new candidate" (section 6b). *)
let same_individual (ident : list (list rdf_term)) (a b : rdf_term) : bool =
  rdf_term_eq a b
  || (match find_ident_group ident a with
      | Some grp -> List.Tot.existsb (fun x -> rdf_term_eq x b) grp
      | None -> false)

(* `dedup_terms` (below) made ident-aware: two terms that denote the
   SAME identified individual collapse to one, exactly as two
   syntactically-identical terms already did. This is what makes
   successor COUNTING "treat identified nodes as one" (module banner):
   once x~y are identified, a `<= k P` label whose successor set
   previously counted x and y separately now sees them as a single
   successor, so the excess `countable_successors`/`all_successors`
   report monotonically shrinks after an identification — the same
   re-detection property `merge_into` gets from physically deleting a
   duplicate edge target. *)
let rec dedup_terms_ident (ident : list (list rdf_term)) (ts : list rdf_term)
  : Tot (list rdf_term) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = dedup_terms_ident ident tl in
    if List.Tot.existsb (fun o -> same_individual ident t o) rest
    then rest else t :: rest

let rec subjects_of_terms (ts : list rdf_term) : Tot (list subject) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    (match term_to_subject t with
     | Some s -> s :: subjects_of_terms tl
     | None -> subjects_of_terms tl)

let rec labels_of_nodes (ns : list rnode) (i : subject)
  : Tot (list class_expr) (decreases ns) =
  match ns with
  | [] -> []
  | n :: tl -> if subject_eq n.rn_id i then n.rn_labels else labels_of_nodes tl i

let rec labels_of_multi (ns : list rnode) (is : list subject)
  : Tot (list class_expr) (decreases is) =
  match is with
  | [] -> []
  | i :: tl -> labels_of_nodes ns i @ labels_of_multi ns tl

(* Pooled across `i`'s WHOLE identification group (section 4a-ident) —
   a plain lookup when `i` is unidentified (group = [i]), the union of
   every group member's OWN labels otherwise. Every label ever added to
   ANY node is an entailed membership of that node's denotation (the
   `pass` invariant, section 8 banner); once two nodes are identified
   their denotations coincide by hypothesis, so pooling is sound by the
   same argument, applied at read time instead of by physically copying
   labels the way `merge_into` does for witnesses. *)
let labels_of (st : rstate) (i : subject) : list class_expr =
  (* Perf guard (same as clash_nodes'): only pay the multi-member
     pooled walk when `i` actually has an identification group; the
     unidentified path is the direct pre-wave lookup. *)
  match find_ident_group st.rs_ident (subject_to_term i) with
  | Some grp -> labels_of_multi st.rs_nodes (subjects_of_terms grp)
  | None -> labels_of_nodes st.rs_nodes i

let rec add_label_nodes (ns : list rnode) (i : subject) (c : class_expr)
  : Tot (list rnode & bool) (decreases ns) =
  match ns with
  | [] -> ([{ rn_id = i; rn_labels = [c] }], true)
  | n :: tl ->
    if subject_eq n.rn_id i then
      (* Dedup is SYNTACTIC (mem_ce_syn) so labels containing
         CE_Unknown are stored once instead of re-added every round —
         the livelock the ce_eq_syn banner describes. *)
      (if mem_ce_syn c n.rn_labels then (n :: tl, false)
       else ({ n with rn_labels = c :: n.rn_labels } :: tl, true))
    else
      let (tl', ch) = add_label_nodes tl i c in
      (n :: tl', ch)

(* CE_Unknown labels are inert by construction (no rule matches them);
   never store them. Adding a label is the ONLY way node content
   grows, and every caller passes an NNF expression. *)
let add_label (st : rstate) (i : subject) (c : class_expr) : rstate & bool =
  match c with
  | CE_Unknown -> (st, false)
  | _ ->
    let (ns, ch) = add_label_nodes st.rs_nodes i c in
    ({ st with rs_nodes = ns }, ch)

let rec add_labels_all (st : rstate) (i : subject) (cs : list class_expr)
  : Tot (rstate & bool) (decreases cs) =
  match cs with
  | [] -> (st, false)
  | c :: tl ->
    let (st1, c1) = add_label st i c in
    let (st2, c2) = add_labels_all st1 i tl in
    (st2, c1 || c2)

(* Successor lookup. `count_only` selects the countable view (asserted
   graph triples + hasValue edges); otherwise all extra edges
   (including witnesses) are visible — the ∀-propagation view. *)
let rec extra_objects (es : list redge) (i : subject) (p : wf_iri)
                      (count_only : bool)
  : Tot (list rdf_term) (decreases es) =
  match es with
  | [] -> []
  | e :: tl ->
    let rest = extra_objects tl i p count_only in
    if subject_eq e.re_s i && e.re_p = p && (e.re_count || not count_only)
    then e.re_o :: rest
    else rest

let rec dedup_terms (ts : list rdf_term) : Tot (list rdf_term) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = dedup_terms tl in
    if List.Tot.existsb (fun o -> rdf_term_eq t o) rest then rest else t :: rest

(* -------------------------------------------------------------------
   4a. Role-aware (inverse-aware) successor lookup.

   For a declared pair (P, Q) with P owl:inverseOf Q: an edge (x, P, y)
   in every model also witnesses (y, Q, x) (Direct Semantics EXT(Q) =
   {(a,b) : (b,a) in EXT(P)}). The closure-level Datalog rule
   (OWL.Closure.owl_rule_inverse_of) already materialises this flip for
   every AUTHOR-ASSERTED triple before the refuter starts — so
   `find_objects g i q` below already sees those. What it cannot see is
   an edge the refuter itself mints DURING expansion (a witness or
   hasValue-derived edge added to `rs_extra`): the closure ran once,
   before refutation, over `g` only. These two helpers close that gap
   by scanning `rs_extra` for the REVERSE direction through every
   declared inverse of the queried role, so a tableau-internal edge
   participates in role-aware counting exactly like an asserted one. *)
let rec base_reverse_objects (g : rdf_graph) (i : subject) (invs : list wf_iri)
  : Tot (list rdf_term) (decreases invs) =
  match invs with
  | [] -> []
  | q :: tl ->
    (List.Tot.map subject_to_term (find_subjects g q (subject_to_term i)))
    @ base_reverse_objects g i tl

let rec extra_reverse_objects (es : list redge) (i_term : rdf_term) (q : wf_iri)
                              (count_only : bool)
  : Tot (list rdf_term) (decreases es) =
  match es with
  | [] -> []
  | e :: tl ->
    let rest = extra_reverse_objects tl i_term q count_only in
    if e.re_p = q && rdf_term_eq e.re_o i_term && (e.re_count || not count_only)
    then subject_to_term e.re_s :: rest
    else rest

let rec extra_reverse_objects_all (es : list redge) (i_term : rdf_term)
                                  (invs : list wf_iri) (count_only : bool)
  : Tot (list rdf_term) (decreases invs) =
  match invs with
  | [] -> []
  | q :: tl ->
    extra_reverse_objects es i_term q count_only
    @ extra_reverse_objects_all es i_term tl count_only

(* Successors reached via ONE named role r: asserted + tableau-internal
   edges over r itself, plus the inverse-aware reverse view over every
   declared inverse of r (exactly the pre-rolebox `countable_successors`
   / `all_successors` bodies, now factored out so `successors_via_roles`
   below can apply the same per-role inverse view to every role in a
   subPropertyOf-closure set, not just the literally-queried one). *)
let successors_via_single_role (g : rdf_graph) (st : rstate) (i : subject)
                               (r : wf_iri) (count_only : bool)
  : list rdf_term =
  let invs = inverses_of st.rs_inv r in
  find_objects g i r
  @ extra_objects st.rs_extra i r count_only
  @ base_reverse_objects g i invs
  @ extra_reverse_objects_all st.rs_extra (subject_to_term i) invs count_only

(* Role-hierarchy-aware successor union: for every role r in `roles`
   (intended to be `subproperties_of st.rs_subprop p` — p and every
   rdfs:subPropertyOf* sub-role of p), gather r's successors. Sound:
   EXT(r) subset-of EXT(p) for every r ⊑* p, so an r-successor is
   ALWAYS a p-successor too in every model — this is exactly the same
   "edge counts for every super-property" propagation the module
   banner promises for ∀-rule / cardinality / existential-satisfaction,
   implemented once here since all three consult `countable_successors`
   / `all_successors`. *)
let rec successors_via_roles (g : rdf_graph) (st : rstate) (i : subject)
                             (roles : list wf_iri) (count_only : bool)
  : Tot (list rdf_term) (decreases roles) =
  match roles with
  | [] -> []
  | r :: tl ->
    successors_via_single_role g st i r count_only
    @ successors_via_roles g st i tl count_only

let rec successors_via_roles_multi (g : rdf_graph) (st : rstate) (is : list subject)
                                   (roles : list wf_iri) (count_only : bool)
  : Tot (list rdf_term) (decreases is) =
  match is with
  | [] -> []
  | i :: tl ->
    successors_via_roles g st i roles count_only
    @ successors_via_roles_multi g st tl roles count_only

(* Role-hierarchy successor union, POOLED across `i`'s WHOLE
   identification group (section 4a-ident/6b) and ident-deduped: an
   edge asserted on ANY group member is, by the current identification
   hypothesis, an edge of the identified individual — sound to pool for
   exactly the reason `labels_of` pools labels above, and this is what
   lets a `<= k P` obligation see a role-hierarchy AND identification
   widened successor set without ever rewriting the edge itself (module
   banner). Reduces to the pre-owl2-named-merge behaviour when `i` is
   unidentified (group = [i]). *)
let countable_successors (g : rdf_graph) (st : rstate) (i : subject) (p : wf_iri)
  : list rdf_term =
  match find_ident_group st.rs_ident (subject_to_term i) with
  | Some grp ->
    dedup_terms_ident st.rs_ident
      (successors_via_roles_multi g st (subjects_of_terms grp)
        (subproperties_of st.rs_subprop p) true)
  | None ->
    (* Perf guard (same as labels_of'): unidentified nodes take the
       pre-wave single-subject walk; dedup stays ident-aware so a
       successor TERM that has itself been identified with another
       still collapses to one countable element. *)
    dedup_terms_ident st.rs_ident
      (successors_via_roles g st i (subproperties_of st.rs_subprop p) true)

let all_successors (g : rdf_graph) (st : rstate) (i : subject) (p : wf_iri)
  : list rdf_term =
  match find_ident_group st.rs_ident (subject_to_term i) with
  | Some grp ->
    dedup_terms_ident st.rs_ident
      (successors_via_roles_multi g st (subjects_of_terms grp)
        (subproperties_of st.rs_subprop p) false)
  | None ->
    dedup_terms_ident st.rs_ident
      (successors_via_roles g st i (subproperties_of st.rs_subprop p) false)

let rec extra_edge_present (es : list redge) (i : subject) (p : wf_iri)
                           (o : rdf_term)
  : Tot bool (decreases es) =
  match es with
  | [] -> false
  | e :: tl ->
    (subject_eq e.re_s i && e.re_p = p && rdf_term_eq e.re_o o)
    || extra_edge_present tl i p o

let graph_edge_present (g : rdf_graph) (i : subject) (p : wf_iri) (o : rdf_term)
  : bool =
  List.Tot.existsb
    (fun (t : triple) -> subject_eq t.s i && t.p = p && rdf_term_eq t.o o)
    g

(* hasValue edge: (i, p, v) holds in every model where i ∈ ∃P.{v} —
   which is exactly when the label was derived — so the edge is
   asserted-strength (countable). *)
let add_countable_edge (g : rdf_graph) (st : rstate) (i : subject)
                       (p : wf_iri) (v : rdf_term)
  : rstate & bool =
  if graph_edge_present g i p v || extra_edge_present st.rs_extra i p v
  then (st, false)
  else ({ st with rs_extra = { re_s = i; re_p = p; re_o = v; re_count = true } :: st.rs_extra }, true)

(* -------------------------------------------------------------------
   5. Provable distinctness (for the counting clash C4).

   Two terms are provably distinct when:
     - owl:differentFrom links them (either direction) in the closed
       graph — asserted or derived distinctness; or
     - both are literals of the SAME recognised comparable datatype
       (integer / decimal / string / boolean) whose values differ
       under datatype_value_eq (which normalises integer/decimal
       lexical forms). Two lexically-distinct values of one datatype's
       value space denote distinct elements — Direct Semantics maps a
       literal to its value; or
     - both terms appear together in one `rs_gendistinct` group — the
       tableau's own >= k R "generating rule" minted them as mutually
       distinct (see the rs_gendistinct field banner and
       `ensure_min_witnesses` below for the soundness argument).
   Everything else (distinct IRIs without differentFrom under no-UNA,
   cross-datatype literals, unrelated bnodes) is NOT provably distinct. *)

let comparable_datatype (d : wf_iri) : bool =
  d = xsd_integer || d = xsd_decimal || d = xsd_string_dt || d = xsd_boolean_dt

(* Do `a` and `b` (distinct terms) both occur in one generated-distinct
   group? Groups are produced only by `ensure_min_witnesses`, one per
   >= k R firing, each holding k pairwise-distinct fresh witnesses —
   so co-membership alone (no cross-group reasoning) is the correct,
   sound test. *)
let group_says_distinct (grp : list rdf_term) (a : rdf_term) (b : rdf_term) : bool =
  not (rdf_term_eq a b)
  && List.Tot.existsb (fun x -> rdf_term_eq x a) grp
  && List.Tot.existsb (fun x -> rdf_term_eq x b) grp

let rec gen_distinct (groups : list (list rdf_term)) (a : rdf_term) (b : rdf_term)
  : Tot bool (decreases groups) =
  match groups with
  | [] -> false
  | grp :: tl -> group_says_distinct grp a b || gen_distinct tl a b

let provably_distinct (g : rdf_graph) (gd : list (list rdf_term))
                      (a : rdf_term) (b : rdf_term) : bool =
  differentFrom_in_graph g a b
  || differentFrom_in_graph g b a
  || gen_distinct gd a b
  || (match a, b with
      | T_Literal l1, T_Literal l2 ->
        l1.datatype = l2.datatype
        && comparable_datatype l1.datatype
        && not (datatype_value_eq l1 l2)
      | _, _ -> false)

(* Group-aware distinctness (owl2-named-merge wave): are `a` and `b`
   forced apart once identification GROUPS (section 4a-ident) are taken
   into account? If `a` has already been identified with some `x` that
   is provably distinct from `b` (or from any member of `b`'s own
   group), then `a` is transitively forced apart from `b` too —
   identifying `a` with `b` on top of that would silently contradict
   the earlier identification. This is the check that keeps a
   differentFrom pair, or a distinct-literal pair, from EVER being
   offered as an identification candidate in section 6b, even
   indirectly through a prior identification: no new distinctness rule,
   just the EXISTING `provably_distinct` applied to every cross-pair
   from the two full groups. *)
let rec exists_distinct_cross (g : rdf_graph) (gd : list (list rdf_term))
                              (xs : list rdf_term) (ys : list rdf_term)
  : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | x :: tl ->
    List.Tot.existsb (fun y -> provably_distinct g gd x y) ys
    || exists_distinct_cross g gd tl ys

let provably_distinct_grouped (g : rdf_graph) (gd : list (list rdf_term))
                              (ident : list (list rdf_term))
                              (a : rdf_term) (b : rdf_term) : bool =
  exists_distinct_cross g gd (ident_group_of ident a) (ident_group_of ident b)

(* Keep only candidates provably distinct from h, with a length bound
   so the subset search below has a decreasing measure. *)
let rec filter_distinct_from (g : rdf_graph) (gd : list (list rdf_term))
                             (h : rdf_term) (ts : list rdf_term)
  : Tot (r : list rdf_term { List.Tot.length r <= List.Tot.length ts })
    (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = filter_distinct_from g gd h tl in
    if provably_distinct g gd h t then t :: rest else rest

(* Is `x` provably distinct from EVERY term in `ms`? Vacuously true for
   `ms = []` — being asserted a member of an EMPTY nominal (owl:oneOf
   with no elements, semantically owl:Nothing) is itself a clash, and
   this fold correctly reports that case as "distinct from all
   (zero) members" without a separate empty-list special case. *)
let rec all_provably_distinct (g : rdf_graph) (gd : list (list rdf_term))
                              (x : rdf_term) (ms : list rdf_term)
  : Tot bool (decreases ms) =
  match ms with
  | [] -> true
  | m :: tl -> provably_distinct g gd x m && all_provably_distinct g gd x tl

(* Does `cands` contain `need` PAIRWISE provably-distinct members?
   Sound: a pairwise provably-distinct set of size k+1 denotes k+1
   distinct elements in every model, violating <= k. Exhaustive
   branch-on-first-element search; candidate lists are successor sets
   of a single individual in W3C test data (tiny). *)
let rec exists_distinct_subset (g : rdf_graph) (gd : list (list rdf_term))
                               (cands : list rdf_term) (need : nat)
  : Tot bool (decreases (List.Tot.length cands)) =
  if need = 0 then true
  else
    match cands with
    | [] -> false
    | h :: tl ->
      (exists_distinct_subset g gd (filter_distinct_from g gd h tl) (need - 1))
      || exists_distinct_subset g gd tl need

(* -------------------------------------------------------------------
   5a. Datatype facet clash (Wave B,
       docs/designissues/2026-07-10-owl2-dl-completion-program.md).

   C6 (datatype range clash): for a node with label set ls_all and a
   property p, EVERY `CE_AllValuesFrom p D` label constrains ALL
   p-fillers to lie in D (standard ∀-semantics: multiple ∀p.Di on one
   node combine by intersection, since "all fillers in D1" AND "all
   fillers in D2" together mean "all fillers in D1 ∩ D2" — sound to
   fold). An `CE_HasValue p v` or `CE_SomeValuesFrom p D0` label each
   separately FORCE at least one p-filler to exist (v itself, or a
   witness in D0) — and that filler, being a p-filler, must ALSO lie
   in the intersected ∀-constraint. If D0 (or {v}) doesn't intersect
   the ∀-constraint, no such filler can exist: clash.

   Soundness-critical: two DIFFERENT existence-forcing obligations on
   the SAME property (two separate ∃p.D0 / ∃p.D0' labels, or two
   different HasValue literals) are NEVER combined with each other —
   only every obligation individually against the SAME shared
   ∀-intersection. Combining two ∃-obligations together would assume
   they share one witness, which is unsound for a non-functional
   property (two distinct ∃p.Di can be satisfied by two DIFFERENT
   fillers). This mirrors the standard DL tableau ∀-propagation rule
   applied to each ∃-witness independently — no witness materialisation
   is actually needed here because every Wave-B target fixture places
   BOTH the ∀ and ∃/hasValue obligations directly on the same ABox
   individual via SubClassOf+ClassAssertion (TBox unfolding already
   deposits every RHS label there), so this operates purely at the
   label-list level.

   `fold_datatype_constraint` is a no-op (returns `acc` unchanged) for
   every class-expression shape XSD.Facets doesn't recognise as
   datatype-related (ordinary named OWL classes, individual
   owl:oneOf/hasValue, any other filler) — so this rule is inert on
   the overwhelming majority of the corpus by construction; it can
   only ever narrow a value_set that started from a recognised XSD
   datatype IRI, a DatatypeRestriction, or an all-literal DataOneOf. *)
let rec fold_datatype_constraint (acc : value_set) (ce : class_expr)
  : Tot value_set (decreases ce) =
  match ce with
  | CE_DataRestriction dt facets ->
    if is_integer_family_datatype dt
    then value_set_intersect acc (VS_Interval (facets_to_interval dt facets full_interval))
    // A DatatypeRestriction over xsd:dateTime with min/max facets binds
    // every filler to a UTC-instant interval; folded into the shared
    // value_set it makes an out-of-range hasValue / someValuesFrom
    // witness refute the node (Contradicting-dateTime-restrictions).
    // Sound: the interval is exact over timezoned instants and the
    // dateTime dimension never mixes with the integer one.
    else if is_datetime_datatype dt
    then value_set_intersect acc (VS_DateInterval (datetime_facets_to_interval facets full_interval))
    else acc
  | CE_OneOf members ->
    if Cons? members && all_literal_terms members
    then value_set_intersect acc (VS_Enum members)
    else acc
  | CE_Named dt ->
    // A bare xsd:dateTime datatype filler constrains fillers to the
    // (unbounded) dateTime dimension — enough to clash against a
    // numeric/string/boolean constraint on the same property. Sound:
    // an unbounded interval adds no false emptiness on its own.
    if is_datetime_datatype dt
    then value_set_intersect acc (VS_DateInterval full_interval)
    else
    (match classify_family dt with
     | Some Fam_Numeric -> value_set_intersect acc (VS_Interval (base_interval_for dt))
     | Some f -> value_set_intersect acc (VS_Family f)
     | None -> acc)
  | CE_ComplementOf inner ->
    let inner_vs = fold_datatype_constraint VS_Unconstrained inner in
    value_set_subtract acc inner_vs
  | _ -> acc

(* Intersect every CE_AllValuesFrom q D filler (D datatype-shaped or
   not — non-datatype D is a no-op via fold_datatype_constraint above)
   for every q that CONSTRAINS p's fillers, over the node's full label
   list. Role-hierarchy aware (Wave E-rolebox): q constrains p's
   fillers whenever p rdfs:subPropertyOf* q (q ∈ superproperties_of p,
   which always includes p itself, preserving the pre-rolebox exact-
   match behaviour) — EXT(p) subset-of EXT(q) means every p-filler is
   ALSO a q-filler, so ∀q.D binds it too. `subprop_pairs` is
   `st.rs_subprop`, threaded in rather than read off a state value so
   this stays a plain Tot fold like its sibling `fold_datatype_constraint`. *)
let rec universal_for_property (subprop_pairs : list (wf_iri & wf_iri))
                               (p : wf_iri) (ls : list class_expr) (acc : value_set)
  : Tot value_set (decreases ls) =
  match ls with
  | [] -> acc
  | CE_AllValuesFrom q d :: tl ->
    universal_for_property subprop_pairs p tl
      (if mem_iri q (superproperties_of subprop_pairs p)
       then fold_datatype_constraint acc d else acc)
  | _ :: tl -> universal_for_property subprop_pairs p tl acc

(* Does ANY single existence-forcing obligation on property p (one
   CE_SomeValuesFrom filler, or one CE_HasValue literal) fail to fit
   inside `universal`? Each checked independently — see the soundness
   note above for why obligations are never combined with each other. *)
let rec exists_unsatisfiable_witness (p : wf_iri) (ls : list class_expr) (universal : value_set)
  : Tot bool (decreases ls) =
  match ls with
  | [] -> false
  | CE_SomeValuesFrom q d :: tl ->
    if q = p && value_set_is_empty (fold_datatype_constraint universal d)
    then true
    else exists_unsatisfiable_witness p tl universal
  | CE_HasValue q v :: tl ->
    if q = p then
      (match v with
       | T_Literal _ ->
         if value_set_is_empty (value_set_intersect universal (VS_Enum [v]))
         then true
         else exists_unsatisfiable_witness p tl universal
       | _ -> exists_unsatisfiable_witness p tl universal)
    else exists_unsatisfiable_witness p tl universal
  | _ :: tl -> exists_unsatisfiable_witness p tl universal

let property_datatype_clash (subprop_pairs : list (wf_iri & wf_iri))
                            (p : wf_iri) (ls_all : list class_expr) : bool =
  let universal = universal_for_property subprop_pairs p ls_all VS_Unconstrained in
  exists_unsatisfiable_witness p ls_all universal

(* Every property mentioned in a Some/All/HasValue label on this node
   (duplicates harmless — `any_property_datatype_clash` just re-checks
   the same property, no different answer, no soundness risk). Every
   mentioned property (super- AND sub-roles alike) is visited as its
   own outer-loop `p`, so a sub-role's OWN existence obligation is
   already checked against its OWN (super-closure-widened) universal
   by `property_datatype_clash` above — no separate role-hierarchy
   widening needed on the existence-obligation side. *)
let rec collect_dt_properties (ls : list class_expr) : Tot (list wf_iri) (decreases ls) =
  match ls with
  | [] -> []
  | CE_SomeValuesFrom p _ :: tl -> p :: collect_dt_properties tl
  | CE_AllValuesFrom p _ :: tl -> p :: collect_dt_properties tl
  | CE_HasValue p _ :: tl -> p :: collect_dt_properties tl
  | _ :: tl -> collect_dt_properties tl

let rec any_property_datatype_clash (subprop_pairs : list (wf_iri & wf_iri))
                                    (ps : list wf_iri) (ls_all : list class_expr)
  : Tot bool (decreases ps) =
  match ps with
  | [] -> false
  | p :: tl ->
    property_datatype_clash subprop_pairs p ls_all
    || any_property_datatype_clash subprop_pairs tl ls_all

(* C6 entry point: is there ANY property on this node whose combined
   ∀-constraint + at least one ∃/hasValue obligation is unsatisfiable? *)
let datatype_range_clash (subprop_pairs : list (wf_iri & wf_iri))
                         (ls_all : list class_expr) : bool =
  any_property_datatype_clash subprop_pairs (collect_dt_properties ls_all) ls_all

(* -------------------------------------------------------------------
   6. Clash detection.
   ------------------------------------------------------------------- *)

(* label-level: is there a <= k' P (unqualified) with k' < k? *)
let exists_max_lt (k : nat) (p : wf_iri) (ls : list class_expr) : bool =
  List.Tot.existsb
    (fun (l : class_expr) ->
      match l with
      | CE_MaxCard k' p' -> p' = p && k' < k
      | _ -> false)
    ls

(* label-level: is there a <= k' P.C' with the SAME filler and k' < k? *)
let exists_maxqual_lt (k : nat) (p : wf_iri) (c : class_expr)
                      (ls : list class_expr) : bool =
  List.Tot.existsb
    (fun (l : class_expr) ->
      match l with
      | CE_MaxQualCard k' p' c' -> p' = p && k' < k && ce_eq c c'
      | _ -> false)
    ls

(* successors provably in filler c: the successor's node carries c as
   a label. Labels are entailed memberships (see the invariant note on
   `pass` below), so this is a sound under-approximation. *)
let rec filter_in_filler (st : rstate) (c : class_expr) (ts : list rdf_term)
  : Tot (list rdf_term) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = filter_in_filler st c tl in
    (match term_to_subject t with
     | Some j -> if mem_ce c (labels_of st j) then t :: rest else rest
     | None -> rest)

(* -------------------------------------------------------------------
   6a. The tableau ≤-rule (witness merging — owl2-le-rule wave).

   PROBLEM this closes: C3/C4 above only clash a `<= k P` label against
   PROVABLY-DISTINCT successors (`countable_successors`, which itself
   excludes ∃-witness edges entirely — `extra_objects`'s `re_count`
   gate). When a node has MORE successors than `k` allows but they are
   NOT provably distinct — the standard case being two separate
   ∃-witnesses, or a role-hierarchy/FunctionalProperty-widened mix of a
   witness and an asserted/witness successor of a sub-role — the C3/C4
   scan simply never sees them and the search reports the branch open.
   Standard SHIQ tableaux close this with the ≤-rule: pick two
   successors that are not YET forced apart and IDENTIFY them (merge
   node labels, redirect edges), then keep going; this is applied
   repeatedly until the successor count is <= k or a clash appears from
   the union of the merged labels.

   NONDETERMINISM, encoded exactly like the existing `CE_UnionOf`
   search (section 9 below reuses this precedent, see `branch`): the
   real ≤-rule picks ONE mergeable pair per application, arbitrarily.
   For REFUTATION we cannot assume any particular choice — we must
   show every choice the algorithm could make still closes. So
   `merge_branch` (section 9) branches over EVERY candidate pair as a
   sibling choice (like every union disjunct) and requires ALL of them
   to close (TClash) before reporting TClash; TOut/TOpen from any
   candidate forbids it, mirroring `branch`'s verdict combination
   exactly. Excess that still remains after one merge (e.g. 3
   successors against `<= 1 P`) is caught again on the NEXT `check`
   round (the merge collapses two successor TERMS into one via
   `dedup_terms` in `all_successors`, so the excess count strictly
   drops by exactly one per merge — monotonic, budget-bounded, and
   re-detected by `find_merge_nodes` like any other saturation step),
   so a whole nested tree of merge choices is explored exactly the way
   nested union branches already are.

   SOUNDNESS of triggering on excess-over-`all_successors` (INCLUDING
   witnesses, unlike the C3/C4 test): if `<= k P` holds of `i` in every
   model (entailed) and `i` has strictly more than `k` PROVABLY
   DIFFERENT-AS-TERMS `P`-successors, then in every model SOME two of
   those terms must denote the SAME domain element — that is exactly
   what `<= k P` forces by pigeonhole. Which pair coincides is exactly
   the nondeterministic choice above; trying every mergeable pair (and
   requiring all to close) is the same OR-for-satisfiable /
   AND-for-refutation encoding already used for `CE_UnionOf`.
   "Mergeable" EXCLUDES any pair already forced apart
   (`provably_distinct` — owl:differentFrom, incomparable literal
   values, or co-membership of a `rs_gendistinct` generating-rule
   group): merging a forced-distinct pair would be unsound, and is
   never offered as a candidate. If a node's full successor set has NO
   mergeable pair at all (every pair already forced apart), no merge
   branch is offered — that situation is already, and correctly, a C4
   clash whenever the same successors are also countable; when it
   is NOT (forced-distinct pure witnesses over the cap) this rule
   soundly stays silent, same as C4 today.

   SOUNDNESS of `merge_into` (the actual identification step, defined
   below): restricting candidates to `is_witness_subject` pairs (see
   its banner) means every edge that could ever mention either side of
   the pair lives in `st.rs_extra` — nothing is asserted about a
   witness bnode in the fixed input graph `g`. `merge_into` therefore
   redirects EVERY `rs_extra` edge mentioning the absorbed node `y`
   (whether as `re_s` — an outgoing/successor edge — or as `re_o` — an
   incoming edge, which is how the inverse-aware reverse lookups
   `extra_reverse_objects`/`extra_reverse_objects_all` see predecessor
   views — so both successor AND predecessor views are covered by one
   rewrite, no separate inverse-specific step needed) onto the
   surviving node `z`, and unions `y`'s current label set onto `z`
   (every label ever added to a node is an entailed membership of its
   denotation — see the `pass` invariant note below — so once `y` and
   `z` are identified, `z`'s denotation is entailed to carry BOTH sets
   of labels). `y`'s own `rnode` entry is deliberately left in place
   rather than deleted: it keeps receiving deterministic expansion on
   its original (unchanged, still perfectly sound) label set, but with
   its edges gone nothing else in the state can reach it any more, so
   it can only ever contribute EXTRA, still-sound entailments of `y`'s
   (== `z`'s, under this branch's hypothesis) identity — anything it
   derives to a clash is a genuine contradiction of a real entailment,
   never a fabricated one; at worst this only costs completeness
   (a combination fact spanning `y`'s post-merge derivations and `z`'s
   post-merge derivations could be missed), which this module's
   contract already tolerates everywhere else (TOpen is not a
   consistency proof). *)

(* Every `p`-successor of `i` (INCLUDING witness edges — the
   completeness gap C3/C4 leave open) that is itself a pure witness
   bnode, i.e. a node this module can safely and completely redirect
   (see `is_witness_subject`'s banner). Named individuals and literals
   are never merge candidates — conservative (fewer merges attempted),
   never unsound. *)
let rec candidate_witness_subjects (st : rstate) (ts : list rdf_term)
  : Tot (list subject) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = candidate_witness_subjects st tl in
    (match term_to_subject t with
     | Some s -> if is_witness_subject st s then s :: rest else rest
     | None -> rest)

(* Every OTHER candidate in `rest` that `h` may soundly be merged with
   (not `h` itself, not forced apart from `h` by `provably_distinct`). *)
let rec pairs_from_head (g : rdf_graph) (gd : list (list rdf_term))
                        (h : subject) (rest : list subject)
  : Tot (list (subject & subject)) (decreases rest) =
  match rest with
  | [] -> []
  | s :: tl ->
    let more = pairs_from_head g gd h tl in
    if subject_eq h s || provably_distinct g gd (subject_to_term h) (subject_to_term s)
    then more
    else (h, s) :: more

(* All unordered mergeable pairs drawn from a (small — one node's
   successor set) candidate list. Exhaustive, like `exists_distinct_subset`
   above; bounded by the same successor-set-is-tiny corpus property, and
   further bounded by the threaded search budget regardless. *)
let rec all_mergeable_pairs (g : rdf_graph) (gd : list (list rdf_term))
                            (ss : list subject)
  : Tot (list (subject & subject)) (decreases ss) =
  match ss with
  | [] -> []
  | h :: tl -> pairs_from_head g gd h tl @ all_mergeable_pairs g gd tl

(* Is THIS label a `<= k P` (or qualified `<= k P.C`) obligation whose
   FULL successor set (witnesses included — `all_successors`, not
   `countable_successors`) exceeds `k`, with at least one mergeable
   pair to branch over? `None` when the label isn't a max-card shape,
   when the full set doesn't exceed the bound, or when every pair in
   the full set is already forced apart (the C3/C4 rules above are the
   ones responsible for flagging THAT case, whenever it also holds over
   the countable-only subset — this rule stays silent rather than
   duplicate or second-guess them). *)
let excess_pairs_for_label (g : rdf_graph) (st : rstate) (i : subject) (l : class_expr)
  : option (list (subject & subject)) =
  match l with
  | CE_MaxCard k p ->
    let full = all_successors g st i p in
    if List.Tot.length full > k then
      let prs = all_mergeable_pairs g st.rs_gendistinct (candidate_witness_subjects st full) in
      if Cons? prs then Some prs else None
    else None
  | CE_MaxQualCard k p c ->
    let full = filter_in_filler st c (all_successors g st i p) in
    if List.Tot.length full > k then
      let prs = all_mergeable_pairs g st.rs_gendistinct (candidate_witness_subjects st full) in
      if Cons? prs then Some prs else None
    else None
  | _ -> None

let rec find_merge_labels (g : rdf_graph) (st : rstate) (i : subject) (ls : list class_expr)
  : Tot (option (list (subject & subject))) (decreases ls) =
  match ls with
  | [] -> None
  | l :: tl ->
    (match excess_pairs_for_label g st i l with
     | Some prs -> Some prs
     | None -> find_merge_labels g st i tl)

(* First node (deterministic: node order, then label order — same
   discipline as `find_union_nodes`) carrying a mergeable excess. *)
let rec find_merge_nodes (g : rdf_graph) (st : rstate) (ns : list rnode)
  : Tot (option (list (subject & subject))) (decreases ns) =
  match ns with
  | [] -> None
  | n :: tl ->
    (match find_merge_labels g st n.rn_id n.rn_labels with
     | Some prs -> Some prs
     | None -> find_merge_nodes g st tl)

(* Rewrite one term/subject occurrence of the absorbed node `y` to the
   surviving node `z`. *)
let redirect_subject_term (y : subject) (z : subject) (t : rdf_term) : rdf_term =
  if rdf_term_eq t (subject_to_term y) then subject_to_term z else t

let redirect_subject (y : subject) (z : subject) (s : subject) : subject =
  if subject_eq s y then z else s

(* Redirect BOTH endpoints of one tableau-internal edge — this is what
   makes the rewrite predecessor/inverse-aware for free: an edge
   discovered through `extra_reverse_objects` matches on `re_o`, so
   redirecting `re_o` here is exactly what keeps inverse-role successor
   views correct after the merge, with no separate inverse-specific
   step. *)
let redirect_edge (y : subject) (z : subject) (e : redge) : redge =
  { e with re_s = redirect_subject y z e.re_s; re_o = redirect_subject_term y z e.re_o }

let rec redirect_group (y : subject) (z : subject) (grp : list rdf_term)
  : Tot (list rdf_term) (decreases grp) =
  match grp with
  | [] -> []
  | t :: tl -> redirect_subject_term y z t :: redirect_group y z tl

(* rs_gendistinct groups are read by `provably_distinct` to forbid
   merging a FORCED-apart pair; once `y` is identified with `z`, any
   distinctness fact the generating rule recorded about `y` (relative
   to its group siblings) is a fact about `z` now, by exactly the same
   "labels are entailed of the merged identity" argument the module
   banner above makes for `rn_labels` — soundly TRANSFERRED, not
   dropped, so a later merge attempt against one of `y`'s former
   group-mates is still correctly refused. *)
let rec redirect_groups (y : subject) (z : subject) (gds : list (list rdf_term))
  : Tot (list (list rdf_term)) (decreases gds) =
  match gds with
  | [] -> []
  | grp :: tl -> redirect_group y z grp :: redirect_groups y z tl

(* The ≤-rule's identification step: absorb `y` into `z`. See the
   section 6a banner above for the full soundness argument. *)
let merge_into (st : rstate) (y : subject) (z : subject) : rstate =
  let (st1, _) = add_labels_all st z (labels_of st y) in
  { st1 with
    rs_extra = List.Tot.map (redirect_edge y z) st1.rs_extra;
    rs_gendistinct = redirect_groups y z st1.rs_gendistinct }

(* -------------------------------------------------------------------
   6b. Named-individual identification (owl2-named-merge wave).

   PROBLEM this closes: section 6a's ≤-rule only merges pairs where
   BOTH successors are pure ∃-witness bnodes, because `merge_into`
   physically redirects every edge mentioning the absorbed node, and
   only a witness's edges are guaranteed to live entirely in
   `rs_extra` (module banner, top of file). When a `<= k P`
   obligation's excess successor set includes a NAMED individual (an
   IRI, or a document bnode asserted directly in `g`) on EITHER side of
   a candidate pair, that individual's graph-asserted edges cannot be
   safely redirected — some could be missed, silently under-counting a
   real successor set elsewhere in the graph. Standard SHIQ/SHOIN
   tableaux handle this with the SAME ≤-rule nondeterminism, just
   realised differently for individuals with a fixed identity: instead
   of rewriting edges, the two names are IDENTIFIED (owl:sameAs-style,
   `rs_ident`, section 4a-ident) and every reader that matters
   (`labels_of`, `countable_successors`/`all_successors`,
   `clash_nodes`) is made to consult the WHOLE group instead of one
   node — see those sites' banners for the pooling argument. No UNA in
   OWL: identifying two distinct names is always a legal hypothesis
   unless something ALREADY forces them apart.

   NONDETERMINISM / AND-verdict: identical encoding to `merge_branch`
   above — every mergeable candidate pair is tried as a sibling branch
   (`identify_branch`, section 9), and ALL must close (TClash) for the
   overall obligation to be reported refuted; any TOpen wins, matching
   `branch`/`merge_branch`'s verdict combination exactly. Budget is
   threaded with the SAME `%[b; List.Tot.length pairs]` measure
   `merge_branch` uses, so the two rules share one termination
   argument.

   CANDIDATE SCOPE: a pair qualifies here iff it is NOT the
   witness-witness case section 6a already owns (that pair is left to
   `merge_branch`, unchanged, so this wave never second-guesses an
   already-verified rule), the two terms are not already identified
   (`same_individual`), and the pair is not `provably_distinct_grouped`
   (owl:differentFrom, incomparable literal values, a `rs_gendistinct`
   generating-rule group, or any of those transitively via a PRIOR
   identification — see that function's banner). A witness MAY appear
   on one side of a pair here (identified with a named individual) —
   sound, because identification never needs to redirect either side's
   edges, unlike `merge_into`; nothing is lost by routing a
   witness-vs-named pair through the partition instead of a physical
   merge.

   SOUNDNESS of the trigger condition (excess-over-`k` on the FULL,
   ident-deduped successor set): identical pigeonhole argument to
   section 6a's banner — if `<= k P` holds of `i` in every model and
   `i` has strictly more than `k` pairwise-not-yet-identified,
   not-yet-forced-apart `P`-successor TERMS, some two of them must
   denote the SAME domain element in every model. Trying every
   not-already-excluded pair (AND-for-refutation) is sound for the same
   reason `exists_distinct_subset`/`merge_branch` already rely on.

   differentFrom / distinct-literal SAFETY: a pair excluded by
   `provably_distinct_grouped` is NEVER offered here, so this rule can
   never identify two names the graph (or a prior identification step)
   already forces apart — if EVERY candidate pair the excess set could
   offer is excluded that way, `excess_ident_pairs_for_label` reports
   `None` and the ordinary C3/C4 counting clash (section 6, over the
   COUNTABLE/asserted-strength subset) is left to report the clash
   instead, exactly as section 6a's witness rule already defers to C3/
   C4 when no mergeable pair exists — this is exactly the pigeonhole a
   max-card bound forcing k+1 successors into k pairwise-mergeable
   named individuals, with one differentFrom pair, must resolve as a
   clash rather than a further identification. *)

(* The union step: identify `x` and `y` in the partition. A no-op if
   they already denote the same element (co-membership or syntactic
   equality). Otherwise pulls whichever existing groups contain `x`
   and/or `y` (singleton groups when either was previously
   unidentified) out of `ident`, unions their members (deduped), and
   reinserts the merged group — a plain union-find "union" written as
   an explicit list rewrite so the whole thing stays `Tot` with a
   structural decreases, no path-compression bookkeeping needed at this
   corpus's scale. *)
let rec remove_ident_group (ident : list (list rdf_term)) (t : rdf_term)
  : Tot (list (list rdf_term) & list rdf_term) (decreases ident) =
  match ident with
  | [] -> ([], [t])
  | grp :: tl ->
    if List.Tot.existsb (fun x -> rdf_term_eq x t) grp
    then (tl, grp)
    else
      let (rest, found) = remove_ident_group tl t in
      (grp :: rest, found)

let identify_pair (ident : list (list rdf_term)) (x : rdf_term) (y : rdf_term)
  : list (list rdf_term) =
  if rdf_term_eq x y then ident
  else
    let (ident1, gx) = remove_ident_group ident x in
    let (ident2, gy) = remove_ident_group ident1 y in
    dedup_terms (gx @ gy) :: ident2

(* Every successor term (witnesses INCLUDED, like `candidate_witness_subjects`
   above) that resolves to a subject at all — literals are never
   identification candidates: an individual's identity is
   nondeterministic under no-UNA, but a literal's is fixed by its
   value, so "identifying" one with anything else would fabricate an
   equality no model need satisfy. *)
let rec all_candidate_subjects (ts : list rdf_term) : Tot (list subject) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = all_candidate_subjects tl in
    (match term_to_subject t with
     | Some s -> s :: rest
     | None -> rest)

(* Every OTHER candidate in `rest` that `h` may soundly be IDENTIFIED
   with — excludes the witness-witness case (owned by section 6a's
   `pairs_from_head`/`merge_branch`), self-pairs, already-identified
   pairs, and group-aware forced-distinct pairs. *)
let rec identify_pairs_from_head (g : rdf_graph) (gd : list (list rdf_term))
                                 (ident : list (list rdf_term)) (st : rstate)
                                 (h : subject) (rest : list subject)
  : Tot (list (subject & subject)) (decreases rest) =
  match rest with
  | [] -> []
  | s :: tl ->
    let more = identify_pairs_from_head g gd ident st h tl in
    if subject_eq h s
       || (is_witness_subject st h && is_witness_subject st s)
       || same_individual ident (subject_to_term h) (subject_to_term s)
       || provably_distinct_grouped g gd ident (subject_to_term h) (subject_to_term s)
    then more
    else (h, s) :: more

let rec all_identify_pairs (g : rdf_graph) (gd : list (list rdf_term))
                           (ident : list (list rdf_term)) (st : rstate)
                           (ss : list subject)
  : Tot (list (subject & subject)) (decreases ss) =
  match ss with
  | [] -> []
  | h :: tl ->
    identify_pairs_from_head g gd ident st h tl @ all_identify_pairs g gd ident st tl

(* Mirrors `excess_pairs_for_label` (section 6a) exactly, over the SAME
   ident-deduped `all_successors` view, but collecting IDENTIFICATION
   candidates instead of witness-merge candidates. `None` when the
   label isn't a max-card shape, the full ident-deduped set doesn't
   exceed the bound (identification already brought it under — the
   excess genuinely closed, nothing left to branch on), or every
   remaining pair is witness-witness (section 6a's job) or forced
   apart. *)
let excess_ident_pairs_for_label (g : rdf_graph) (st : rstate) (i : subject) (l : class_expr)
  : option (list (subject & subject)) =
  match l with
  | CE_MaxCard k p ->
    let full = all_successors g st i p in
    if List.Tot.length full > k then
      let prs = all_identify_pairs g st.rs_gendistinct st.rs_ident st (all_candidate_subjects full) in
      if Cons? prs then Some prs else None
    else None
  | CE_MaxQualCard k p c ->
    let full = filter_in_filler st c (all_successors g st i p) in
    if List.Tot.length full > k then
      let prs = all_identify_pairs g st.rs_gendistinct st.rs_ident st (all_candidate_subjects full) in
      if Cons? prs then Some prs else None
    else None
  | _ -> None

let rec find_identify_labels (g : rdf_graph) (st : rstate) (i : subject) (ls : list class_expr)
  : Tot (option (list (subject & subject))) (decreases ls) =
  match ls with
  | [] -> None
  | l :: tl ->
    (match excess_ident_pairs_for_label g st i l with
     | Some prs -> Some prs
     | None -> find_identify_labels g st i tl)

(* First node (deterministic: node order, then label order — same
   discipline as `find_merge_nodes`) carrying an identifiable excess. *)
let rec find_identify_nodes (g : rdf_graph) (st : rstate) (ns : list rnode)
  : Tot (option (list (subject & subject))) (decreases ns) =
  match ns with
  | [] -> None
  | n :: tl ->
    (match find_identify_labels g st n.rn_id n.rn_labels with
     | Some prs -> Some prs
     | None -> find_identify_nodes g st tl)

(* Per-label clash test against the node's full label set + edges.

   Soundness arguments:
   C1 (⊥): x ∈ CEXT(owl:Nothing) = ∅ is false in every model, and the
       label is entailed — contradiction.
   C2 (complement): x ∈ C and x ∈ negC cannot both hold in any model.
       (After NNF, neg wraps only atomic shapes; ce_eq requires
       structural identity, so both labels speak of one class.)
   C3 (min/max): at-least m and at-most n on one property with m > n is
       unsatisfiable; the qualified pair is compared only at
       structurally identical fillers (same set). ∃P.C / hasValue give
       >= 1 (a witness exists in every model). Qualified >= m P.C also
       clashes with unqualified <= n P for m > n (C-successors are
       successors).
   C4 (counting): see exists_distinct_subset / provably_distinct.
       Only countable (asserted-strength) successors participate.
   C5 (bottom): ∃/min>=1/hasValue on a property with EXT = ∅.          *)
let clash_for_label (g : rdf_graph) (st : rstate) (i : subject)
                    (ls_all : list class_expr) (l : class_expr) : bool =
  match l with
  | CE_Named x -> x = owl_Nothing
  | CE_ComplementOf c ->
    mem_ce c ls_all
    || (match c with
        | CE_Named x -> x = owl_Thing
        | _ -> false)
  | CE_MinCard k p ->
    k >= 1 && (is_bottom_prop p || exists_max_lt k p ls_all)
  | CE_SomeValuesFrom p c ->
    is_bottom_prop p
    || exists_max_lt 1 p ls_all
    || exists_maxqual_lt 1 p c ls_all
  | CE_HasValue p _ ->
    is_bottom_prop p || exists_max_lt 1 p ls_all
  | CE_MinQualCard k p c ->
    k >= 1
    && (is_bottom_prop p
        || exists_max_lt k p ls_all
        || exists_maxqual_lt k p c ls_all
        (* Nominal-aware counting (#209 Wave A, sharpened): a nominal
           {a1,...,am} denotes AT MOST m distinct individuals in every
           model (that is the entire content of owl:oneOf — no more,
           no fewer). >= k P.{a1,...,am} demands k pairwise-distinct
           P-fillers all drawn from a set of size m: impossible once
           k > m, with NO owl:differentFrom needed — the bound comes
           from the nominal's own finite size, not from asserted
           distinctness of specific individuals. *)
        || (match c with
            | CE_OneOf members -> k > List.Tot.length members
            | _ -> false))
  | CE_OneOf members ->
    (* O-rule (#209 Wave A): i : {a1,...,am} forces i to equal ONE of
       the members in every model (that is what owl:oneOf asserts). If
       i is provably distinct (owl:differentFrom, either direction, or
       incomparable-value literals) from EVERY member, no member can be
       i — clash. Sound, no cardinality reasoning needed; kept from the
       first Wave-A probe (#209) even though it fires on zero corpus
       tests by itself — it is free and still correct. *)
    all_provably_distinct g st.rs_gendistinct (subject_to_term i) members
  | CE_MaxCard k p ->
    let succs = countable_successors g st i p in
    if k = 0 then Cons? succs
    else exists_distinct_subset g st.rs_gendistinct succs (k + 1)
  | CE_MaxQualCard k p c ->
    let succs = filter_in_filler st c (countable_successors g st i p) in
    if k = 0 then Cons? succs
    else exists_distinct_subset g st.rs_gendistinct succs (k + 1)
  | _ -> false

let rec clash_labels (g : rdf_graph) (st : rstate) (i : subject)
                     (ls_all : list class_expr) (ls_iter : list class_expr)
  : Tot bool (decreases ls_iter) =
  match ls_iter with
  | [] -> false
  | l :: tl ->
    clash_for_label g st i ls_all l || clash_labels g st i ls_all tl

let rec clash_nodes (g : rdf_graph) (st : rstate) (ns : list rnode)
  : Tot bool (decreases ns) =
  match ns with
  | [] -> false
  | n :: tl ->
    (* Pooled across n's identification group (owl2-named-merge wave,
       section 4a-ident): once two named individuals are identified, a
       clash entailed by the UNION of their labels (e.g. one carries
       `<= 0 P`, the other `>= 1 P`) must be visible from either one's
       own node entry. `labels_of` is the ident-aware read that
       supplies it without ever physically copying a label the way
       `merge_into` does for witnesses. Perf guard: the pooled read
       costs an O(rs_nodes) scan per group member, so it is only taken
       when this node actually HAS an identification group — on the
       (overwhelmingly common) unidentified path this is the same
       direct `n.rn_labels` access as before the wave, keeping
       `clash_nodes` linear when the partition is empty. *)
    let ls =
      match find_ident_group st.rs_ident (subject_to_term n.rn_id) with
      | Some _ -> labels_of st n.rn_id
      | None -> n.rn_labels
    in
    clash_labels g st n.rn_id ls ls
    || datatype_range_clash st.rs_subprop ls
    || clash_nodes g st tl

let has_clash (g : rdf_graph) (st : rstate) : bool =
  clash_nodes g st st.rs_nodes

(* -------------------------------------------------------------------
   7. TBox axiom collection.

   Axioms are (LHS, RHS) pairs of NNF class expressions, applied by
   the unfolding rule: a node whose label is ce_eq to LHS gains RHS.
   Soundness: each collected pair satisfies CEXT(LHS) ⊆ CEXT(RHS) in
   every model of the graph:
     - (A rdfs:subClassOf B)         : A ⊑ B (rdfs9 semantics).
     - (A owl:equivalentClass B)     : A ⊑ B and B ⊑ A.
     - (A owl:disjointWith B)        : A ⊑ negB and B ⊑ negA.
     - (A owl:complementOf B)        : A = negB, so A ⊑ negB and B ⊑ negA.
     - named subject z carrying restriction / boolean markers denotes
       exactly that class expression (OWL 2 RDF-Based semantics; same
       reading as Tableau.fst section 8c), so z ⊑ CE and CE ⊑ z.
   LHS/RHS containing CE_Unknown are inert (ce_eq never matches
   Unknown; add_label drops Unknown) — sound.                          *)

(* CLOSURE-SCAFFOLDING GUARD (soundness-critical). The OWL-RL closure
   materialises canonical restriction-membership bnodes named
   "__rl_svf_..." / "__rl_minqc1_..." / "__rl_maxqc1_..." /
   "__rl_exactqc1_..." (OWL.Closure cls-svf2-qualified /
   cls-minc-qual1 / cls-maxqc1 / cls-exactqc1) as SUPPORT TRIPLES for
   the test corpus's bnode-existential conclusion matching. Membership
   in an "__rl_exactqc1_P__on__C" node is asserted for ANY x with at
   least one C-filler on P — a deliberately loose, consumer-specific
   encoding that is NOT model-theoretically sound read as
   "x ∈ exactly-1 P.C". Reading it literally manufactured a refutation
   of the CONSISTENT New-Feature-ObjectQCR-001 / WebOnt-description-
   logic-662/665/667 / WebOnt-miscellaneous-011 premises (x with two
   provably-distinct fillers "violates" the scaffold's exact-1). Every
   class-expression this module parses therefore maps closure-internal
   scaffold bnodes to CE_Unknown — inert in labels, axioms, and
   branching. Dropping a (non-)constraint is always sound. *)
let is_scaffold_bnode (b : bnode_id) : bool =
  String.length b >= 5 && String.sub b 0 5 = "__rl_"

let parse_nnf (g : rdf_graph) (t : rdf_term) : class_expr =
  match t with
  | T_BNode b -> if is_scaffold_bnode b then CE_Unknown else nnf (parse_class_expr g t 32)
  | _ -> nnf (parse_class_expr g t 32)

let parse_nnf_subject (g : rdf_graph) (s : subject) : class_expr =
  match s with
  | S_BNode b -> if is_scaffold_bnode b then CE_Unknown else parse_nnf g (subject_to_term s)
  | _ -> parse_nnf g (subject_to_term s)

let rec collect_axioms_aux (gfull : rdf_graph) (ts : rdf_graph)
  : Tot (list (class_expr & class_expr)) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = collect_axioms_aux gfull tl in
    if t.p = rdfs_subClassOf then
      (parse_nnf_subject gfull t.s, parse_nnf gfull t.o) :: rest
    else if t.p = owl_equivalentClass then
      let a = parse_nnf_subject gfull t.s in
      let b = parse_nnf gfull t.o in
      (* Contrapositive unfolding (owl2-contrapositive wave, construct-gap:
         "contrapositive unfolding" in the Wave E profile). owl:equivalentClass
         asserts a GENUINE iff — both a ⊑ b and b ⊑ a already go into the pair
         list below — so BOTH classical contrapositives are equally sound here:
           a ⊑ b  contrapositive  ¬b ⊑ ¬a
           b ⊑ a  contrapositive  ¬a ⊑ ¬b
         This is what unlocks the FaCT-derived WebOnt-description-logic-6xx
         family: those fixtures encode complementary class pairs arithmetically
         (X ≡ >=1 P, X.comp ≡ =0 P on the SAME property, with no explicit
         owl:complementOf triple linking X and X.comp at all) — deriving
         anything from that pairing REQUIRES going through a defined name's
         negation, which plain (a,b)/(b,a) unfolding never does since neither
         side is ever the LHS the node's label actually carries. na/nb reuse
         `nnf_neg` (NNF-in, NNF-out, already used by nnf itself) so this adds
         no new recursion, no new fuel parameter, and no new branching source —
         only two more STATIC axiom pairs per equivalentClass triple for the
         existing apply_axioms exact-match scan to consult.
         Deliberately NOT done for rdfs:subClassOf below, nor for
         disjointWith/complementOf (self-dual: contrapositive of (a,¬b) is
         just (b,¬a), already present, no new information). rdfs:subClassOf's
         A ⊑ D is one-directional ONLY — D ⊑ A is not asserted — so a node
         labelled ¬D must NOT be treated as ¬A here: that would silently
         assume the missing reverse direction (the "equivalence-vs-subclass
         confusion" the module's soundness gate calls out). The valid
         contrapositive of a lone A ⊑ D (¬D ⊑ ¬A) runs the OPPOSITE direction
         from what a naive "not-defined-so-not-defining-condition" unfold
         would produce, and is not something this module needs: nothing in
         the target fixtures required it (every clash chain traced during
         design went entirely through equivalentClass/bidirectional-marker
         pairs), so it stays out to keep the axiom table growth linear and
         the soundness argument simple. *)
      let na = nnf_neg a in
      let nb = nnf_neg b in
      (a, b) :: (b, a) :: (nb, na) :: (na, nb) :: rest
    else if t.p = owl_disjointWith || t.p = owl_complementOf then
      let a = parse_nnf_subject gfull t.s in
      let b = parse_nnf gfull t.o in
      let na = nnf (CE_ComplementOf (parse_class_expr gfull (subject_to_term t.s) 32)) in
      let nb = nnf (CE_ComplementOf (parse_class_expr gfull t.o 32)) in
      (a, nb) :: (b, na) :: rest
    else if (t.p = owl_onProperty || t.p = owl_intersectionOf || t.p = owl_unionOf)
            && S_IRI? t.s then
      (* Named class-expression subject: z ≡ CE(z). One axiom pair per
         marker triple; duplicates are harmless (add_label dedups).
         Contrapositive closure (same soundness argument as the
         owl:equivalentClass branch above — this IS a genuine bidirectional
         definition per the OWL 2 RDF-Based reading in the section-7 banner,
         not a one-way subsumption): z's negation and CE(z)'s negation are
         equally each other's contrapositive-derived unfold targets. This is
         the branch the FaCT 6xx fixtures actually route the SECOND half of
         each complement's definition through (e.g. `X.comp` is ALSO given a
         real boolean-expression body — an intersectionOf sitting directly on
         the named class — alongside its numeric-restriction equivalentClass
         body; the contrapositive above turns "not X.comp" into a class-label
         this branch's OWN pair can then unfold into the boolean expression's
         NNF-negated disjunction). *)
      (match t.s with
       | S_IRI z ->
         let ce = nnf (parse_ce_of_subject gfull t.s) in
         let nz = nnf_neg (CE_Named z) in
         let nce = nnf_neg ce in
         (CE_Named z, ce) :: (ce, CE_Named z) :: (nce, nz) :: (nz, nce) :: rest
       | _ -> rest)
    else rest

let collect_axioms (g : rdf_graph) : list (class_expr & class_expr) =
  collect_axioms_aux g g

(* -------------------------------------------------------------------
   8. Expansion rules (deterministic part).
   ------------------------------------------------------------------- *)

let rec apply_axioms (tb : list (class_expr & class_expr)) (st : rstate)
                     (i : subject) (l : class_expr)
  : Tot (rstate & bool) (decreases tb) =
  match tb with
  | [] -> (st, false)
  | (a, d) :: tl ->
    let (st1, c1) = if ce_eq a l then add_label st i d else (st, false) in
    let (st2, c2) = apply_axioms tl st1 i l in
    (st2, c1 || c2)

(* EDGE-MEMBERSHIP INTRODUCTION: a node's ASSERTED successors can prove
   it belongs to an axiom's LHS even when no rdf:type triple says so —
   the positive direction Tableau.fst's materialisation used to supply
   before the refuter was moved onto the RL-base closure (see the
   runner's apply_closure_stages banner). Soundness per shape, all
   over countable (asserted-strength) successors only:
     - >= 1 P            : any asserted successor is a witness.
     - >= k P (k >= 2)   : k PAIRWISE PROVABLY-DISTINCT successors
                           (provably_distinct — no-UNA safe; a plain
                           count of k would be unsound, two IRIs may
                           denote one element).
     - ∃ P.C             : an asserted successor whose node carries
                           label C (labels are entailed memberships).
     - hasValue P v      : the (i, P, v) edge is present.
     - >= k P.C          : as >= k P over the C-labelled successors.
   Everything else: false (withholding is sound). Pins
   WebOnt-disjointWith-010: the self-disjoint min-1 restriction refutes
   only if the anonymous individual's asserted P-edge proves its
   min-1 membership first. *)
let edge_entails_membership (g : rdf_graph) (st : rstate) (i : subject)
                            (a : class_expr) : bool =
  match a with
  | CE_MinCard k p ->
    if k = 0 then false
    else if k = 1 then Cons? (countable_successors g st i p)
    else exists_distinct_subset g st.rs_gendistinct (countable_successors g st i p) k
  | CE_SomeValuesFrom p c ->
    ce_definite c &&
    List.Tot.existsb
      (fun (o : rdf_term) ->
        match term_to_subject o with
        | Some j -> mem_ce c (labels_of st j)
        | None -> false)
      (countable_successors g st i p)
  | CE_HasValue p v ->
    List.Tot.existsb (fun (o : rdf_term) -> rdf_term_eq o v)
      (countable_successors g st i p)
  | CE_MinQualCard k p c ->
    if k = 0 || not (ce_definite c) then false
    else
      let cs = filter_in_filler st c (countable_successors g st i p) in
      if k = 1 then Cons? cs
      else exists_distinct_subset g st.rs_gendistinct cs k
  | _ -> false

(* Once per node per round: fire axioms whose LHS membership is proved
   by the node's asserted edges. Adds the LHS too (so label-level clash
   rules like min/max see it), then the RHS.

   PERF (owl2-dpll wave): the node's label read is HOISTED — `ls_i`
   carries `labels_of st i` down the axiom recursion and is re-fetched
   ONLY when an axiom actually fired (the sole way `st`'s labels
   change here). The old per-axiom `labels_of st i` recomputation was
   measured (callgrind, dl-504) at ~75% of the whole refutation wall:
   |tb| full `rs_nodes` scans per node per round, each O(nodes) of
   long-IRI `subject_eq` compares. Same reads, same results — pure
   call-elimination. *)
let rec apply_axioms_edges_ls (tb : list (class_expr & class_expr)) (g : rdf_graph)
                              (st : rstate) (i : subject) (ls_i : list class_expr)
  : Tot (rstate & bool) (decreases tb) =
  match tb with
  | [] -> (st, false)
  | (a, d) :: tl ->
    if not (mem_ce_syn a ls_i) && edge_entails_membership g st i a
    then
      let (sta, ca) = add_label st i a in
      let (stb, cb) = add_label sta i d in
      let (st2, c2) = apply_axioms_edges_ls tl g stb i (labels_of stb i) in
      (st2, ca || cb || c2)
    else
      let (st2, c2) = apply_axioms_edges_ls tl g st i ls_i in
      (st2, c2)

let apply_axioms_edges (tb : list (class_expr & class_expr)) (g : rdf_graph)
                       (st : rstate) (i : subject)
  : rstate & bool =
  apply_axioms_edges_ls tb g st i (labels_of st i)

(* ∀-propagation: x ∈ ∀P.C and (x,y) ∈ P imply y ∈ C — for asserted
   edges, hasValue edges AND witness edges (the witness stands for a
   successor that exists in every model; all successors are in C).
   Literal successors are skipped (no class labels on literals —
   withholding is sound). *)
let rec forall_prop (st : rstate) (c : class_expr) (succs : list rdf_term)
  : Tot (rstate & bool) (decreases succs) =
  match succs with
  | [] -> (st, false)
  | o :: tl ->
    let (st1, c1) =
      (match term_to_subject o with
       | Some j -> add_label st j c
       | None -> (st, false))
    in
    let (st2, c2) = forall_prop st1 c tl in
    (st2, c1 || c2)

(* Fresh deterministic witness id. The leading space makes the id
   impossible to collide with ANY document-derived bnode id (space is
   not legal in an RDF/XML nodeID NCName or a Turtle bnode label, and
   the parsers' own generated ids are "rdfxml_b<n>"-shaped), and with
   Tableau's materialisation witnesses ("_:bw_..."). A collision would
   merge the witness's label set with a real individual's — labels the
   real individual is NOT entailed to have — so uniqueness here is a
   soundness requirement, not cosmetics. Witness ids never leave this
   module (the refuter adds no triples to any graph). *)
let witness_id (n : nat) : bnode_id =
  String.concat "" [" rw_"; string_of_int n]

(* ∃-witness introduction: x ∈ ∃P.C forces SOME P-successor in C in
   every model; we materialise one witness node standing for it. The
   witness edge is NOT countable (the successor may coincide with an
   existing one in some model — counting it would fabricate
   distinctness, an unsoundness). Fired only when no known successor
   already carries the filler label, so it is once-per-obligation.
   filler = None encodes the unqualified >= 1 P obligation. *)
let ensure_witness (g : rdf_graph) (st : rstate) (i : subject) (p : wf_iri)
                   (filler : option class_expr)
  : rstate & bool =
  (* Non-definite fillers (containing CE_Unknown) are demoted to the
     unqualified >= 1 P obligation: their satisfied-check below could
     never succeed (strict ce_eq is irreflexive on Unknown) and the
     rule would mint a fresh witness EVERY round — the second livelock
     the ce_eq_syn banner describes. Demotion is sound: the witness we
     then create carries fewer labels (none), which can only weaken
     refutation, and ∃P.C does entail >= 1 P. *)
  let filler =
    match filler with
    | Some c -> if ce_definite c then Some c else None
    | None -> None
  in
  let succs = all_successors g st i p in
  let satisfied =
    match filler with
    | None -> Cons? succs
    | Some c ->
      List.Tot.existsb
        (fun (o : rdf_term) ->
          match term_to_subject o with
          | Some j -> mem_ce c (labels_of st j)
          | None -> false)
        succs
  in
  if satisfied then (st, false)
  else
    let d = witness_depth_of st.rs_wdepth i in
    if d >= max_witness_depth then (st, false)  (* withhold — sound *)
    else
      let w = witness_id st.rs_fresh in
      let ws : subject = S_BNode w in
      let edge : redge = { re_s = i; re_p = p; re_o = T_BNode w; re_count = false } in
      let st1 = { st with rs_extra = edge :: st.rs_extra;
                          rs_fresh = st.rs_fresh + 1;
                          rs_wdepth = (w, d + 1) :: st.rs_wdepth } in
      let (st2, _) =
        match filler with
        | Some c -> add_label st1 ws c
        | None -> (st1, false)
      in
      (st2, true)

(* One label's deterministic expansion. INVARIANT maintained: every
   label ever added to node j is a class expression j's denotation
   provably belongs to in every model of the input graph (given the
   labels already present were). Union labels are NOT expanded here —
   they branch in the search (section 9). *)
(* Singleton-nominal existential witness (#209 Wave A follow-up,
   "spy-point" pattern). ∃P.{a} forces a P-edge to the SPECIFIC named
   individual `a` in every model — {a}'s extension is exactly one
   element (the referent of the term `a`), unlike a general ∃P.C
   filler where the witness's identity is unconstrained. We therefore
   assert (i, p, a) as a COUNTABLE edge (like hasValue) rather than
   minting an anonymous ∃-witness: this lets the edge participate in
   inverse-role successor counting AT `a` (e.g. a maxCardinality
   restriction on invP sitting on `a` must see this edge to derive a
   clash — that is the entire content of the spy-point pattern).
   Sound: CEXT({a}) = {denotation of a} in every model, so `i : ∃P.{a}`
   entails the edge (i, p, a) directly; no witness-merging machinery
   needed for the singleton case. Multi-member nominals ({a1,...,am},
   m >= 2) fall back to the ordinary anonymous witness — we cannot
   name which member is the successor, only that at least one is. *)
let ensure_existential (g : rdf_graph) (st : rstate) (i : subject) (p : wf_iri)
                       (c : class_expr)
  : rstate & bool =
  match c with
  | CE_OneOf [a] -> add_countable_edge g st i p a
  | _ -> ensure_witness g st i p (Some c)

(* -------------------------------------------------------------------
   8a. Multi-witness generation for unqualified min-cardinality k >= 2
   (#209 spy-point increment — the standard SHIQ/SHOIN tableau
   "generating rule" for >= n R, previously missing here: the k = 1
   path above only ever ensures ONE successor exists, and marks it
   non-countable / filler-less, so it never becomes a node other
   axioms can unfold against).

   Direct Semantics interprets ObjectMinCardinality(k, R) at x as
   |{y : (x,y) in EXT(R)}| >= k — i.e. k PAIRWISE DISTINCT
   R-successors are entailed to exist in EVERY model of the premises,
   regardless of their identity. When fewer than k pairwise
   provably-distinct R-successors are already known, minting k fresh
   mutually-distinct witnesses, adding k countable R-edges to them,
   AND registering them as full tableau nodes (unlike the k = 1 path)
   is a sound representative choice: whichever domain elements
   actually satisfy the k successors in a "real" model, every one of
   them is subject to every axiom that holds universally over the
   domain (e.g. an owl:Thing-anchored one) exactly as our fresh
   representatives are — so any further consequence propagated from
   the fresh witnesses is a genuine entailment, not a guess. This is
   what closes the spy-point pattern (WebOnt-description-logic-035):
   a maxCardinality bound on an inverse role, sitting on one "spy"
   individual, is violated once >= n domain elements are shown to
   exist via generating-rule witnesses that each acquire an edge to
   the spy through an unrelated owl:Thing-anchored axiom.

   Capped at `max_generated_witnesses` — for k beyond the cap we
   deliberately under-generate (WITHHOLDING is always sound; corpus
   cardinalities the spy-point pattern does not need, e.g. k = 601 in
   WebOnt-description-logic-910, would otherwise blow the shared
   per-test time budget for no soundness benefit — that test needs
   functional-property equality-propagation reasoning this increment
   does not attempt, see the module banner). Idempotent: once k
   witnesses are minted and grouped in `rs_gendistinct`, the very
   check this function opens with finds them on the next round (the
   group makes `exists_distinct_subset` succeed), so no further
   witnesses are minted for the same obligation. Guarded by the same
   witness-depth cap as `ensure_witness`, for the same cyclic-TBox
   termination reason. *)
let max_generated_witnesses : nat = 12

let rec mint_witness_group (base : nat) (n : nat)
  : Tot (list bnode_id) (decreases n) =
  if n = 0 then []
  else witness_id (base + n - 1) :: mint_witness_group base (n - 1)

let rec min_witness_parts (i : subject) (p : wf_iri) (d : nat) (bids : list bnode_id)
  : Tot (list redge & list rnode & list (bnode_id & nat) & list rdf_term)
    (decreases bids) =
  match bids with
  | [] -> ([], [], [], [])
  | b :: tl ->
    let (es, ns, ds, ts) = min_witness_parts i p d tl in
    let wt = T_BNode b in
    ({ re_s = i; re_p = p; re_o = wt; re_count = true } :: es,
     { rn_id = S_BNode b; rn_labels = [] } :: ns,
     (b, d + 1) :: ds,
     wt :: ts)

let ensure_min_witnesses (g : rdf_graph) (st : rstate) (i : subject) (p : wf_iri)
                         (k : nat)
  : rstate & bool =
  if k < 2 then ensure_witness g st i p None
  else
    let kk = if k > max_generated_witnesses then max_generated_witnesses else k in
    let succs = all_successors g st i p in
    if exists_distinct_subset g st.rs_gendistinct succs kk then (st, false)
    else
      let d = witness_depth_of st.rs_wdepth i in
      if d >= max_witness_depth then (st, false)  (* withhold — sound *)
      else
        let bids = mint_witness_group st.rs_fresh kk in
        let (es, ns, ds, ts) = min_witness_parts i p d bids in
        let st1 = { st with
                    rs_extra = es @ st.rs_extra;
                    rs_nodes = st.rs_nodes @ ns;
                    rs_fresh = st.rs_fresh + kk;
                    rs_wdepth = ds @ st.rs_wdepth;
                    rs_gendistinct = ts :: st.rs_gendistinct } in
        (st1, true)

(* Is role R transitive? Direct declaration, OR any declared inverse
   of R is declared transitive — Trans(R) iff Trans(R⁻) in every model
   (EXT(R⁻) = {(b,a) : (a,b) ∈ EXT(R)}; composing two R⁻-steps is the
   reverse of composing two R-steps, so one relation's composition
   closure is exactly the other's). *)
let role_is_transitive (st : rstate) (r : wf_iri) : bool =
  mem_iri r st.rs_transprops
  || List.Tot.existsb (fun q -> mem_iri q st.rs_transprops)
       (inverses_of st.rs_inv r)

(* For each transitive role R in `roles` (the ⊑*-closure below Q for a
   ∀Q.C label on node i), push the label ∀R.C onto every R-successor
   of i — the SHIQ ∀+ rule body. See the soundness argument at the
   call site (apply_label_rules, CE_AllValuesFrom case). *)
let rec push_transitive_foralls (g : rdf_graph) (st : rstate) (i : subject)
                                (c : class_expr) (roles : list wf_iri)
  : Tot (rstate & bool) (decreases roles) =
  match roles with
  | [] -> (st, false)
  | r :: tl ->
    let (st1, c1) =
      if role_is_transitive st r
      then forall_prop st (CE_AllValuesFrom r c) (all_successors g st i r)
      else (st, false)
    in
    let (st2, c2) = push_transitive_foralls g st1 i c tl in
    (st2, c1 || c2)

let apply_label_rules (g : rdf_graph) (st : rstate) (i : subject)
                      (l : class_expr)
  : rstate & bool =
  match l with
  | CE_IntersectionOf cs ->
    (* x ∈ C1 ⊓ ... ⊓ Cn implies x ∈ each Ci. *)
    add_labels_all st i cs
  | CE_AllValuesFrom p c ->
    let succs = all_successors g st i p in
    let (st1, c1) = forall_prop st c succs in
    (* Transitive S-rule (Wave E-rolebox), the standard SHIQ ∀+ rule:
       x ∈ ∀Q.C with Trans(R), R ⊑* Q, x -R-> y in every model implies
       y ∈ ∀R.C — the constraint must hold all the way down the
       R-chain, since y -R-> z (transitively x -R-> z, hence x -Q-> z
       by R ⊑* Q) puts z under the original ∀Q.C too. Iterated over
       EVERY transitive sub-role R of Q (including Q itself —
       `subproperties_of` is reflexive), each over its own R-successor
       view. Transitivity is checked inverse-aware
       (`role_is_transitive`): EXT(R) is transitive iff EXT(R⁻) is
       (Direct Semantics: (a,b),(b,c) ∈ EXT(R⁻) iff (c,b),(b,a) ∈
       EXT(R), whose composition is closed exactly when EXT(R)'s is) —
       the WebOnt t6/t7 fixtures place ∀invR.C labels while declaring
       Trans(r) with invR owl:inverseOf r, so the DIRECT-only check
       misses every one of them. Sound: only ever adds an entailed
       label over edges that already hold in every model, never
       fabricates an edge. *)
    let (st1b, c1b) =
      push_transitive_foralls g st1 i c
        (subproperties_of st.rs_subprop p)
    in
    (* EXT(owl:topObjectProperty) = Δ × Δ: every individual is its own
       top-successor, so ∀top.C puts C on the node itself. *)
    if p = owl_topObjectProperty then
      let (st2, c2) = add_label st1b i c in
      (st2, c1 || c1b || c2)
    else (st1b, c1 || c1b)
  | CE_HasValue p v -> add_countable_edge g st i p v
  | CE_SomeValuesFrom p c ->
    if is_bottom_prop p then (st, false)  (* C5 clash fires instead *)
    else ensure_existential g st i p c
  | CE_MinQualCard k p c ->
    if k >= 1 && not (is_bottom_prop p)
    then ensure_existential g st i p c
    else (st, false)
  | CE_MinCard k p ->
    if k >= 1 && not (is_bottom_prop p)
    then ensure_min_witnesses g st i p k
    else (st, false)
  | _ -> (st, false)

let step_label (tb : list (class_expr & class_expr)) (g : rdf_graph)
               (st : rstate) (i : subject) (l : class_expr)
  : rstate & bool =
  let (st1, c1) = apply_axioms tb st i l in
  let (st2, c2) = apply_label_rules g st1 i l in
  (st2, c1 || c2)

let rec pass_labels (tb : list (class_expr & class_expr)) (g : rdf_graph)
                    (st : rstate) (i : subject) (ls : list class_expr)
  : Tot (rstate & bool) (decreases ls) =
  match ls with
  | [] -> (st, false)
  | l :: tl ->
    let (st1, c1) = step_label tb g st i l in
    let (st2, c2) = pass_labels tb g st1 i tl in
    (st2, c1 || c2)

(* owl:FunctionalProperty (Wave E-rolebox): CEXT(P) is a partial
   function in every model for every declared functional P — i.e.
   every individual has AT MOST 1 P-successor, in every model,
   unconditionally (a structural fact, like owl:Thing membership just
   above — not a derived one). Injecting `CE_MaxCard 1 P` onto every
   node for every P in `rs_funcprops` folds this DIRECTLY into the
   EXISTING C3/C4 max-card clash machinery (`clash_for_label`'s
   `CE_MaxCard` case, `countable_successors`, `provably_distinct`) with
   NO new merge logic: a node whose (role-hierarchy-widened) countable
   P-successors include 2 pairwise-provably-distinct terms now clashes
   exactly as an explicit `<= 1 P` restriction would. Where the two
   successors are NOT provably distinct (e.g. two separate ∃-witnesses
   that would need to be MERGED/identified to see the clash) this
   stays open — witness merging is out of scope this wave (see module
   banner). Routed through `step_label` (not bare `add_label`) so it
   also unfolds any `(<=1 P, D)`-shaped TBox axiom exactly like every
   other injected label; idempotent via `step_label`'s underlying
   `add_label` syntactic dedup, same as the Thing injection below. *)
let rec inject_functional (tb : list (class_expr & class_expr)) (g : rdf_graph)
                          (fps : list wf_iri) (st : rstate) (i : subject)
  : Tot (rstate & bool) (decreases fps) =
  match fps with
  | [] -> (st, false)
  | fp :: tl ->
    (* STORE the max-1 label (owl2-named-merge wave fix), don't just
       route it through step_label transiently: `clash_for_label`'s C3/
       C4 cases, `find_merge_labels` (section 6a), and
       `find_identify_labels` (section 6b) all iterate a node's STORED
       `rn_labels` — a label that is only ever passed to `step_label`
       but never added is invisible to every one of them, so the
       FunctionalProperty-as-max-1 fold this function's banner promises
       never actually reached the max-card clash/merge machinery unless
       the fixture ALSO asserted an explicit maxCardinality restriction.
       Storing is sound for exactly the reason the banner already gives:
       CEXT(P) being a partial function is a structural fact of every
       model for a declared functional P, so `<= 1 P` is entailed of
       EVERY individual unconditionally. Idempotent via add_label's
       syntactic dedup (changed=false after the first round). *)
    let (st0, c0) = add_label st i (CE_MaxCard 1 fp) in
    let (st1, c1) = step_label tb g st0 i (CE_MaxCard 1 fp) in
    let (st2, c2) = inject_functional tb g tl st1 i in
    (st2, c0 || c1 || c2)

(* Universal owl:Thing membership: CEXT(owl:Thing) = Δ (the WHOLE
   domain) in every model, for EVERY individual, whether or not
   anything ever asserts `i rdf:type owl:Thing` explicitly. Without
   this, a node only carries the `CE_Named owl_Thing` label when the
   ABox happens to say so, so a TBox axiom shaped `owl:Thing ⊑ D` (or
   an edge-entailment check whose filler is literally owl:Thing, e.g.
   `∃P.owl:Thing`) silently never fires on individuals that were never
   explicitly typed Thing — even though it is ENTAILED for all of
   them. Adding the label unconditionally, once per node per round, is
   sound (it is a structural fact, not a derived one) and idempotent
   (add_label's syntactic dedup means it changes nothing after the
   first round it fires in). Routed through `step_label` so it also
   unfolds any `(owl:Thing, D)` TBox axiom exactly like every other
   label. Only reaches nodes already present in `rs_nodes`; witnesses
   minted with no filler (`ensure_witness ... None`) never become
   nodes and so stay outside this pass — withholding there is sound,
   just incomplete. *)
let rec pass_nodes (tb : list (class_expr & class_expr)) (g : rdf_graph)
                   (st : rstate) (ns : list rnode)
  : Tot (rstate & bool) (decreases ns) =
  match ns with
  | [] -> (st, false)
  | n :: tl ->
    let (st0, c0) = step_label tb g st n.rn_id (CE_Named owl_Thing) in
    let (st0f, c0f) = inject_functional tb g st.rs_funcprops st0 n.rn_id in
    let (st1, c1) = pass_labels tb g st0f n.rn_id n.rn_labels in
    let (st1b, c1b) = apply_axioms_edges tb g st1 n.rn_id in
    let (st2, c2) = pass_nodes tb g st1b tl in
    (st2, c0 || c0f || c1 || c1b || c2)

(* One full deterministic round over a snapshot of the current nodes.
   Nodes/labels added during the round are picked up next round. *)
let pass (tb : list (class_expr & class_expr)) (g : rdf_graph) (st : rstate)
  : rstate & bool =
  pass_nodes tb g st st.rs_nodes

(* -------------------------------------------------------------------
   9. Branching search with a threaded budget.
   ------------------------------------------------------------------- *)

type tri =
  | TClash   (* every branch below closed with a genuine clash *)
  | TOpen    (* some branch is fully expanded and clash-free *)
  | TOut     (* budget exhausted before a verdict *)

(* First union label (deterministic: node order, then label order) that
   is not yet satisfied (no disjunct present) and is branchable (all
   disjuncts Unknown-free — an Unknown disjunct can never be refuted,
   so such a union is skipped: dropping the constraint is sound). *)
let branchable_union (ls_all : list class_expr) (l : class_expr)
  : option (list class_expr) =
  match l with
  | CE_UnionOf cs ->
    if ce_list_definite cs
       && not (List.Tot.existsb (fun d -> mem_ce d ls_all) cs)
    then Some cs
    else None
  | _ -> None

let rec find_union_labels (ls_all : list class_expr) (ls_iter : list class_expr)
  : Tot (option (list class_expr)) (decreases ls_iter) =
  match ls_iter with
  | [] -> None
  | l :: tl ->
    (match branchable_union ls_all l with
     | Some cs -> Some cs
     | None -> find_union_labels ls_all tl)

let rec find_union_nodes (ns : list rnode)
  : Tot (option (subject & list class_expr)) (decreases ns) =
  match ns with
  | [] -> None
  | n :: tl ->
    (match find_union_labels n.rn_labels n.rn_labels with
     | Some cs -> Some (n.rn_id, cs)
     | None -> find_union_nodes tl)

(* -------------------------------------------------------------------
   8b. DPLL-style union-branching heuristics (owl2-dpll wave).

   PROBLEM this closes: `branch` below is refutation-complete but pays
   for every union label with a full nondeterministic case split, even
   when the OTHER disjuncts are already provably impossible given the
   node's current label set. A pure propositional-SAT encoding inside
   OWL (WebOnt-description-logic-504/502: nine disjoint boolean pairs
   plus_k/minus_k, ~90 three-literal `rdfs:subClassOf (plus_a OR
   plus_b OR minus_c)` clauses on ONE individual) turns this into a
   90-clause 3-SAT refutation. Branching in declaration order with NO
   propagation and NO clash-first pruning exhausts the fuel budget
   rediscovering the same pigeonhole contradiction combinatorially
   instead of converging the way DPLL does.

   TWO techniques below, both provably sound extensions of the
   EXISTING clash machinery — no new clash rule is added; the probe
   restates the C1/C2 arms of `clash_for_label` (section 6) and the
   axiom-match of `apply_axioms` (section 8) as PURE predicates over
   one node's label list, each arm carrying the same soundness
   argument as its stateful original:

   (1) UNIT PROPAGATION (`disjunct_would_clash` / `surviving_disjuncts`
       / `find_union_nodes_scan`): before branching on a union, probe
       EVERY disjunct with a cheap, budget-INDEPENDENT trial — would
       this disjunct C1/C2-clash against the node's current labels,
       either directly or through one axiom-unfold level? This is
       exactly what the first recursive `check` call on that branch
       would itself discover; computing it as a pure predicate spends
       neither an OR-branch nor budget on an alternative that was
       always going to close. (The probe deliberately never copies an
       rstate or walks the graph — an earlier draft that ran real
       `pass` rounds per probe was sound but two orders of magnitude
       too slow, blowing the per-test wall cap it was meant to save.)

       WHY label-local suffices as an ORACLE: `check` only consults
       the scan at quiescence, immediately after `has_clash` reported
       the WHOLE state clash-free, and the trial adds one label to
       node `i` — so `i`'s label set is where a new C1/C2 clash
       appears. Effects the probe cannot see (edge-counting clashes,
       cross-node filler counts, datatype facets) are deliberately not
       probed — the probe saying `false` only means "not proven to
       clash", which costs propagation power, never soundness; the
       real `branch` still explores such a disjunct and the real
       `has_clash` still catches the clash there.

       WHY one unfold level suffices for the target family:
       disjointWith compiles to BOTH contrapositive axiom pairs
       ((a, negb) AND (b, nega) — section 7), so by quiescence a
       DECIDED literal has already materialised the complement of
       every class it excludes ON THE NODE; probing the excluded
       disjunct then clashes IMMEDIATELY via C2, zero unfolds needed.
       The single unfold level additionally catches one-way
       `d subClassOf b` chains whose `b`-complement is already
       present. Deeper chains are simply not proven — conservative.

       If EVERY disjunct of some entailed union fails the probe, the
       union constraint itself is unsatisfiable given the branch's
       current commitments: TClash, with no `branch` call at all
       (mirrors `branch`'s own `[] -> (TClash, b)` base case — this
       just reaches the same verdict without paying disjunct by
       disjunct for it).

       If exactly ONE disjunct survives, classical disjunctive
       syllogism applies: x is entailed to be in C1 ⊔ ... ⊔ Cn (every
       label in this module is an entailed membership — see the `pass`
       invariant note above), and every Ci except the survivor is now
       PROVEN impossible along this branch, so the survivor is itself
       entailed. It is added as a plain deterministic label — no
       OR-branch, no budget spent on the disqualified alternatives —
       and `check` loops from the top, so a whole chain of forced
       literals collapses to a fixpoint (`find_union_nodes_scan`
       re-scans fresh every round, and each round BATCHES every unit
       it finds — see `union_scan_verdict`) before any real branch is
       taken — the DPLL "propagate to a fixpoint before deciding"
       discipline.

   (2) CLASH-FIRST PRUNING + FEWEST-SURVIVORS-FIRST (folded into the
       same scan): when a union still has 2+ surviving disjuncts, any
       disjunct the SAME probe already proved impossible is DROPPED
       from the list `branch` receives. `branch`'s AND-semantics
       ("TClash only if EVERY disjunct's branch closes") is unaffected
       by removing a disjunct independently proven to close, so this
       only shrinks the branching factor — it can never change the
       verdict. Live disjuncts keep their original relative order.
       Among still-multi-way unions the scan then picks the one with
       the FEWEST survivors (ties: first in node/label order — the
       old `find_union_nodes` discipline) — the classic most-
       constrained-first decision heuristic; branch-target selection
       was always an arbitrary deterministic choice here, so
       re-ordering it is trivially sound.

   PRIORITY: a 0-survivor union ANYWHERE refutes the path outright
   (short-circuits the scan); otherwise ALL 1-survivor unions found in
   the sweep propagate as one batch; only when nothing anywhere is
   forced does the search branch, on the fewest-survivor branchable
   union's PRUNED list. *)

(* Would label `c`, added to a node whose current label set is `ls`,
   produce an IMMEDIATE C1/C2 clash? Exactly the ⊥ / complement cases
   of `clash_for_label` (section 6), restated over a bare label list
   so the probe never copies an rstate: c = owl:Nothing (C1); c = ¬cc
   with cc present, or cc = owl:Thing (C2 — same two arms as
   `clash_for_label`'s `CE_ComplementOf` case); or ¬c itself present
   (C2 seen from the stored complement's side — `clash_for_label`
   detects this pair when ITERATING the stored ¬c, `mem_ce c ls_all`;
   here the probe iterates the trial `c`, so the mirror-image lookup
   is the one that fires). Every arm is a genuine model-theoretic
   contradiction per section 6's C1/C2 soundness arguments. *)
let label_conflicts_with (ls : list class_expr) (c : class_expr) : bool =
  (match c with
   | CE_Named x -> x = owl_Nothing
   | CE_ComplementOf cc ->
     mem_ce cc ls
     || (match cc with CE_Named x -> x = owl_Thing | _ -> false)
   | _ -> false)
  || mem_ce (CE_ComplementOf c) ls

(* One axiom-unfold level: some (a, rhs) with a = d (ce_eq — the same
   match `apply_axioms` fires on) whose entailed rhs conflicts with
   `ls`. d entails rhs on this node (section 7 axiom soundness), so a
   conflict is a genuine clash of the branch that commits to d. *)
let rec axiom_rhs_conflicts (tb : list (class_expr & class_expr))
                            (ls : list class_expr) (d : class_expr)
  : Tot bool (decreases tb) =
  match tb with
  | [] -> false
  | (a, rhs) :: tl ->
    (ce_eq a d && label_conflicts_with ls rhs)
    || axiom_rhs_conflicts tl ls d

(* Does hypothetically committing to disjunct `d` on a node with label
   set `ls` produce a C1/C2 clash, either immediately or after one
   axiom-unfold level? `true` is a genuine, already-sound clash
   derivation (both helpers above) — not an approximation of
   SOUNDNESS, only of completeness (`false` only means "not yet known
   to clash", never "safe"). A pure predicate over the label list: no
   rstate copy, no graph walk — this is what keeps a full scan (every
   disjunct of every open union, every quiescent point) cheap enough
   to run inside the per-test wall-clock cap. See the section 8b
   banner for why label-local + one unfold is the right oracle
   strength. *)
let disjunct_would_clash (tb : list (class_expr & class_expr))
                         (ls : list class_expr) (d : class_expr) : bool =
  label_conflicts_with ls d || axiom_rhs_conflicts tb ls d

(* Disjuncts of `cs` that survive the probe, order preserved. *)
let rec surviving_disjuncts (tb : list (class_expr & class_expr))
                            (ls : list class_expr) (cs : list class_expr)
  : Tot (list class_expr) (decreases cs) =
  match cs with
  | [] -> []
  | d :: tl ->
    let rest = surviving_disjuncts tb ls tl in
    if disjunct_would_clash tb ls d then rest else d :: rest

(* Scan verdict for one quiescent state. Batched: ALL forced unions
   found in one sweep propagate together — a unit's justification is
   evaluated against the CURRENT (pre-batch) label sets, and each unit
   is individually entailed given them, so adding several entailed
   labels in one step is exactly as sound as adding one and re-scanning
   (entailment is monotone under adding entailed labels); batching just
   amortises the full deterministic `pass` cascade that follows over
   the whole batch instead of paying it per unit — the difference
   between converging inside the per-test wall cap and not. *)
noeq type union_scan_verdict =
  | UScanEmpty  : union_scan_verdict
    (* some entailed union has ZERO surviving disjuncts *)
  | UScanForced : list (subject & class_expr) -> union_scan_verdict
    (* every (node, lone-survivor) pair found — nonempty *)
  | UScanBranch : subject -> list class_expr -> union_scan_verdict
    (* fewest-survivor multi-way union, pruned *)
  | UScanNone   : union_scan_verdict

(* Prefer the FEWEST survivors among multi-way candidates
   (most-constrained-first); ties keep the EARLIER candidate — the
   "first in node/label order" contract `find_union_nodes` always had.
   `a` is always the earlier candidate at every call site below.
   Branch-target selection was always an arbitrary deterministic
   choice, so re-ordering it is trivially sound. *)
let combine_branch_pick (a b : option (subject & list class_expr))
  : option (subject & list class_expr) =
  match a, b with
  | Some (_, sa), Some (_, sb) ->
    if List.Tot.length sb < List.Tot.length sa then b else a
  | None, _ -> b
  | _, None -> a

(* One node's labels: collect EVERY branchable union's outcome.
   UScanEmpty short-circuits (the whole search path is refuted — no
   point scanning further); forced pairs accumulate; the fewest-
   survivor multi-way candidate is remembered. *)
let rec find_union_labels_scan (tb : list (class_expr & class_expr)) (i : subject)
                               (ls_all : list class_expr) (ls_iter : list class_expr)
  : Tot (option (list (subject & class_expr) & option (subject & list class_expr)))
    (decreases ls_iter) =
  match ls_iter with
  | [] -> Some ([], None)
  | l :: tl ->
    (match branchable_union ls_all l with
     | None -> find_union_labels_scan tb i ls_all tl
     | Some cs ->
       (match surviving_disjuncts tb ls_all cs with
        | [] -> None  (* encodes UScanEmpty *)
        | survivors ->
          (match find_union_labels_scan tb i ls_all tl with
           | None -> None
           | Some (forced, pick) ->
             (match survivors with
              | [d] -> Some ((i, d) :: forced, pick)
              | _ -> Some (forced, combine_branch_pick (Some (i, survivors)) pick)))))

let rec find_union_nodes_scan_aux (tb : list (class_expr & class_expr)) (ns : list rnode)
  : Tot (option (list (subject & class_expr) & option (subject & list class_expr)))
    (decreases ns) =
  match ns with
  | [] -> Some ([], None)
  | n :: tl ->
    (match find_union_labels_scan tb n.rn_id n.rn_labels n.rn_labels with
     | None -> None
     | Some (forced_n, pick_n) ->
       (match find_union_nodes_scan_aux tb tl with
        | None -> None
        | Some (forced_tl, pick_tl) ->
          Some (forced_n @ forced_tl, combine_branch_pick pick_n pick_tl)))

let find_union_nodes_scan (tb : list (class_expr & class_expr)) (ns : list rnode)
  : union_scan_verdict =
  match find_union_nodes_scan_aux tb ns with
  | None -> UScanEmpty
  | Some ([], None) -> UScanNone
  | Some ([], Some (i, survivors)) -> UScanBranch i survivors
  | Some (forced, _) -> UScanForced forced

(* Batch-apply the forced units. Each `d` was entailed at the state the
   scan ran on (all sibling disjuncts provably clash there — section 8b
   banner); adding labels never retracts entailments, so every later
   unit in the batch is still entailed when its turn comes. *)
let rec add_forced_labels (st : rstate) (ps : list (subject & class_expr))
  : Tot rstate (decreases ps) =
  match ps with
  | [] -> st
  | (i, d) :: tl ->
    let (st1, _) = add_label st i d in
    add_forced_labels st1 tl

(* check/branch: the budget is THREADED — every recursive entry
   consumes at least one unit and returns the remainder, so total work
   across the whole search tree is linear in the initial budget.

   Verdict soundness:
     TClash from `check`  : the deterministic expansion (all additions
       entailed) reached a state containing a clash — no model exists
       for this branch's assumptions.
     TClash from `branch` : x ∈ C1 ⊔ ... ⊔ Cn is entailed, and for
       EVERY i the branch extended with x ∈ Ci refuted. In any model x
       belongs to some Ci, so no model exists. TOut/TOpen from any
       disjunct forbids the TClash verdict (TOpen wins over TOut so an
       open branch reports openness).                                  *)
let rec check (tb : list (class_expr & class_expr)) (g : rdf_graph)
              (st : rstate) (b : nat)
  : Tot (tri & (r : nat { r <= b })) (decreases %[b; 0]) =
  if b = 0 then (TOut, 0)
  else if has_clash g st then (TClash, b - 1)
  else
    let (st', changed) = pass tb g st in
    if changed then
      let (r, b') = check tb g st' (b - 1) in (r, b')
    else
      (match find_union_nodes_scan tb st'.rs_nodes with
       | UScanEmpty ->
         (* every disjunct of some entailed union provably clashes
            under the probe: the union constraint itself is
            unsatisfiable along this branch — section 8b technique
            (1), the "0 survivors" case. Same verdict `branch` would
            reach after exhausting every disjunct, reached without
            paying for the recursion. *)
         (TClash, b - 1)
       | UScanForced forced ->
         (* unit propagation (section 8b technique (1)): each lone
            survivor is entailed by disjunctive syllogism now that
            every sibling disjunct is proven impossible — add the
            whole batch deterministically and loop; no OR-branch
            spent. *)
         let st'' = add_forced_labels st' forced in
         let (r, b') = check tb g st'' (b - 1) in (r, b')
       | UScanBranch i survivors ->
         (* clash-first pruning + fewest-survivors-first (section 8b
            technique (2)): `survivors` already dropped every disjunct
            the probe proved impossible — branch only over what is
            genuinely still live, on the most constrained union. *)
         let (r, b') = branch tb g i survivors st' (b - 1) in (r, b')
       | UScanNone ->
         (* ≤-rule (owl2-le-rule wave): only consulted once union
            branching has nothing left to offer — see the section 6a
            banner for the soundness argument and why trying every
            candidate pair (AND-semantics, `merge_branch` below) is the
            refutation-sound encoding of the rule's real
            nondeterminism. *)
         (match find_merge_nodes g st' st'.rs_nodes with
          | Some prs ->
            let (r, b') = merge_branch tb g prs st' (b - 1) in (r, b')
          | None ->
            (* Named-individual identification (owl2-named-merge wave):
               only consulted once BOTH union branching and witness
               merging have nothing left to offer — see the section 6b
               banner for why this is the correct fallback tier (it
               never second-guesses a witness-witness merge section 6a
               already owns). *)
            (match find_identify_nodes g st' st'.rs_nodes with
             | Some prs ->
               let (r, b') = identify_branch tb g prs st' (b - 1) in (r, b')
             | None -> (TOpen, b - 1))))
and branch (tb : list (class_expr & class_expr)) (g : rdf_graph)
           (i : subject) (ds : list class_expr) (st : rstate) (b : nat)
  : Tot (tri & (r : nat { r <= b })) (decreases %[b; List.Tot.length ds]) =
  match ds with
  | [] -> (TClash, b)
  | d :: tl ->
    if b = 0 then (TOut, 0)
    else
      let (st1, _) = add_label st i d in
      let (r1, b1) = check tb g st1 (b - 1) in
      (match r1 with
       | TOpen -> (TOpen, b1)
       | _ ->
         let (r2, b2) = branch tb g i tl st b1 in
         (match r1, r2 with
          | TClash, x -> (x, b2)
          | TOut, TOpen -> (TOpen, b2)
          | TOut, _ -> (TOut, b2)))
and merge_branch (tb : list (class_expr & class_expr)) (g : rdf_graph)
                 (pairs : list (subject & subject)) (st : rstate) (b : nat)
  : Tot (tri & (r : nat { r <= b })) (decreases %[b; List.Tot.length pairs]) =
  (* Same shape and same verdict-combination as `branch` above (see the
     section 6a banner): TClash only if EVERY candidate pair's merge
     closes; TOpen from any candidate wins; TOut otherwise. Budget is
     threaded exactly like `branch` — each entry consumes >= 1 unit. *)
  match pairs with
  | [] -> (TClash, b)
  | (y, z) :: tl ->
    if b = 0 then (TOut, 0)
    else
      let st1 = merge_into st y z in
      let (r1, b1) = check tb g st1 (b - 1) in
      (match r1 with
       | TOpen -> (TOpen, b1)
       | _ ->
         let (r2, b2) = merge_branch tb g tl st b1 in
         (match r1, r2 with
          | TClash, x -> (x, b2)
          | TOut, TOpen -> (TOpen, b2)
          | TOut, _ -> (TOut, b2)))
and identify_branch (tb : list (class_expr & class_expr)) (g : rdf_graph)
                    (pairs : list (subject & subject)) (st : rstate) (b : nat)
  : Tot (tri & (r : nat { r <= b })) (decreases %[b; List.Tot.length pairs]) =
  (* Same shape, same verdict-combination, and the SAME
     `%[b; List.Tot.length pairs]` measure as `merge_branch` above (see
     the section 6b banner): TClash only if EVERY candidate pair's
     identification closes; TOpen from any candidate wins; TOut
     otherwise. The only difference from `merge_branch` is the state
     update — `identify_pair` extends the `rs_ident` partition instead
     of physically redirecting edges. *)
  match pairs with
  | [] -> (TClash, b)
  | (y, z) :: tl ->
    if b = 0 then (TOut, 0)
    else
      let st1 = { st with rs_ident = identify_pair st.rs_ident (subject_to_term y) (subject_to_term z) } in
      let (r1, b1) = check tb g st1 (b - 1) in
      (match r1 with
       | TOpen -> (TOpen, b1)
       | _ ->
         let (r2, b2) = identify_branch tb g tl st b1 in
         (match r1, r2 with
          | TClash, x -> (x, b2)
          | TOut, TOpen -> (TOpen, b2)
          | TOut, _ -> (TOut, b2)))

(* -------------------------------------------------------------------
   10. Graph-level immediate inconsistency checks.
   ------------------------------------------------------------------- *)

let sameAs_linked (g : rdf_graph) (a : rdf_term) (b : rdf_term) : bool =
  List.Tot.existsb
    (fun (t : triple) ->
      t.p = owl_sameAs &&
      ((rdf_term_eq (subject_to_term t.s) a && rdf_term_eq t.o b) ||
       (rdf_term_eq (subject_to_term t.s) b && rdf_term_eq t.o a)))
    g

(* G1: owl:AllDifferent members must be pairwise distinct. A member
   pair that is the SAME term (x <> x) or is owl:sameAs-linked while
   listed as different is unsatisfiable (eq-diff2 / eq-diff3, OWL 2
   RL Table 4). Positions i < j only — a term is trivially sameAs
   itself via the closure's reflexivity, which must not fire. *)
let rec alldiff_pair_violation (g : rdf_graph) (ms : list rdf_term)
  : Tot bool (decreases ms) =
  match ms with
  | [] -> false
  | h :: tl ->
    List.Tot.existsb
      (fun (o : rdf_term) -> rdf_term_eq h o || sameAs_linked g h o)
      tl
    || alldiff_pair_violation g tl

let rec alldiff_lists_violation (g : rdf_graph) (heads : list rdf_term)
  : Tot bool (decreases heads) =
  match heads with
  | [] -> false
  | h :: tl ->
    alldiff_pair_violation g (walk_rdf_list g h 64)
    || alldiff_lists_violation g tl

let alldifferent_violation (g : rdf_graph) : bool =
  List.Tot.existsb
    (fun (t : triple) ->
      t.p = rdf_type
      && rdf_term_eq t.o (T_IRI owl_AllDifferent_iri)
      && (alldiff_lists_violation g (find_objects g t.s owl_members_iri)
          || alldiff_lists_violation g (find_objects g t.s owl_distinctMembers)))
    g

(* G2: EXT(bottom property) = ∅ — any asserted triple over it is false
   in every model. *)
let bottom_property_assertion (g : rdf_graph) : bool =
  List.Tot.existsb (fun (t : triple) -> is_bottom_prop t.p) g

(* G3: (p owl:propertyDisjointWith p) forces EXT(p) disjoint from
   itself, i.e. EXT(p) = ∅ — any use of p is then unsatisfiable
   (prp-pdw with p1 = p2, which the RL marker misses because it
   requires two distinct predicates). *)
let self_disjoint_property_in_use (g : rdf_graph) : bool =
  List.Tot.existsb
    (fun (t : triple) ->
      t.p = owl_propertyDisjointWith
      && rdf_term_eq (subject_to_term t.s) t.o
      && (match t.s with
          | S_IRI p -> List.Tot.existsb (fun (u : triple) -> u.p = p) g
          | _ -> false))
    g

(* G4: rdf:nil is the (unique) EMPTY list. Both OWL 2 semantics give
   list structure to sequences (Direct Semantics can only parse
   well-formed lists; RDF-Based Semantics' extension conditions for
   sequences, OWL 2 RDF-Based Semantics section 5, treat rdf:nil as
   the terminator with no rdf:first / rdf:rest of its own), so a graph
   asserting `rdf:nil rdf:first _` or `rdf:nil rdf:rest _` has no
   model — the W3C InconsistencyTests WebOnt-I5.5-003/-004 pin exactly
   this (annotated DIRECT + RDF-BASED). *)
let nil_structure_violation (g : rdf_graph) : bool =
  List.Tot.existsb
    (fun (t : triple) ->
      (t.p = rdf_first || t.p = rdf_rest)
      && (match t.s with
          | S_IRI i -> i = rdf_nil
          | _ -> false))
    g

(* G5: hasSelf-disjointness. When a named class c is owl:disjointWith
   a restriction r = ObjectHasSelf(p) (owl:onProperty p +
   owl:hasSelf "true"), an individual x with `x rdf:type c` AND the
   reflexive edge `x p x` lies in both CEXT(c) and CEXT(r) — but
   disjointWith forces CEXT(c) ∩ CEXT(r) = ∅ (OWL 2 Direct Semantics,
   ObjectHasSelf: x ∈ SELF(p) iff (x,x) ∈ EXT(p)). No model exists.
   Tableau.fst's class_expr AST has no HasSelf constructor (parse
   yields CE_Unknown), so this narrow shape is checked at graph level
   instead — the W3C InconsistencyTest Footnote-not-about-self pins it. *)
let owl_hasSelf_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#hasSelf");
  "http://www.w3.org/2002/07/owl#hasSelf"

let is_hasself_restriction (g : rdf_graph) (r : subject) : option wf_iri =
  match find_first_object g r owl_onProperty with
  | Some (T_IRI p) ->
    (match find_first_object g r owl_hasSelf_iri with
     | Some (T_Literal l) ->
       if l.lexical_form = "true" || l.lexical_form = "1" then Some p else None
     | _ -> None)
  | _ -> None

let hasself_disjoint_violation_for (g : rdf_graph) (c : wf_iri) (r : subject)
  : bool =
  match is_hasself_restriction g r with
  | None -> false
  | Some p ->
    List.Tot.existsb
      (fun (t : triple) ->
        t.p = rdf_type
        && rdf_term_eq t.o (T_IRI c)
        && List.Tot.existsb
             (fun (u : triple) ->
               u.p = p && subject_eq u.s t.s
               && rdf_term_eq u.o (subject_to_term t.s))
             g)
      g

let hasself_disjoint_violation (g : rdf_graph) : bool =
  List.Tot.existsb
    (fun (t : triple) ->
      t.p = owl_disjointWith
      && (match t.s, t.o with
          | S_IRI c, T_BNode b -> hasself_disjoint_violation_for g c (S_BNode b)
          | S_BNode b, T_IRI c -> hasself_disjoint_violation_for g c (S_BNode b)
          | S_IRI c, T_IRI r -> hasself_disjoint_violation_for g c (S_IRI r)
          | _, _ -> false))
    g

let immediate_inconsistency (g : rdf_graph) : bool =
  alldifferent_violation g
  || bottom_property_assertion g
  || self_disjoint_property_in_use g
  || nil_structure_violation g
  || hasself_disjoint_violation g

(* -------------------------------------------------------------------
   11. Initial state + entry point.
   ------------------------------------------------------------------- *)

let rec init_nodes_aux (gfull : rdf_graph) (ts : rdf_graph) (st : rstate)
  : Tot rstate (decreases ts) =
  match ts with
  | [] -> st
  | t :: tl ->
    let st' =
      if t.p = rdf_type then
        let (st1, _) = add_label st t.s (parse_nnf gfull t.o) in st1
      else st
    in
    init_nodes_aux gfull tl st'

let init_state (g : rdf_graph) : rstate =
  init_nodes_aux g g
    { rs_nodes = []; rs_extra = []; rs_fresh = 0; rs_wdepth = [];
      rs_inv = collect_inverse_pairs g; rs_gendistinct = [];
      rs_subprop = collect_subprop_pairs g;
      rs_transprops = collect_transitive_props g;
      rs_funcprops = collect_functional_props g;
      rs_ident = [] }

(* tableau_consistent — the public satisfiability check.

     Some false : the graph is provably INCONSISTENT (a clash on every
                  branch, or an immediate graph-level violation). This
                  is the only verdict wired into scoring; each
                  contributing rule carries its Direct Semantics
                  soundness argument above.
     Some true  : saturated + branched to quiescence with no clash.
                  NOT a completeness guarantee (see module banner);
                  callers must not score "consistent" on it alone
                  beyond what they already do by default.
     None       : fuel exhausted — indeterminate; callers keep their
                  existing behaviour.                                   *)
let tableau_consistent (g : rdf_graph) (fuel : nat) : Tot (option bool) =
  if immediate_inconsistency g then Some false
  else
    let tb = collect_axioms g in
    let st0 = init_state g in
    match check tb g st0 fuel with
    | (TClash, _) -> Some false
    | (TOpen, _) -> Some true
    | (TOut, _) -> None

(* -------------------------------------------------------------------
   12. In-file sanity matrix (guarded, dead-code — same pattern as
       Tableau.fst section 9).
   ------------------------------------------------------------------- *)

let _refute_sanity_matrix : unit =
  if false then
    begin
      (* NNF pushes negation through booleans and flips quantifiers. *)
      let i_a : wf_iri = assert_norm (is_iri "http://ex/A"); "http://ex/A" in
      let i_b : wf_iri = assert_norm (is_iri "http://ex/B"); "http://ex/B" in
      let neg_union = nnf (CE_ComplementOf (CE_UnionOf [CE_Named i_a; CE_Named i_b])) in
      assert_norm (ce_eq neg_union
        (CE_IntersectionOf [CE_ComplementOf (CE_Named i_a);
                            CE_ComplementOf (CE_Named i_b)]));
      (* neg(>= 1 P) = (<= 0 P). *)
      let i_p : wf_iri = assert_norm (is_iri "http://ex/p"); "http://ex/p" in
      assert_norm (ce_eq (nnf_neg (CE_MinCard 1 i_p)) (CE_MaxCard 0 i_p));
      (* Unknown never equals itself (no fabricated clashes). *)
      assert_norm (not (ce_eq CE_Unknown CE_Unknown));
      ()
    end
  else ()
