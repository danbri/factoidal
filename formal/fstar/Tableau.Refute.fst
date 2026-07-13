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
                     deliberately incomplete: nominals/oneOf, datatype
                     facets, inverse roles, sameAs-merging cardinality
                     are not implemented); callers must treat it the
                     same as None for scoring "inconsistent".
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
  | CE_ExactCard _ _ | CE_OneOf _ -> true
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
  | CE_ExactCard k p -> CE_IntersectionOf [CE_MinCard k p; CE_MaxCard k p]
  | CE_ExactQualCard k p d ->
    let d' = nnf d in
    CE_IntersectionOf [CE_MinQualCard k p d'; CE_MaxQualCard k p d']
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

let max_witness_depth : nat = 3

let rec witness_depth_of (ds : list (bnode_id & nat)) (i : subject)
  : Tot nat (decreases ds) =
  match i with
  | S_IRI _ -> 0
  | S_BNode b ->
    (match ds with
     | [] -> 0
     | (w, d) :: tl -> if w = b then d else witness_depth_of tl i)

let rec mem_ce (c : class_expr) (ls : list class_expr) : Tot bool (decreases ls) =
  match ls with
  | [] -> false
  | l :: tl -> if ce_eq c l then true else mem_ce c tl

(* Syntactic membership — storage dedup only (see ce_eq_syn banner). *)
let rec mem_ce_syn (c : class_expr) (ls : list class_expr) : Tot bool (decreases ls) =
  match ls with
  | [] -> false
  | l :: tl -> if ce_eq_syn c l then true else mem_ce_syn c tl

let rec labels_of_nodes (ns : list rnode) (i : subject)
  : Tot (list class_expr) (decreases ns) =
  match ns with
  | [] -> []
  | n :: tl -> if subject_eq n.rn_id i then n.rn_labels else labels_of_nodes tl i

let labels_of (st : rstate) (i : subject) : list class_expr =
  labels_of_nodes st.rs_nodes i

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

let countable_successors (g : rdf_graph) (st : rstate) (i : subject) (p : wf_iri)
  : list rdf_term =
  let invs = inverses_of st.rs_inv p in
  dedup_terms (find_objects g i p
               @ extra_objects st.rs_extra i p true
               @ base_reverse_objects g i invs
               @ extra_reverse_objects_all st.rs_extra (subject_to_term i) invs true)

let all_successors (g : rdf_graph) (st : rstate) (i : subject) (p : wf_iri)
  : list rdf_term =
  let invs = inverses_of st.rs_inv p in
  dedup_terms (find_objects g i p
               @ extra_objects st.rs_extra i p false
               @ base_reverse_objects g i invs
               @ extra_reverse_objects_all st.rs_extra (subject_to_term i) invs false)

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
       literal to its value.
   Everything else (distinct IRIs without differentFrom under no-UNA,
   cross-datatype literals, bnodes) is NOT provably distinct.          *)

let comparable_datatype (d : wf_iri) : bool =
  d = xsd_integer || d = xsd_decimal || d = xsd_string_dt || d = xsd_boolean_dt

let provably_distinct (g : rdf_graph) (a : rdf_term) (b : rdf_term) : bool =
  differentFrom_in_graph g a b
  || differentFrom_in_graph g b a
  || (match a, b with
      | T_Literal l1, T_Literal l2 ->
        l1.datatype = l2.datatype
        && comparable_datatype l1.datatype
        && not (datatype_value_eq l1 l2)
      | _, _ -> false)

(* Keep only candidates provably distinct from h, with a length bound
   so the subset search below has a decreasing measure. *)
let rec filter_distinct_from (g : rdf_graph) (h : rdf_term) (ts : list rdf_term)
  : Tot (r : list rdf_term { List.Tot.length r <= List.Tot.length ts })
    (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    let rest = filter_distinct_from g h tl in
    if provably_distinct g h t then t :: rest else rest

(* Is `x` provably distinct from EVERY term in `ms`? Vacuously true for
   `ms = []` — being asserted a member of an EMPTY nominal (owl:oneOf
   with no elements, semantically owl:Nothing) is itself a clash, and
   this fold correctly reports that case as "distinct from all
   (zero) members" without a separate empty-list special case. *)
let rec all_provably_distinct (g : rdf_graph) (x : rdf_term) (ms : list rdf_term)
  : Tot bool (decreases ms) =
  match ms with
  | [] -> true
  | m :: tl -> provably_distinct g x m && all_provably_distinct g x tl

(* Does `cands` contain `need` PAIRWISE provably-distinct members?
   Sound: a pairwise provably-distinct set of size k+1 denotes k+1
   distinct elements in every model, violating <= k. Exhaustive
   branch-on-first-element search; candidate lists are successor sets
   of a single individual in W3C test data (tiny). *)
let rec exists_distinct_subset (g : rdf_graph) (cands : list rdf_term) (need : nat)
  : Tot bool (decreases (List.Tot.length cands)) =
  if need = 0 then true
  else
    match cands with
    | [] -> false
    | h :: tl ->
      (exists_distinct_subset g (filter_distinct_from g h tl) (need - 1))
      || exists_distinct_subset g tl need

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
    all_provably_distinct g (subject_to_term i) members
  | CE_MaxCard k p ->
    let succs = countable_successors g st i p in
    if k = 0 then Cons? succs
    else exists_distinct_subset g succs (k + 1)
  | CE_MaxQualCard k p c ->
    let succs = filter_in_filler st c (countable_successors g st i p) in
    if k = 0 then Cons? succs
    else exists_distinct_subset g succs (k + 1)
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
    clash_labels g st n.rn_id n.rn_labels n.rn_labels
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
      (a, b) :: (b, a) :: rest
    else if t.p = owl_disjointWith || t.p = owl_complementOf then
      let a = parse_nnf_subject gfull t.s in
      let b = parse_nnf gfull t.o in
      let na = nnf (CE_ComplementOf (parse_class_expr gfull (subject_to_term t.s) 32)) in
      let nb = nnf (CE_ComplementOf (parse_class_expr gfull t.o 32)) in
      (a, nb) :: (b, na) :: rest
    else if (t.p = owl_onProperty || t.p = owl_intersectionOf || t.p = owl_unionOf)
            && S_IRI? t.s then
      (* Named class-expression subject: z ≡ CE(z). One axiom pair per
         marker triple; duplicates are harmless (add_label dedups). *)
      (match t.s with
       | S_IRI z ->
         let ce = nnf (parse_ce_of_subject gfull t.s) in
         (CE_Named z, ce) :: (ce, CE_Named z) :: rest
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
    else exists_distinct_subset g (countable_successors g st i p) k
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
      else exists_distinct_subset g cs k
  | _ -> false

(* Once per node per round: fire axioms whose LHS membership is proved
   by the node's asserted edges. Adds the LHS too (so label-level clash
   rules like min/max see it), then the RHS. *)
let rec apply_axioms_edges (tb : list (class_expr & class_expr)) (g : rdf_graph)
                           (st : rstate) (i : subject)
  : Tot (rstate & bool) (decreases tb) =
  match tb with
  | [] -> (st, false)
  | (a, d) :: tl ->
    let (st1, c1) =
      if not (mem_ce_syn a (labels_of st i)) && edge_entails_membership g st i a
      then
        let (sta, ca) = add_label st i a in
        let (stb, cb) = add_label sta i d in
        (stb, ca || cb)
      else (st, false)
    in
    let (st2, c2) = apply_axioms_edges tl g st1 i in
    (st2, c1 || c2)

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
    (* EXT(owl:topObjectProperty) = Δ × Δ: every individual is its own
       top-successor, so ∀top.C puts C on the node itself. *)
    if p = owl_topObjectProperty then
      let (st2, c2) = add_label st1 i c in
      (st2, c1 || c2)
    else (st1, c1)
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
    then ensure_witness g st i p None
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
    let (st1, c1) = pass_labels tb g st0 n.rn_id n.rn_labels in
    let (st1b, c1b) = apply_axioms_edges tb g st1 n.rn_id in
    let (st2, c2) = pass_nodes tb g st1b tl in
    (st2, c0 || c1 || c1b || c2)

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
      (match find_union_nodes st'.rs_nodes with
       | None -> (TOpen, b - 1)
       | Some (i, ds) ->
         let (r, b') = branch tb g i ds st' (b - 1) in (r, b'))
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
      rs_inv = collect_inverse_pairs g }

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
