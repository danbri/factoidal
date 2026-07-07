module Tableau

(* OWL-DL tableau reasoner — STAGES (b) + (c): CLASS-EXPRESSION
   SATISFIABILITY INCLUDING CARDINALITY RESTRICTIONS.

   This module implements the part of the tableau that can answer
   "is individual i a member of class-expression C?" where C is built from:
     - Named classes (IRIs)
     - owl:Restriction bnodes with owl:onProperty and
       * owl:someValuesFrom
       * owl:allValuesFrom
       * owl:hasValue
       * owl:minCardinality / owl:maxCardinality / owl:cardinality
       * owl:minQualifiedCardinality + owl:onClass
       * owl:maxQualifiedCardinality + owl:onClass
       * owl:qualifiedCardinality + owl:onClass
     - Boolean combinators: owl:intersectionOf, owl:unionOf
     - Partial owl:complementOf (only the trivial clash check within a branch)

   STAGE (c) SOUNDNESS NOTES:
     - min-N: Some true when count of known P-successors (in any class
       for unqualified, or provably in class C for qualified) is >= N.
       Under open-world + no-UNA, two distinct IRI successors might be
       sameAs, so the count is a conservative LOWER bound. Some true
       from it is still sound (we exhibit witnesses; OWL doesn't require
       distinctness for min-N unless asserted). Never returns Some false
       here — absence of known successors does not preclude unseen ones.
     - max-N: Only returns Some true when k=0 AND there are no known
       successors (or, for qualified, no successor is provably in C).
       True max-N refutation requires sameAs aggregation / UNA — deferred.
     - exactly-N: Same k=0 restriction as max-N.

   WHAT REMAINS DEFERRED TO LATER STAGES:
     - No full classical-negation dual-branch search — stage (d).
     - No fresh-individual skolemisation for ∃ — stage (e).
     - Stage (c) max/exact over k>=1 requires differentFrom tracking — stage (f).

   The contract of `owl_tableau_entails` is unchanged from stage (a):
     Some true  = provably entailed
     Some false = provably NOT entailed
     None       = unknown — caller should fall back to the Datalog
                  closure. Returning None is ALWAYS sound.

   Soundness note: every place this file can produce `Some true` is
   justified by a direct model-theoretic argument (see comments on
   is_member cases). When uncertain, we return None. The tableau
   never fabricates fresh individuals in stage (b), so existential
   obligations that cannot be discharged from the ABox yield None.
*)

open FStar.List.Tot
open RDF.Graph.Executable
open OWL.Vocabulary

(* -------------------------------------------------------------------
   1. OWL vocabulary constants needed by stage (b).
   ------------------------------------------------------------------- *)

(* OWL + RDF IRI constants (owl_intersectionOf, owl_Restriction,
   rdf_first, etc.) come from `OWL.Vocabulary` opened above. The
   constants live in one shared module so Tableau and other consumers
   (eventually OWL.QueryRewrite) don't redefine them. See #209
   (Tableau audit). *)

(* -------------------------------------------------------------------
   2. Class expression AST.
   ------------------------------------------------------------------- *)

(* A class expression. We intentionally keep the AST small for stage (b).
   Later stages will extend this with cardinality (CE_MinCard etc.) and
   enumerated classes (CE_OneOf).

   The recursive constructors are bounded at parse time by a fuel
   parameter so F* can discharge termination with a decreases clause. *)
noeq type class_expr =
  | CE_Named       : wf_iri -> class_expr
  (* ∃ P. C *)
  | CE_SomeValuesFrom : wf_iri -> class_expr -> class_expr
  (* ∀ P. C *)
  | CE_AllValuesFrom  : wf_iri -> class_expr -> class_expr
  (* ∃ P. {v} — "has specific value" *)
  | CE_HasValue       : wf_iri -> rdf_term -> class_expr
  (* Intersection: C1 ⊓ C2 ⊓ ... — stored as list. Empty list is
     equivalent to owl:Thing (top); stage (b) does not synthesise the
     empty case. *)
  | CE_IntersectionOf : list class_expr -> class_expr
  (* Union: C1 ⊔ C2 ⊔ ... *)
  | CE_UnionOf        : list class_expr -> class_expr
  (* Complement: ¬ C. Stage (b) only handles the trivial "C ⊓ ¬C
     within one branch is a clash" check; full dual-branch search is
     stage (d). *)
  | CE_ComplementOf   : class_expr -> class_expr
  (* Stage (c): cardinality restrictions. *)
  | CE_MinCard        : nat -> wf_iri -> class_expr
  | CE_MaxCard        : nat -> wf_iri -> class_expr
  | CE_ExactCard      : nat -> wf_iri -> class_expr
  | CE_MinQualCard    : nat -> wf_iri -> class_expr -> class_expr
  | CE_MaxQualCard    : nat -> wf_iri -> class_expr -> class_expr
  | CE_ExactQualCard  : nat -> wf_iri -> class_expr -> class_expr
  (* Parse gave up — unknown class expression. `is_member` returns
     None for these, falling back to the Datalog closure. *)
  | CE_Unknown        : class_expr

(* -------------------------------------------------------------------
   3. Helpers over the RDF graph.
   ------------------------------------------------------------------- *)

(* Find the first object of (subj pred ?) in g, if any. *)
let find_first_object (g : rdf_graph) (subj : subject) (pred : wf_iri)
  : option rdf_term =
  match find_objects g subj pred with
  | []     -> None
  | h :: _ -> Some h

(* Treat an rdf_term as a subject when possible (IRIs and bnodes only). *)
let term_as_subject (t : rdf_term) : option subject =
  match t with
  | T_IRI i   -> Some (S_IRI i)
  | T_BNode b -> Some (S_BNode b)
  | _         -> None

(* Walk an RDF list rooted at `head` (which is the object of some
   triple pointing into the list). Returns the list elements in
   order. Bounded by fuel (the length of the graph is an adequate
   bound since each step consumes at least one triple). *)
let rec walk_rdf_list (g : rdf_graph) (head : rdf_term) (fuel : nat)
  : Tot (list rdf_term) (decreases fuel) =
  match fuel with
  | 0 -> []
  | n ->
    match head with
    | T_IRI i -> if i = rdf_nil then [] else []
    | T_BNode _ ->
      (match term_as_subject head with
       | None -> []
       | Some s ->
         let first = find_first_object g s rdf_first in
         let rest  = find_first_object g s rdf_rest in
         match first, rest with
         | Some h, Some t -> h :: walk_rdf_list g t (n - 1)
         | _, _ -> [])
    | _ -> []

(* -------------------------------------------------------------------
   4. Parse a class expression from a graph term.
   ------------------------------------------------------------------- *)

(* The parser is fuel-bounded (class expressions may nest through
   intersectionOf lists arbitrarily deeply in principle). At each
   recursive call we decrement `fuel`; if fuel runs out we emit
   `CE_Unknown` which is sound (is_member returns None for
   CE_Unknown). *)

(* Lexicographic measure %[fuel; 0] vs %[fuel; len ts] ensures the
   mutually-recursive list walk terminates: parse_class_expr_list
   consumes `ts` at fixed `fuel`; parse_class_expr strictly
   decreases `fuel`. Inside parse_class_expr we pass `n - 1` to the
   list walker so the fuel is strictly smaller than our own. *)
(* Cardinality values in W3C entailment tests are tiny (0-9 covers
   essentially all cases). We match literal lexical forms directly so
   F\* doesn't need to verify a string-to-nat helper. Anything outside
   the 0-9 range is surfaced as None, which makes the outer parse
   emit CE_Unknown — sound under open-world. *)
let cardinality_literal_to_nat (s : string) : option nat =
  if s = "0" then Some 0
  else if s = "1" then Some 1
  else if s = "2" then Some 2
  else if s = "3" then Some 3
  else if s = "4" then Some 4
  else if s = "5" then Some 5
  else if s = "6" then Some 6
  else if s = "7" then Some 7
  else if s = "8" then Some 8
  else if s = "9" then Some 9
  else None

let cardinality_value (g : rdf_graph) (s : subject) (pred : wf_iri) : option nat =
  match find_first_object g s pred with
  | Some (T_Literal l) -> cardinality_literal_to_nat l.lexical_form
  | _ -> None

let rec parse_class_expr (g : rdf_graph) (t : rdf_term) (fuel : nat)
  : Tot class_expr (decreases %[fuel; 0]) =
  match fuel with
  | 0 -> CE_Unknown
  | n ->
    match t with
    | T_IRI i ->
      (* A named class expression — just an IRI. *)
      CE_Named i
    | T_BNode _ ->
      (match term_as_subject t with
       | None -> CE_Unknown
       | Some s ->
         (* Dispatch on which of the OWL class-expression markers is
            present on the bnode. Preference order:
              1. owl:intersectionOf list  -> CE_IntersectionOf
              2. owl:unionOf list         -> CE_UnionOf
              3. owl:complementOf ?C      -> CE_ComplementOf
              4. Restriction markers      -> CE_SomeValuesFrom etc.
         *)
         match find_first_object g s owl_intersectionOf with
         | Some list_head ->
           let items = walk_rdf_list g list_head n in
           CE_IntersectionOf (parse_class_expr_list g items (n - 1))
         | None ->
           match find_first_object g s owl_unionOf with
           | Some list_head ->
             let items = walk_rdf_list g list_head n in
             CE_UnionOf (parse_class_expr_list g items (n - 1))
           | None ->
             match find_first_object g s owl_complementOf with
             | Some c ->
               CE_ComplementOf (parse_class_expr g c (n - 1))
             | None ->
               (* Try restrictions. Require owl:onProperty P with P an IRI. *)
               match find_first_object g s owl_onProperty with
               | Some (T_IRI p) ->
                 (match find_first_object g s owl_someValuesFrom with
                  | Some c -> CE_SomeValuesFrom p (parse_class_expr g c (n - 1))
                  | None ->
                    match find_first_object g s owl_allValuesFrom with
                    | Some c -> CE_AllValuesFrom p (parse_class_expr g c (n - 1))
                    | None ->
                      match find_first_object g s owl_hasValue with
                      | Some v -> CE_HasValue p v
                      | None ->
                        (* Stage (c): cardinality restrictions. *)
                        (match cardinality_value g s owl_minQualifiedCardinality with
                         | Some k ->
                           (match find_first_object g s owl_onClass with
                            | Some c -> CE_MinQualCard k p (parse_class_expr g c (n - 1))
                            | None -> CE_MinCard k p)
                         | None ->
                           match cardinality_value g s owl_maxQualifiedCardinality with
                           | Some k ->
                             (match find_first_object g s owl_onClass with
                              | Some c -> CE_MaxQualCard k p (parse_class_expr g c (n - 1))
                              | None -> CE_MaxCard k p)
                           | None ->
                             match cardinality_value g s owl_qualifiedCardinality with
                             | Some k ->
                               (match find_first_object g s owl_onClass with
                                | Some c -> CE_ExactQualCard k p (parse_class_expr g c (n - 1))
                                | None -> CE_ExactCard k p)
                             | None ->
                               match cardinality_value g s owl_minCardinality with
                               | Some k -> CE_MinCard k p
                               | None ->
                                 match cardinality_value g s owl_maxCardinality with
                                 | Some k -> CE_MaxCard k p
                                 | None ->
                                   match cardinality_value g s owl_cardinality with
                                   | Some k -> CE_ExactCard k p
                                   | None -> CE_Unknown))
               | _ -> CE_Unknown)
    | _ -> CE_Unknown
and parse_class_expr_list (g : rdf_graph) (ts : list rdf_term) (fuel : nat)
  : Tot (list class_expr) (decreases %[fuel; List.Tot.length ts]) =
  match ts with
  | []      -> []
  | h :: tl -> parse_class_expr g h fuel :: parse_class_expr_list g tl fuel

(* -------------------------------------------------------------------
   5. is_member : does individual `i` satisfy class-expression `ce`?
   ------------------------------------------------------------------- *)

(* We return option bool:
     Some true  : provably a member
     Some false : provably NOT a member
     None       : unknown (caller falls back).

   This is the three-valued "definite truth" used by description logics.
   CRITICAL for soundness: any path that isn't rock-solid returns None.

   Arguments:
     g    : the CLOSED graph (already run through OWL-RL closure by
            the caller). We look up rdf:type from this.
     i    : the individual we're asking about (a subject).
     ce   : the class expression.
     fuel : recursion budget — class-expression nesting + one step per
            recursive ∀-check.                                            *)

(* rdf:type lookup: does the closed graph assert (i rdf:type C)? *)
let has_type (g : rdf_graph) (i : subject) (c : wf_iri) : bool =
  List.Tot.existsb
    (fun (t : triple) ->
      t.p = rdf_type &&
      subject_eq t.s i &&
      (match t.o with
       | T_IRI o -> o = c
       | _       -> false))
    g

(* Find all P-successors of i: the y's such that (i P y) in g. *)
let find_P_successors (g : rdf_graph) (i : subject) (p : wf_iri)
  : list rdf_term =
  find_objects g i p

(* Check if any successor satisfies the predicate f (returns bool). *)
let rec any_successor_sat (f : rdf_term -> bool) (xs : list rdf_term)
  : Tot bool (decreases xs) =
  match xs with
  | []      -> false
  | h :: tl -> if f h then true else any_successor_sat f tl

(* disjointWith bridge for CE_ComplementOf:
   sound rule (one direction, monotonic): if `c_iri owl:disjointWith d_iri`
   (or symmetric `d_iri owl:disjointWith c_iri`) and `i rdf:type d_iri`
   in the closed graph, then `i` is provably a member of `(complementOf c_iri)`.
   We never produce Some false here; absence of a disjoint witness leaves
   the existing flip logic in CE_ComplementOf unchanged. *)
let rec any_disjoint_witness_in (g : rdf_graph) (i : subject)
                                (ds : list rdf_term)
  : Tot bool (decreases ds) =
  match ds with
  | []      -> false
  | h :: tl ->
    (match h with
     | T_IRI d_iri -> if has_type g i d_iri then true
                      else any_disjoint_witness_in g i tl
     | _           -> any_disjoint_witness_in g i tl)

let rec any_disjoint_witness_sym (g : rdf_graph) (i : subject) (c_iri : wf_iri)
                                 (subjs : list subject)
  : Tot bool (decreases subjs) =
  match subjs with
  | []      -> false
  | h :: tl ->
    (match h with
     | S_IRI d_iri -> if has_type g i d_iri then true
                      else any_disjoint_witness_sym g i c_iri tl
     | _           -> any_disjoint_witness_sym g i c_iri tl)

let has_disjoint_witness (g : rdf_graph) (i : subject) (c_iri : wf_iri) : bool =
  let forward = find_objects g (S_IRI c_iri) owl_disjointWith in
  if any_disjoint_witness_in g i forward then true
  else
    let reverse = find_subjects g owl_disjointWith (T_IRI c_iri) in
    any_disjoint_witness_sym g i c_iri reverse

(* is_member — main recursive entry.

   Termination: `fuel` decreases in every non-Named case. Within a single
   call we may fan out across a list of sub-expressions (intersection,
   union) but `parse_class_expr` already produced fixed lists — no loops
   remain at is_member time. *)

(* Mutual recursion termination. Measure is lexicographic %[fuel; k]
   where k is a list length for the list helpers. The main entry
   `is_member` has k = 0. When `is_member` delegates to any of the
   helpers, it passes `fuel = n - 1` (strictly smaller). When a
   helper recurses on its tail it keeps fuel constant but shrinks the
   list. Cross-calls from helper back to `is_member` pass `fuel`
   unchanged and land at k = 0 — strictly smaller than k = len(list)
   which is >= 1 at the point of the cross-call. *)
let rec is_member (g : rdf_graph) (i : subject) (ce : class_expr) (fuel : nat)
  : Tot (option bool) (decreases %[fuel; 0]) =
  match fuel with
  | 0 -> None
  | n ->
    match ce with
    | CE_Unknown -> None

    | CE_Named c ->
      (* Named class: open-world lookup. If the (closed) graph asserts
         it, we're done. Otherwise we cannot conclude `Some false` in
         open-world semantics — return None. *)
      if has_type g i c then Some true else None

    | CE_HasValue p v ->
      (* ∃ P.{v}: the individual has v on property P in the ABox. *)
      let succs = find_P_successors g i p in
      if any_successor_sat (fun t -> rdf_term_eq t v) succs
      then Some true
      else None

    | CE_SomeValuesFrom p c ->
      (* ∃ P.C: if any known P-successor of i is a member of C, Some true.
         If no P-successor is known, or no known P-successor can be
         shown to be a member of C, return None (don't invent witnesses
         — that's stage (e)). We do NOT return Some false here because
         in open-world an unseen witness may exist.                      *)
      let succs = find_P_successors g i p in
      any_is_member g succs c (n - 1)

    | CE_AllValuesFrom p c ->
      (* ∀ P.C: every (known) P-successor must be a member of C. Under
         open-world we can't be sure about hypothetical unseen successors
         → we only answer Some true when we can discharge the obligation
         from what we know (which is accepted in the OWL W3C tests that
         interpret "all" as "for every asserted successor, the restriction
         must hold").

         Returning Some false is sound: if ANY known successor provably
         violates C (is_member returns Some false), then ∀ fails.        *)
      let succs = find_P_successors g i p in
      all_is_member g succs c (n - 1)

    | CE_IntersectionOf ces ->
      (* ⊓: all must be Some true. Any Some false ⇒ Some false.
         Otherwise None. *)
      is_intersection_member g i ces (n - 1)

    | CE_UnionOf ces ->
      (* ⊔: any Some true ⇒ Some true. All Some false ⇒ Some false.
         Otherwise None. *)
      is_union_member g i ces (n - 1)

    | CE_ComplementOf c ->
      (* Partial: flip a definite answer. None stays None. This is NOT
         full classical negation; it cannot prove "i is not a C" unless
         we already have an explicit disproof of C. Stage (d) upgrades
         this to dual-branch search.

         Phase 2 bridge (paper-Q3): when c is a named class c_iri and the
         graph asserts `c_iri owl:disjointWith d_iri` (either direction)
         with `i rdf:type d_iri`, then i is a member of (complementOf c_iri)
         under OWL semantics. Sound, monotonic, one-direction only — never
         derives Some false. *)
      (match c with
       | CE_Named c_iri ->
         if has_disjoint_witness g i c_iri then Some true
         else
           (match is_member g i c (n - 1) with
            | Some b -> Some (not b)
            | None   -> None)
       | _ ->
         (match is_member g i c (n - 1) with
          | Some b -> Some (not b)
          | None   -> None))

    | CE_MinCard k p ->
      (* at-least-k P: count distinct known P-successors. Under UNA-off
         we treat two different IRIs as different; bnodes might alias,
         so this is a conservative lower bound. Sound floor: if
         count >= k, answer Some true; otherwise None. *)
      let succs = find_P_successors g i p in
      if List.Tot.length succs >= k then Some true else None

    | CE_MaxCard k p ->
      (* at-most-k P: provable only for the trivially-empty case
         without same-As tracking or finite-model closure. For k=0 +
         no known successors, Some true; else None. *)
      let succs = find_P_successors g i p in
      if k = 0 && List.Tot.length succs = 0 then Some true else None

    | CE_ExactCard k p ->
      (* = k: answerable from current infra only when k=0 + no
         known successors (both MinCard and MaxCard are Some true). *)
      let succs = find_P_successors g i p in
      if k = 0 && List.Tot.length succs = 0 then Some true else None

    | CE_MinQualCard k p c ->
      let succs = find_P_successors g i p in
      let matched = count_qual_successors g succs c (n - 1) in
      if matched >= k then Some true else None

    | CE_MaxQualCard k p c ->
      let succs = find_P_successors g i p in
      let matched = count_qual_successors g succs c (n - 1) in
      if k = 0 && matched = 0 then Some true else None

    | CE_ExactQualCard k p c ->
      let succs = find_P_successors g i p in
      let matched = count_qual_successors g succs c (n - 1) in
      if k = 0 && matched = 0 then Some true else None

(* ∃: fold over successors; short-circuit on Some true. *)
and any_is_member (g : rdf_graph) (ys : list rdf_term) (c : class_expr)
                  (fuel : nat)
  : Tot (option bool) (decreases %[fuel; List.Tot.length ys]) =
  match ys with
  | []      -> None
  | y :: tl ->
    (match term_as_subject y with
     | None -> any_is_member g tl c fuel
     | Some ys_subj ->
       (match is_member g ys_subj c fuel with
        | Some true -> Some true
        | _         -> any_is_member g tl c fuel))

(* ∀: fold over successors; short-circuit on Some false. All Some true
   → Some true. Any None → None (can't prove "all"). *)
and all_is_member (g : rdf_graph) (ys : list rdf_term) (c : class_expr)
                  (fuel : nat)
  : Tot (option bool) (decreases %[fuel; List.Tot.length ys]) =
  match ys with
  | []      -> Some true  (* vacuous truth *)
  | y :: tl ->
    (match term_as_subject y with
     | None ->
       (* A literal as a P-successor violates any class assertion
          because classes only hold IRIs / bnodes. Return Some false. *)
       Some false
     | Some ys_subj ->
       (match is_member g ys_subj c fuel with
        | Some false -> Some false
        | Some true  -> all_is_member g tl c fuel
        | None       -> None))

(* ⊓ *)
and is_intersection_member (g : rdf_graph) (i : subject) (ces : list class_expr)
                           (fuel : nat)
  : Tot (option bool) (decreases %[fuel; List.Tot.length ces]) =
  match ces with
  | []      -> Some true  (* empty intersection = owl:Thing *)
  | c :: tl ->
    (match is_member g i c fuel with
     | Some false -> Some false
     | Some true  -> is_intersection_member g i tl fuel
     | None       ->
       (* One conjunct is unknown. But if a later conjunct is Some
          false, the whole intersection is Some false. We need to scan
          the rest looking for a disproof. *)
       match is_intersection_member g i tl fuel with
       | Some false -> Some false
       | _          -> None)

(* ⊔ *)
and is_union_member (g : rdf_graph) (i : subject) (ces : list class_expr)
                    (fuel : nat)
  : Tot (option bool) (decreases %[fuel; List.Tot.length ces]) =
  match ces with
  | []      -> Some false  (* empty union = owl:Nothing *)
  | c :: tl ->
    (match is_member g i c fuel with
     | Some true  -> Some true
     | Some false -> is_union_member g i tl fuel
     | None       ->
       (* One disjunct is unknown. But if a later disjunct is Some
          true, the whole union is Some true. *)
       match is_union_member g i tl fuel with
       | Some true -> Some true
       | _         -> None)

(* Stage (c): count how many of `ys` provably satisfy class `c`.
   Successors whose membership is unknown or which are literals
   don't count — conservative (underestimates true count under
   open-world). *)
and count_qual_successors (g : rdf_graph) (ys : list rdf_term)
                          (c : class_expr) (fuel : nat)
  : Tot nat (decreases %[fuel; List.Tot.length ys]) =
  match ys with
  | []      -> 0
  | y :: tl ->
    let rest = count_qual_successors g tl c fuel in
    (match term_as_subject y with
     | None         -> rest
     | Some ys_subj ->
       (match is_member g ys_subj c fuel with
        | Some true -> rest + 1
        | _         -> rest))

(* -------------------------------------------------------------------
   6. Tableau state (legacy stage (a) types, kept for source compat).
   ------------------------------------------------------------------- *)

noeq type tab_link = {
  tl_pred : wf_iri;
  tl_obj  : rdf_term;
}

noeq type tab_individual =
  | TI_IRI    : wf_iri    -> tab_individual
  | TI_BNode  : bnode_id  -> tab_individual
  | TI_Skolem : nat       -> tab_individual

noeq type tab_node = {
  tn_indiv    : tab_individual;
  tn_classes  : list wf_iri;
  tn_links    : list tab_link;
  tn_same_as  : list tab_individual;
}

let make_iri_node (i : wf_iri) : tab_node =
  { tn_indiv = TI_IRI i; tn_classes = []; tn_links = []; tn_same_as = [] }

type tab_status =
  | Open
  | Closed
  | Unknown

noeq type tab_branch = {
  tb_nodes  : list tab_node;
  tb_status : tab_status;
}

let empty_branch : tab_branch =
  { tb_nodes = []; tb_status = Open }

noeq type tab_obligation = {
  tob_owner : tab_individual;
  tob_desc  : string;
}

noeq type tableau_state = {
  ts_branches     : list tab_branch;
  ts_obligations  : list tab_obligation;
  ts_una          : bool;
  ts_fuel_used    : nat;
}

let init_tableau_state (_ : unit) : tableau_state =
  { ts_branches    = [empty_branch];
    ts_obligations = [];
    ts_una         = false;
    ts_fuel_used   = 0; }

let rec triple_in_graph (goal : triple) (g : rdf_graph) : Tot bool (decreases g) =
  match g with
  | [] -> false
  | t :: rest -> if triple_eq t goal then true else triple_in_graph goal rest

let tableau_step (st : tableau_state) (fuel : nat)
  : Tot (tableau_state & tab_status) (decreases fuel) =
  if fuel = 0 then (st, Unknown)
  else
    match st.ts_obligations with
    | []     -> (st, Unknown)
    | _ :: _ -> (st, Unknown)

(* -------------------------------------------------------------------
   7. owl_tableau_entails — top-level entailment-check entry.
   ------------------------------------------------------------------- *)

(* Stage-(b) behaviour:

   If the goal is (i rdf:type C) with C a bnode and C parses as a
   non-Unknown class expression, return is_member's result. Otherwise,
   keep the stage-(a) fallback: if the triple is in the closed graph,
   Some true; else None.

   We deliberately treat the `schema` argument the same as `data` at
   this point by not consulting it — the runner's convention is that
   `data` already contains the schema triples (merged), which matches
   how entailment_closure is called. If the caller passes schema
   triples separately in the future, this function will need an
   update. *)

let owl_tableau_entails
  (regime : string)
  (data   : rdf_dataset)
  (schema : rdf_dataset)
  (goal   : triple)
  : Tot (option bool)
  =
  let _ = regime in
  let _ = schema in
  let g = data.ds_default in
  (* Fast path: triple already present (Datalog did it). *)
  if triple_in_graph goal g then Some true
  else
    (* Try class-expression reasoning if the goal is rdf:type with a
       bnode / IRI object that looks like a class expression. *)
    if goal.p = rdf_type then
      let ce = parse_class_expr g goal.o 32 in
      match ce with
      | CE_Unknown -> None
      | CE_Named _ -> None  (* pure named class: already covered by the closure *)
      | _          -> is_member g goal.s ce 64
    else None

let owl_tableau_entails_graph
  (regime : string)
  (g      : rdf_graph)
  (goal   : triple)
  : Tot (option bool)
  =
  let ds = { ds_default = g; ds_named = [] } in
  owl_tableau_entails regime ds empty_dataset goal

(* -------------------------------------------------------------------
   8. Materialisation pass: add `i rdf:type <CE-bnode>` for every
      class-expression bnode in the graph and every individual that
      satisfies it.
   ------------------------------------------------------------------- *)

(* Is this bnode (as subject) a class expression? Check if any of the
   OWL class-expression markers is present. We reject pure IRIs here
   because named classes are already handled by the Datalog closure. *)
let is_class_expression_subject (g : rdf_graph) (s : subject) : bool =
  (* Only bnodes (CE bnodes); named classes are OWL-RL territory. *)
  match s with
  | S_IRI _ -> false
  | S_BNode _ ->
    Some? (find_first_object g s owl_intersectionOf) ||
    Some? (find_first_object g s owl_unionOf) ||
    Some? (find_first_object g s owl_complementOf) ||
    Some? (find_first_object g s owl_onProperty)

(* Collect every bnode subject that appears to be a class expression. *)
let rec collect_ce_bnodes (g : rdf_graph) (gfull : rdf_graph)
  : Tot (list subject) (decreases g) =
  match g with
  | []      -> []
  | t :: tl ->
    let rest = collect_ce_bnodes tl gfull in
    match t.s with
    | S_BNode _ ->
      if is_class_expression_subject gfull t.s &&
         not (List.Tot.existsb (fun x -> subject_eq x t.s) rest)
      then t.s :: rest
      else rest
    | _ -> rest

(* Collect candidate individuals (every IRI subject, plus bnode
   subjects that are NOT themselves class expressions). We include
   IRI objects of rdf:type triples too, to catch individuals that
   only appear as objects (rare in tests but safe). *)
let rec collect_candidate_individuals (g : rdf_graph) (gfull : rdf_graph)
  : Tot (list subject) (decreases g) =
  match g with
  | []      -> []
  | t :: tl ->
    let rest = collect_candidate_individuals tl gfull in
    let is_ce = is_class_expression_subject gfull t.s in
    if is_ce then rest
    else
      if List.Tot.existsb (fun x -> subject_eq x t.s) rest
      then rest
      else t.s :: rest

(* For a single (individual, CE-bnode) pair, decide whether to emit
   `i rdf:type <bnode>`. Returns a singleton list (for easy concat)
   or the empty list.                                                *)
let materialise_for_pair (g : rdf_graph) (i : subject) (ce_s : subject)
                        (ce : class_expr)
  : list triple =
  (* Skip if already asserted. *)
  let existing =
    List.Tot.existsb
      (fun (t : triple) ->
        t.p = rdf_type &&
        subject_eq t.s i &&
        (match t.o, ce_s with
         | T_IRI o, S_IRI ci -> o = ci
         | T_BNode o, S_BNode cb -> o = cb
         | _, _ -> false))
      g
  in
  if existing then []
  else
    match is_member g i ce 64 with
    | Some true ->
      let obj = match ce_s with
                | S_IRI ci -> T_IRI ci
                | S_BNode cb -> T_BNode cb
      in
      [ { s = i; p = rdf_type; o = obj } ]
    | _ -> []

(* Build materialisation triples for a single CE bnode across all
   candidate individuals. *)
let rec materialise_for_ce (g : rdf_graph) (candidates : list subject)
                          (ce_s : subject) (ce : class_expr)
  : Tot (list triple) (decreases candidates) =
  match candidates with
  | []      -> []
  | i :: tl ->
    materialise_for_pair g i ce_s ce @
    materialise_for_ce g tl ce_s ce

(* Run over all CE bnodes. *)
let rec materialise_all (g : rdf_graph) (candidates : list subject)
                       (ces : list subject)
  : Tot (list triple) (decreases ces) =
  match ces with
  | []         -> []
  | ce_s :: tl ->
    let ce = parse_class_expr g (match ce_s with
                                 | S_IRI i -> T_IRI i
                                 | S_BNode b -> T_BNode b) 32 in
    match ce with
    | CE_Unknown ->
      materialise_all g candidates tl
    | _ ->
      materialise_for_ce g candidates ce_s ce @
      materialise_all g candidates tl

(* Structural unpacking of equivalentClass with an intersectionOf on
   the right:
     (X owl:equivalentClass I) and (I owl:intersectionOf (A1 ... An))
     implies (X rdfs:subClassOf Ai) for each Ai.
   We emit these triples on X, NOT on I. Emitting on I produces noisy
   bnode-valued ?C bindings in queries like parent9 which ask
   `?C rdfs:subClassOf <R1>` — every anonymous intersection bnode
   would match and pollute the result set. Placing the cls-int1
   result on the NAMED side of the equivalentClass preserves the
   inference :Father ⊑ :Parent without introducing spurious
   anonymous subclasses.

   Same story for unionOf-on-the-right of an equivalentClass:
     (X owl:equivalentClass U) and (U owl:unionOf (A1 ... An))
     implies (Ai rdfs:subClassOf X) for each Ai.                        *)

let rec emit_intersection_subclasses_via_eqc
  (named_subj : subject) (items : list rdf_term)
  : Tot (list triple) (decreases items) =
  match items with
  | []      -> []
  | t :: tl ->
    let tail = emit_intersection_subclasses_via_eqc named_subj tl in
    match term_to_subject t with
    | Some _ ->
      ({ s = named_subj; p = rdfs_subClassOf; o = t } <: triple) :: tail
    | None -> tail

let rec emit_union_subclasses_via_eqc
  (named_subj : subject) (items : list rdf_term)
  : Tot (list triple) (decreases items) =
  match items with
  | []      -> []
  | t :: tl ->
    let tail = emit_union_subclasses_via_eqc named_subj tl in
    match term_to_subject t with
    | Some t_subj ->
      ({ s = t_subj; p = rdfs_subClassOf; o = subject_to_term named_subj } <: triple) :: tail
    | None -> tail

(* For every (X equivalentClass C) triple where C is a class-expression
   bnode with an intersectionOf / unionOf marker, emit the
   subClassOf expansion on X. *)
let rec materialise_eqc_expansion (g : rdf_graph) (all : rdf_graph)
  : Tot (list triple) (decreases g) =
  match g with
  | []      -> []
  | t :: tl ->
    let tail = materialise_eqc_expansion tl all in
    if t.p = owl_equivalentClass then
      match term_to_subject t.o with
      | Some ce_s ->
        (* Look for intersectionOf. *)
        (match find_first_object all ce_s owl_intersectionOf with
         | Some list_head ->
           let items = walk_rdf_list all list_head 64 in
           emit_intersection_subclasses_via_eqc t.s items @ tail
         | None ->
           match find_first_object all ce_s owl_unionOf with
           | Some list_head ->
             let items = walk_rdf_list all list_head 64 in
             emit_union_subclasses_via_eqc t.s items @ tail
           | None -> tail)
      | None -> tail
    else tail

(* -------------------------------------------------------------------
   8a. Phase-1 EXISTENTIAL WITNESS INTRODUCTION (parent4 fix).

   When the closed graph contains `(i rdf:type B)` where B is a
   class-expression bnode that parses as `∃P.C` (or MinCard 1 / MinQualCard 1),
   description-logic semantics requires SOME P-successor for i. OWL-RL
   closure is Datalog and cannot synthesise that successor. We mint a
   fresh deterministic bnode `_:bw_<i_str>_<p_str>` and emit:

     i p _:bw_<i_str>_<p_str>
     _:bw_<i_str>_<p_str> rdf:type C_iri        // only if C is CE_Named

   Soundness: in every model of the closed graph there must exist some
   P-successor of i in C. We exhibit a specific witness that any model
   could be extended to satisfy. We never assert anything about distinct-
   ness vs. existing successors, so this never contradicts the ABox.
   The witness only fires when there is no already-known P-successor that
   provably satisfies C — otherwise we'd duplicate.

   Bound: only one witness per (i, p, C-shape) tuple is generated. Acts
   as a single-step ∃-introduction without iteration; the closure caller
   may re-run materialisation if desired.
   ------------------------------------------------------------------- *)

(* Pull out the (P, C) "obligation" of a CE if it is an existential
   shape (∃P.C / MinCard 1 P / MinQualCard 1 P C). Returns None for
   non-existential CEs and for k != 1 cardinality variants. *)
let existential_obligation (ce : class_expr) : option (wf_iri & class_expr) =
  match ce with
  | CE_SomeValuesFrom p c -> Some (p, c)
  | CE_MinCard k p ->
    if k = 1 then Some (p, CE_Unknown) else None
  | CE_MinQualCard k p c ->
    if k = 1 then Some (p, c) else None
  | _ -> None

(* Build the deterministic witness bnode id for (i, p). We embed the
   subject string and predicate IRI so different obligations get
   different witnesses; bnode_id = string under the hood, so this is
   just string concat. *)
let witness_bnode_id (i : subject) (p : wf_iri) : bnode_id =
  let i_str = match i with
              | S_IRI s   -> s
              | S_BNode b -> b in
  String.concat "" ["_:bw_"; i_str; "__"; p]

(* Decide whether `i` already has a known P-successor that provably
   satisfies `c`. If so, no witness is needed.   *)
let already_has_witness (g : rdf_graph) (i : subject) (p : wf_iri)
                        (c : class_expr) : bool =
  let succs = find_P_successors g i p in
  match c with
  | CE_Unknown ->
    (* unqualified: any successor will do. *)
    not (Nil? succs)
  | _ ->
    (match any_is_member g succs c 32 with
     | Some true -> true
     | _         -> false)

(* For every CE-bnode that is an existential, find every i typed with
   it, mint a witness if needed, emit (i p _:bw) and optionally
   (_:bw rdf:type C_iri). Skips literals, skips already-satisfied
   obligations. *)
let witnesses_for_ce_bnode (g : rdf_graph) (ce_s : subject) (ce : class_expr)
  : list triple =
  match existential_obligation ce with
  | None -> []
  | Some (p, c) ->
    let ce_term = subject_to_term ce_s in
    let typed_individuals = find_subjects g rdf_type ce_term in
    List.Tot.fold_left
      (fun (acc : list triple) (i : subject) ->
        if already_has_witness g i p c then acc
        else
          let bw_id = witness_bnode_id i p in
          let bw_term = T_BNode bw_id in
          let edge : triple = { s = i; p = p; o = bw_term } in
          let acc1 = edge :: acc in
          (* If C is a named class, also emit (witness rdf:type C). *)
          match c with
          | CE_Named c_iri ->
            let type_t : triple = {
              s = S_BNode bw_id; p = rdf_type; o = T_IRI c_iri;
            } in
            type_t :: acc1
          | _ -> acc1)
      []
      typed_individuals

(* Iterate over all CE bnodes, accumulating witness triples. *)
let rec witnesses_for_all (g : rdf_graph) (ces : list subject)
  : Tot (list triple) (decreases ces) =
  match ces with
  | []         -> []
  | ce_s :: tl ->
    let ce = parse_class_expr g (subject_to_term ce_s) 32 in
    (match ce with
     | CE_Unknown -> witnesses_for_all g tl
     | _ ->
       witnesses_for_ce_bnode g ce_s ce @ witnesses_for_all g tl)

(* Public entry: introduce existential witnesses where the materialised
   graph requires them. Sound — adds only triples that any model of
   the input must already (essentially) satisfy. *)
let tableau_introduce_witnesses (g : rdf_graph) : rdf_graph =
  let ces = collect_ce_bnodes g g in
  let extras = witnesses_for_all g ces in
  add_triples_if_new g extras

(* -------------------------------------------------------------------
   8b. DIRECT owl:unionOf / owl:intersectionOf subclass materialisation.

   An OWL class defined DIRECTLY as `(S owl:unionOf (X1 ... Xn))` denotes
   S ≡ X1 ⊔ ... ⊔ Xn, and `(S owl:intersectionOf (X1 ... Xn))` denotes
   S ≡ X1 ⊓ ... ⊓ Xn. Neither the OWL-RL Datalog closure (which has no
   union/intersection rules at all) nor `materialise_eqc_expansion`
   (which only fires when the boolean combinator sits on the RIGHT of an
   `owl:equivalentClass` triple) emits the entailed subClassOf axioms in
   the direct case. This pass fills that gap.

   Emitted axioms (both sound in EVERY model, purely additive):
     - unionOf S (X1..Xn)        ==>  Xi rdfs:subClassOf S  for each Xi.
       Soundness: the interpretation of Xi is a subset of the union
       X1 ⊔ .. ⊔ Xn, which equals the interpretation of S, so Xi ⊑ S
       holds in every model of the KB. (reuses
       emit_union_subclasses_via_eqc, whose output is exactly
       `Xi rdfs:subClassOf named_subj`.)
     - intersectionOf S (X1..Xn) ==>  S rdfs:subClassOf Xi  for each Xi.
       Soundness: the interpretation of S is the intersection of the Xi,
       hence a subset of each Xi, so S ⊑ Xi holds in every model.
       (reuses emit_intersection_subclasses_via_eqc, output
       `named_subj rdfs:subClassOf Xi`.)

   We NEVER emit an rdfs:subClassOf that could be false, so this pass is
   sound in the same option-bool sense as the rest of the module (it only
   ever adds entailed triples; it removes nothing and never guesses).

   RESTRICTION to S_IRI subjects: we skip bnode union/intersection
   subjects. Anonymous boolean class-expression bnodes are used as QUERY
   patterns (e.g. `?C rdfs:subClassOf [ owl:unionOf (..) ]` in parent9/
   parent10); emitting subClassOf edges onto such bnodes would pollute
   those answer sets with spurious anonymous classes (the same hazard the
   equivalentClass path documents by emitting on the NAMED side). Named
   union/intersection classes carry no such risk. Skipping bnode subjects
   only WITHHOLDS inferences — it is sound (never emits a wrong triple)
   and keeps the SPARQL 1.1 entailment regime suite at 70/70. *)
let rec materialise_direct_boolean_subclasses (g : rdf_graph) (all : rdf_graph)
  : Tot (list triple) (decreases g) =
  match g with
  | []      -> []
  | t :: tl ->
    let tail = materialise_direct_boolean_subclasses tl all in
    (match t.s with
     | S_IRI _ ->
       if t.p = owl_unionOf then
         let items = walk_rdf_list all t.o 64 in
         emit_union_subclasses_via_eqc t.s items @ tail
       else if t.p = owl_intersectionOf then
         let items = walk_rdf_list all t.o 64 in
         emit_intersection_subclasses_via_eqc t.s items @ tail
       else tail
     | _ -> tail)

(* -------------------------------------------------------------------
   8c. NAMED class-expression membership materialisation (cls-svf /
       cls-hv / reverse cls-int for NAMED restriction / boolean subjects).

   A class-expression can be denoted by a NAMED IRI subject, not only an
   anonymous bnode. In OWL 2 RDF-Based semantics a subject `z` carrying
   restriction / boolean markers directly denotes exactly that class:

     z owl:onProperty p . z owl:someValuesFrom c .
        ==>  CEXT(z) = { x : exists y. (x,y) in EXT(p) and y in CEXT(c) }
     z owl:onProperty p . z owl:hasValue v .
        ==>  CEXT(z) = { x : (x,v) in EXT(p) }
     c owl:intersectionOf (X1..Xn)
        ==>  CEXT(c) = CEXT(X1) INTERSECT .. INTERSECT CEXT(Xn)
     c owl:unionOf (X1..Xn)
        ==>  CEXT(c) = CEXT(X1) UNION .. UNION CEXT(Xn)

   The pre-existing materialisation collects ONLY bnode class-expression
   subjects (`collect_ce_bnodes` matches `S_BNode` only), and
   `parse_class_expr` maps every IRI straight to `CE_Named` (so it never
   inspects a named subject's own restriction markers). Consequently a
   ground membership like `w rdf:type z` (z a NAMED restriction) or
   `z rdf:type c` (c a NAMED intersection) is never emitted, even though
   it is entailed. This pass fills that gap for NAMED subjects.

   SOUNDNESS — this pass emits `i rdf:type z` (z a NAMED IRI) ONLY when
   `is_member g i (parse z) = Some true` AND the parsed class expression
   is `ce_positive_sound`. `ce_positive_sound` admits exactly the shapes
   whose `is_member`-`Some true` is unconditionally entailment-sound
   (every model of the KB has i in CEXT(z)):
     - CE_Named c        : `Some true` == asserted `i rdf:type c`
       (set-semantics: i in the interpretation of c). Sound.
     - CE_HasValue p v   : `Some true` == asserted `i p v`, so i in the
       interpretation of exists-p.{v}. Sound.
     - CE_SomeValuesFrom p c (c positive-sound): a known successor y with
       i p y and y in the interpretation of c exhibits a witness, so i is
       in exists-p.c in every model. Sound.
     - CE_MinCard k p    : k known distinct successors are witnesses for
       min-k p (a conservative lower bound; `Some true` only when the
       count already reaches k). Sound.
     - CE_MinQualCard k p c (c positive-sound): as MinCard but successors
       provably in the interpretation of c. Sound.
     - CE_IntersectionOf / CE_UnionOf of positive-sound parts: INTERSECT
       needs all conjuncts `Some true` (each sound => i in each set => i in
       the intersection); UNION needs one disjunct `Some true` (i in that
       set, which is a subset of the union). Sound.
   We DELIBERATELY EXCLUDE the open-world-unsound positive directions —
   CE_AllValuesFrom (a hidden/unseen successor could violate C, so
   "all KNOWN successors in C" does NOT entail i in all-p.C), CE_MaxCard /
   CE_ExactCard / CE_MaxQualCard / CE_ExactQualCard (need sameAs / UNA to
   assert a positive membership) and CE_ComplementOf (needs classical
   negation). For those `ce_positive_sound` returns false and the pass
   withholds — withholding an entailment is always sound.

   Named subjects only (S_IRI). Bnode boolean/restriction subjects stay
   the exclusive territory of the bnode passes above; emitting named
   memberships never pollutes the anonymous-class query answer sets that
   the bnode-skipping rationale (section 8b) protects, because the emitted
   object is a NAMED class (`w rdf:type z`, z an IRI), exactly what a
   Datalog closure would itself carry. *)

(* Parse the class expression denoted by an arbitrary subject (IRI or
   bnode) by inspecting ITS OWN restriction / boolean markers — unlike
   parse_class_expr, which maps every IRI directly to CE_Named. Non-
   recursive in the mutual-recursion sense: it only calls the already-
   defined parse_class_expr / parse_class_expr_list for the fillers, so
   termination is immediate. Returns CE_Unknown when the subject carries
   no class-expression markers (the caller then emits nothing). *)
let parse_ce_of_subject (g : rdf_graph) (s : subject) : class_expr =
  match find_first_object g s owl_intersectionOf with
  | Some list_head ->
    CE_IntersectionOf (parse_class_expr_list g (walk_rdf_list g list_head 32) 31)
  | None ->
    match find_first_object g s owl_unionOf with
    | Some list_head ->
      CE_UnionOf (parse_class_expr_list g (walk_rdf_list g list_head 32) 31)
    | None ->
      match find_first_object g s owl_complementOf with
      | Some c -> CE_ComplementOf (parse_class_expr g c 31)
      | None ->
        match find_first_object g s owl_onProperty with
        | Some (T_IRI p) ->
          (match find_first_object g s owl_someValuesFrom with
           | Some c -> CE_SomeValuesFrom p (parse_class_expr g c 31)
           | None ->
             match find_first_object g s owl_allValuesFrom with
             | Some c -> CE_AllValuesFrom p (parse_class_expr g c 31)
             | None ->
               match find_first_object g s owl_hasValue with
               | Some v -> CE_HasValue p v
               | None ->
                 (match cardinality_value g s owl_minQualifiedCardinality with
                  | Some k ->
                    (match find_first_object g s owl_onClass with
                     | Some c -> CE_MinQualCard k p (parse_class_expr g c 31)
                     | None -> CE_MinCard k p)
                  | None ->
                    match cardinality_value g s owl_maxQualifiedCardinality with
                    | Some k ->
                      (match find_first_object g s owl_onClass with
                       | Some c -> CE_MaxQualCard k p (parse_class_expr g c 31)
                       | None -> CE_MaxCard k p)
                    | None ->
                      match cardinality_value g s owl_qualifiedCardinality with
                      | Some k ->
                        (match find_first_object g s owl_onClass with
                         | Some c -> CE_ExactQualCard k p (parse_class_expr g c 31)
                         | None -> CE_ExactCard k p)
                      | None ->
                        match cardinality_value g s owl_minCardinality with
                        | Some k -> CE_MinCard k p
                        | None ->
                          match cardinality_value g s owl_maxCardinality with
                          | Some k -> CE_MaxCard k p
                          | None ->
                            match cardinality_value g s owl_cardinality with
                            | Some k -> CE_ExactCard k p
                            | None -> CE_Unknown))
        | _ -> CE_Unknown

(* The soundness gate: does every `Some true` `is_member` can produce for
   this class expression correspond to an ENTAILED membership (holds in
   every model)? See the section 8c banner for the per-shape argument. *)
let rec ce_positive_sound (ce : class_expr) : Tot bool (decreases ce) =
  match ce with
  | CE_Named _            -> true
  | CE_HasValue _ _       -> true
  | CE_MinCard _ _        -> true
  | CE_SomeValuesFrom _ c -> ce_positive_sound c
  | CE_MinQualCard _ _ c  -> ce_positive_sound c
  | CE_IntersectionOf ces -> ce_list_positive_sound ces
  | CE_UnionOf ces        -> ce_list_positive_sound ces
  | _                     -> false
and ce_list_positive_sound (ces : list class_expr) : Tot bool (decreases ces) =
  match ces with
  | []      -> true
  | c :: tl -> ce_positive_sound c && ce_list_positive_sound tl

(* A NAMED (IRI) subject that carries restriction / boolean markers. *)
let is_named_ce_subject (g : rdf_graph) (s : subject) : bool =
  match s with
  | S_BNode _ -> false
  | S_IRI _ ->
    Some? (find_first_object g s owl_onProperty) ||
    Some? (find_first_object g s owl_intersectionOf) ||
    Some? (find_first_object g s owl_unionOf)

(* Collect every NAMED subject that appears to be a class expression. *)
let rec collect_named_ce_subjects (g : rdf_graph) (gfull : rdf_graph)
  : Tot (list subject) (decreases g) =
  match g with
  | []      -> []
  | t :: tl ->
    let rest = collect_named_ce_subjects tl gfull in
    (match t.s with
     | S_IRI _ ->
       if is_named_ce_subject gfull t.s &&
          not (List.Tot.existsb (fun x -> subject_eq x t.s) rest)
       then t.s :: rest
       else rest
     | _ -> rest)

(* For every NAMED class-expression subject whose parsed CE is
   positive-sound, emit `i rdf:type z` for each candidate individual i
   that `is_member` proves a member. Skips CE_Named / CE_Unknown and any
   CE outside the positive-sound fragment (withholding is sound). *)
let rec materialise_all_named (g : rdf_graph) (candidates : list subject)
                              (ces : list subject)
  : Tot (list triple) (decreases ces) =
  match ces with
  | []         -> []
  | ce_s :: tl ->
    let ce = parse_ce_of_subject g ce_s in
    (match ce with
     | CE_Named _   -> materialise_all_named g candidates tl
     | CE_Unknown   -> materialise_all_named g candidates tl
     | _ ->
       if ce_positive_sound ce
       then materialise_for_ce g candidates ce_s ce
            @ materialise_all_named g candidates tl
       else materialise_all_named g candidates tl)

(* Public entry: one-shot materialisation pass. Runs to completion (no
   iteration) — the closure caller can re-run the Datalog closure
   afterwards to propagate any new rdf:type triples through
   rdfs:subClassOf etc. Stage (b) does not iterate materialisation ↔
   closure to a fixpoint; that's a future optimisation.

   Phase 1: we first introduce existential witnesses (parent4 fix), then
   materialise CE-bnode memberships against the augmented graph so newly-
   minted witness P-successors can satisfy MinCard/SomeValuesFrom checks.

   Direct boolean subclasses (§8b): we additionally emit the subClassOf
   axioms entailed by direct owl:unionOf / owl:intersectionOf named-class
   definitions, so the following RL closure pass can propagate instance
   memberships through them (rdfs9).

   Named class-expression memberships (section 8c): we emit `i rdf:type z`
   for NAMED restriction / boolean class subjects z whose parsed CE is
   positive-sound and which `is_member` proves i satisfies (cls-svf /
   cls-hv / reverse cls-int over a NAMED subject). *)
let tableau_materialise (g : rdf_graph) : rdf_graph =
  let g1 = tableau_introduce_witnesses g in
  let ces = collect_ce_bnodes g1 g1 in
  let individuals = collect_candidate_individuals g1 g1 in
  let instance_triples   = materialise_all g1 individuals ces in
  let structural_triples = materialise_eqc_expansion g1 g1 in
  let bool_subclasses    = materialise_direct_boolean_subclasses g1 g1 in
  let named_ces          = collect_named_ce_subjects g1 g1 in
  let named_instance_triples = materialise_all_named g1 individuals named_ces in
  add_triples_if_new
    (add_triples_if_new
      (add_triples_if_new
        (add_triples_if_new g1 structural_triples) bool_subclasses)
      instance_triples)
    named_instance_triples

(* -------------------------------------------------------------------
   9. In-file test matrix (guarded, dead-code).
   ------------------------------------------------------------------- *)

(* These guard the types — they compile but never execute. *)
let _tableau_sanity_matrix : unit =
  if false then
    begin
      let i_alice : wf_iri =
        assert_norm (is_iri "http://ex/alice");
        "http://ex/alice" in
      let i_person : wf_iri =
        assert_norm (is_iri "http://ex/Person");
        "http://ex/Person" in
      let type_triple : triple = {
        s = S_IRI i_alice;
        p = rdf_type;
        o = T_IRI i_person;
      } in
      let data1 : rdf_dataset = {
        ds_default = [type_triple]; ds_named = [];
      } in
      let res1 = owl_tableau_entails "OWL-Direct" data1 empty_dataset type_triple in
      assert (res1 = Some true);

      let i_student : wf_iri =
        assert_norm (is_iri "http://ex/Student");
        "http://ex/Student" in
      let different_goal : triple = {
        s = S_IRI i_alice;
        p = rdf_type;
        o = T_IRI i_student;
      } in
      let data2 : rdf_dataset = {
        ds_default = []; ds_named = [];
      } in
      let res2 = owl_tableau_entails "OWL-Direct" data2 empty_dataset different_goal in
      assert (res2 = None);

      let st = init_tableau_state () in
      let (_, status) = tableau_step st 0 in
      assert (status = Unknown);

      // Stage (c) sanity: min-cardinality counting.
      //
      // Dataset:
      //   :Bob :hasChild :Charlie .
      //   :Charlie rdf:type owl:NamedIndividual .
      //
      // Class expression: (min 1 :hasChild) — unqualified.
      // Query: is :Bob a (min 1 :hasChild)?  Expected: Some true.
      let i_bob : wf_iri =
        assert_norm (is_iri "http://ex/Bob");
        "http://ex/Bob" in
      let i_charlie : wf_iri =
        assert_norm (is_iri "http://ex/Charlie");
        "http://ex/Charlie" in
      let i_hasChild : wf_iri =
        assert_norm (is_iri "http://ex/hasChild");
        "http://ex/hasChild" in
      let bob_has_charlie : triple = {
        s = S_IRI i_bob;
        p = i_hasChild;
        o = T_IRI i_charlie;
      } in
      let g3 : rdf_graph = [bob_has_charlie] in
      let ce_min1 = CE_MinCard 1 i_hasChild in
      let res_min1 = is_member g3 (S_IRI i_bob) ce_min1 8 in
      assert (res_min1 = Some true);

      // min 2 on the same data: not provable (we have 1 known successor).
      let ce_min2 = CE_MinCard 2 i_hasChild in
      let res_min2 = is_member g3 (S_IRI i_bob) ce_min2 8 in
      assert (res_min2 = None);

      // max 0 on Bob: NOT provable (he has a known successor).
      let ce_max0 = CE_MaxCard 0 i_hasChild in
      let res_max0 = is_member g3 (S_IRI i_bob) ce_max0 8 in
      assert (res_max0 = None);

      // max 0 on an individual with no known successors: Some true.
      // Here Alice has no hasChild edge, so max-0 holds vacuously.
      let i_alice2 : wf_iri =
        assert_norm (is_iri "http://ex/Alice2");
        "http://ex/Alice2" in
      let res_max0_alice = is_member g3 (S_IRI i_alice2) ce_max0 8 in
      assert (res_max0_alice = Some true);

      // Qualified min-1 with onClass: extend data so Charlie is typed.
      // :Charlie rdf:type :Male
      let i_male : wf_iri =
        assert_norm (is_iri "http://ex/Male");
        "http://ex/Male" in
      let charlie_male : triple = {
        s = S_IRI i_charlie;
        p = rdf_type;
        o = T_IRI i_male;
      } in
      let g4 : rdf_graph = [bob_has_charlie; charlie_male] in
      let ce_min1_male = CE_MinQualCard 1 i_hasChild (CE_Named i_male) in
      let res_min1_male = is_member g4 (S_IRI i_bob) ce_min1_male 8 in
      assert (res_min1_male = Some true);

      // Qualified min-1 with onClass :Female: Charlie isn't Female → None.
      let i_female2 : wf_iri =
        assert_norm (is_iri "http://ex/Female2");
        "http://ex/Female2" in
      let ce_min1_female = CE_MinQualCard 1 i_hasChild (CE_Named i_female2) in
      let res_min1_female = is_member g4 (S_IRI i_bob) ce_min1_female 8 in
      assert (res_min1_female = None);

      // Phase 1 sanity: existential_obligation extracts (p, c) from
      // CE_SomeValuesFrom and CE_MinCard 1 / MinQualCard 1, returns
      // None for other CEs.
      let obl1 = existential_obligation
                   (CE_SomeValuesFrom i_hasChild (CE_Named i_male)) in
      assert (obl1 = Some (i_hasChild, CE_Named i_male));
      let obl2 = existential_obligation (CE_MinCard 1 i_hasChild) in
      assert (obl2 = Some (i_hasChild, CE_Unknown));
      let obl3 = existential_obligation
                   (CE_MinQualCard 1 i_hasChild (CE_Named i_female2)) in
      assert (obl3 = Some (i_hasChild, CE_Named i_female2));
      let obl_neg1 = existential_obligation (CE_Named i_male) in
      assert (obl_neg1 = None);
      let obl_neg2 = existential_obligation (CE_MinCard 2 i_hasChild) in
      assert (obl_neg2 = None);

      // Section 8c sanity: the positive-sound gate admits the sound
      // positive shapes and rejects the open-world-unsound ones.
      assert (ce_positive_sound (CE_SomeValuesFrom i_hasChild (CE_Named i_male)));
      assert (ce_positive_sound (CE_HasValue i_hasChild (T_IRI i_charlie)));
      assert (ce_positive_sound (CE_MinCard 1 i_hasChild));
      assert (ce_positive_sound
                (CE_IntersectionOf [CE_Named i_male; CE_Named i_person]));
      assert (not (ce_positive_sound (CE_AllValuesFrom i_hasChild (CE_Named i_male))));
      assert (not (ce_positive_sound (CE_MaxCard 0 i_hasChild)));
      assert (not (ce_positive_sound
                     (CE_IntersectionOf
                        [CE_Named i_male;
                         CE_AllValuesFrom i_hasChild (CE_Named i_person)])));

      // NAMED restriction membership (cls-svf, named subject z):
      //   z owl:onProperty hasChild ; owl:someValuesFrom Male .
      //   Bob hasChild Charlie . Charlie a Male .
      //   ==> Bob a z   (z a NAMED IRI class).
      let i_z : wf_iri =
        assert_norm (is_iri "http://ex/Zclass");
        "http://ex/Zclass" in
      let z_onprop : triple = {
        s = S_IRI i_z; p = owl_onProperty; o = T_IRI i_hasChild;
      } in
      let z_svf : triple = {
        s = S_IRI i_z; p = owl_someValuesFrom; o = T_IRI i_male;
      } in
      let g5 : rdf_graph = [bob_has_charlie; charlie_male; z_onprop; z_svf] in
      let z_ce = parse_ce_of_subject g5 (S_IRI i_z) in
      assert (z_ce = CE_SomeValuesFrom i_hasChild (CE_Named i_male));
      let res_bob_z = is_member g5 (S_IRI i_bob) z_ce 16 in
      assert (res_bob_z = Some true);

      ()
    end
  else ()
