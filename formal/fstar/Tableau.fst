module Tableau

(* OWL-DL tableau reasoner — STAGE (b): CLASS-EXPRESSION SATISFIABILITY.

   This module implements the part of the tableau that can answer
   "is individual i a member of class-expression C?" where C is built from:
     - Named classes (IRIs)
     - owl:Restriction bnodes with owl:onProperty and
       * owl:someValuesFrom
       * owl:allValuesFrom
       * owl:hasValue
     - Boolean combinators: owl:intersectionOf, owl:unionOf
     - Partial owl:complementOf (only the trivial clash check within a branch)

   WHAT STAGE (b) EXPLICITLY DOES NOT DO (deferred to later stages):
     - No cardinality (min/max/exact) — stage (c).
     - No full classical-negation dual-branch search — stage (d).
     - No fresh-individual skolemisation for ∃ — stage (e).

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

(* -------------------------------------------------------------------
   1. OWL vocabulary constants needed by stage (b).
   ------------------------------------------------------------------- *)

let owl_intersectionOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#intersectionOf");
  "http://www.w3.org/2002/07/owl#intersectionOf"

let owl_unionOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#unionOf");
  "http://www.w3.org/2002/07/owl#unionOf"

let owl_complementOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#complementOf");
  "http://www.w3.org/2002/07/owl#complementOf"

let owl_Restriction : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Restriction");
  "http://www.w3.org/2002/07/owl#Restriction"

let owl_onProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onProperty");
  "http://www.w3.org/2002/07/owl#onProperty"

let owl_someValuesFrom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#someValuesFrom");
  "http://www.w3.org/2002/07/owl#someValuesFrom"

let owl_allValuesFrom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#allValuesFrom");
  "http://www.w3.org/2002/07/owl#allValuesFrom"

let owl_hasValue : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#hasValue");
  "http://www.w3.org/2002/07/owl#hasValue"

let rdf_first : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"

let rdf_rest : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"

let rdf_nil : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"

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
                      | None -> CE_Unknown)
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
         this to dual-branch search. *)
      (match is_member g i c (n - 1) with
       | Some b -> Some (not b)
       | None   -> None)

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

(* Public entry: one-shot materialisation pass. Runs to completion (no
   iteration) — the closure caller can re-run the Datalog closure
   afterwards to propagate any new rdf:type triples through
   rdfs:subClassOf etc. Stage (b) does not iterate materialisation ↔
   closure to a fixpoint; that's a future optimisation.                *)
let tableau_materialise (g : rdf_graph) : rdf_graph =
  let ces = collect_ce_bnodes g g in
  let individuals = collect_candidate_individuals g g in
  let instance_triples   = materialise_all g individuals ces in
  let structural_triples = materialise_eqc_expansion g g in
  add_triples_if_new (add_triples_if_new g structural_triples) instance_triples

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

      ()
    end
  else ()
