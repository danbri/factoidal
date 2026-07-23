module SHACL.NodeExpr

/// SHACL 1.2 node expressions (SHACL-AF section 5 / the `shnex`
/// vocabulary). A node expression is an RDF subgraph that, given a
/// focus node and a variable scope, EVALUATES to a list of RDF terms.
/// The W3C shacl12 `node-expr` suite drives these directly via
/// `sht:EvalNodeExpr` test entries (evaluate the expression, compare
/// the result list to `mf:result`).
///
/// The evaluator interprets the expression node straight off the graph
/// (no separate parse step): it looks at which `shnex:` predicate the
/// expression node carries and dispatches. Fuel bounds the recursion
/// (expression graphs may be cyclic / malformed).
///
/// This is a CONSUMER of the SHACL.Validation core (path evaluation,
/// rdf:List extraction, dedup) — it opens that module and reuses its
/// verified helpers rather than duplicating them. Phase 1 covers the
/// generator + simple-aggregate forms; the per-element-focus forms
/// (orderBy / filterShape / flatMap / intersection / min / max / sum /
/// the match* / find* / remove family) land in a follow-up.

open FStar.List.Tot
open RDF.Graph.Executable
open SHACL.Validation

module Alg = SPARQL11.Algebra

// --- shnex vocabulary ------------------------------------------------

let shnex_ns : string = "http://www.w3.org/ns/shacl-node-expr#"

let shnex_focusNode : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#focusNode");
  "http://www.w3.org/ns/shacl-node-expr#focusNode"

let shnex_pathValues : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#pathValues");
  "http://www.w3.org/ns/shacl-node-expr#pathValues"

let shnex_nodes : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#nodes");
  "http://www.w3.org/ns/shacl-node-expr#nodes"

let shnex_concat : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#concat");
  "http://www.w3.org/ns/shacl-node-expr#concat"

let shnex_count : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#count");
  "http://www.w3.org/ns/shacl-node-expr#count"

let shnex_distinct : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#distinct");
  "http://www.w3.org/ns/shacl-node-expr#distinct"

let shnex_exists : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#exists");
  "http://www.w3.org/ns/shacl-node-expr#exists"

let shnex_if : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#if");
  "http://www.w3.org/ns/shacl-node-expr#if"

let shnex_then : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#then");
  "http://www.w3.org/ns/shacl-node-expr#then"

let shnex_else : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#else");
  "http://www.w3.org/ns/shacl-node-expr#else"

let shnex_var : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#var");
  "http://www.w3.org/ns/shacl-node-expr#var"

let shnex_instancesOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#instancesOf");
  "http://www.w3.org/ns/shacl-node-expr#instancesOf"

let shnex_sum : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#sum");
  "http://www.w3.org/ns/shacl-node-expr#sum"

let shnex_min : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#min");
  "http://www.w3.org/ns/shacl-node-expr#min"

let shnex_max : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#max");
  "http://www.w3.org/ns/shacl-node-expr#max"

let shnex_limit : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#limit");
  "http://www.w3.org/ns/shacl-node-expr#limit"

let shnex_offset : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#offset");
  "http://www.w3.org/ns/shacl-node-expr#offset"

// --- small helpers ---------------------------------------------------

let mk_int_lit (n : int) : rdf_term =
  T_Literal ({ lexical_form = string_of_int n; datatype = xsd_integer;
               lang_tag = None; direction = None })

let mk_bool_lit (b : bool) : rdf_term =
  T_Literal ({ lexical_form = (if b then "true" else "false"); datatype = xsd_boolean;
               lang_tag = None; direction = None })

// Effective boolean value of an expression result: a leading boolean
// literal decides directly; otherwise a non-empty list is truthy.
let ne_ebv (l : list rdf_term) : bool =
  match l with
  | (T_Literal lit) :: _ -> if lit.datatype = xsd_boolean then lit.lexical_form = "true" else true
  | []                   -> false
  | _                    -> true

let rec list_drop (n : nat) (l : list rdf_term) : Tot (list rdf_term) (decreases l) =
  match n, l with
  | 0, _ -> l
  | _, [] -> []
  | _, _ :: tl -> list_drop (n - 1) tl

let rec list_take (n : nat) (l : list rdf_term) : Tot (list rdf_term) (decreases l) =
  match n, l with
  | 0, _ -> []
  | _, [] -> []
  | _, hd :: tl -> hd :: list_take (n - 1) tl

// shnex:instancesOf C -> the subjects that are rdf:type C in the graph.
let instances_of (g : rdf_graph) (c : wf_iri) : list rdf_term =
  dedup_terms (List.Tot.map subject_to_term (find_subjects g rdf_type (T_IRI c)))

// --- numeric aggregates (integer-valued; decimal/double deferred) -----

let parse_int_term (t : rdf_term) : option int =
  match t with
  | T_Literal l -> if l.datatype = xsd_integer then Alg.parse_int_string l.lexical_form else None
  | _ -> None

// Some [n1;..] iff every term is an xsd:integer literal; None otherwise
// (so a decimal/double member makes the whole aggregate bow out cleanly
// rather than compute a wrong integer result).
let rec ints_of (l : list rdf_term) : Tot (option (list int)) (decreases l) =
  match l with
  | [] -> Some []
  | h :: r -> (match parse_int_term h, ints_of r with
               | Some n, Some ns -> Some (n :: ns)
               | _, _ -> None)

let sum_expr (vals : list rdf_term) : list rdf_term =
  match ints_of vals with
  | Some ns -> [ mk_int_lit (List.Tot.fold_left (fun a b -> a + b) 0 ns) ]
  | None -> []

let rec max_int (ns : list int) (acc : int) : Tot int (decreases ns) =
  match ns with [] -> acc | h :: r -> max_int r (if h > acc then h else acc)
let rec min_int (ns : list int) (acc : int) : Tot int (decreases ns) =
  match ns with [] -> acc | h :: r -> min_int r (if h < acc then h else acc)

let max_expr (vals : list rdf_term) : list rdf_term =
  match ints_of vals with Some (h :: t) -> [ mk_int_lit (max_int t h) ] | _ -> []
let min_expr (vals : list rdf_term) : list rdf_term =
  match ints_of vals with Some (h :: t) -> [ mk_int_lit (min_int t h) ] | _ -> []

// --- the evaluator ---------------------------------------------------

#push-options "--z3rlimit 150"
let rec eval_ne (g : rdf_graph) (focus : option rdf_term) (scope : list (string & rdf_term))
                (expr : rdf_term) (fuel : nat)
  : Tot (list rdf_term) (decreases %[fuel; 0; 0])
  =
  if fuel = 0 then [] else
  let fuel' : nat = fuel - 1 in
  match term_to_subject expr with
  // A literal (or triple term) is a constant expression -> itself.
  | None -> [expr]
  | Some es ->
    let base : list rdf_term =
      if Cons? (find_objects g es shnex_focusNode)
      then (match focus with Some f -> [f] | None -> [])
      else
      match find_objects g es shnex_var with
      | (T_Literal l) :: _ ->
        if l.lexical_form = "focusNode"
        then (match focus with Some f -> [f] | None -> [])
        else (match List.Tot.find (fun (n, _) -> n = l.lexical_form) scope with
              | Some (_, t) -> [t] | None -> [])
      | _ ->
      (match find_objects g es shnex_pathValues with
       | (p :: _) -> (match focus with Some f -> eval_path g f (parse_path g p fuel') | None -> [])
       | [] ->
      (match find_objects g es shnex_nodes with
       | (l :: _) -> eval_ne_list g focus scope (rdf_list_terms g l fuel') fuel'
       | [] ->
      (match find_objects g es shnex_concat with
       | (l :: _) -> eval_ne_list g focus scope (rdf_list_terms g l fuel') fuel'
       | [] ->
      (match find_objects g es shnex_distinct with
       | (e :: _) -> dedup_terms (eval_ne g focus scope e fuel')
       | [] ->
      (match find_objects g es shnex_count with
       | (e :: _) -> [ mk_int_lit (List.Tot.length (eval_ne g focus scope e fuel')) ]
       | [] ->
      (match find_objects g es shnex_exists with
       | (e :: _) -> [ mk_bool_lit (Cons? (eval_ne g focus scope e fuel')) ]
       | [] ->
      (match find_objects g es shnex_if with
       | (c :: _) ->
         if ne_ebv (eval_ne g focus scope c fuel')
         then (match find_objects g es shnex_then with (t :: _) -> eval_ne g focus scope t fuel' | [] -> [])
         else (match find_objects g es shnex_else with (e :: _) -> eval_ne g focus scope e fuel' | [] -> [])
       | [] ->
      (match find_objects g es shnex_sum with
       | (e :: _) -> sum_expr (eval_ne g focus scope e fuel')
       | [] ->
      (match find_objects g es shnex_min with
       | (e :: _) -> min_expr (eval_ne g focus scope e fuel')
       | [] ->
      (match find_objects g es shnex_max with
       | (e :: _) -> max_expr (eval_ne g focus scope e fuel')
       | [] ->
      (match find_objects g es shnex_instancesOf with
       | (T_IRI c) :: _ -> instances_of g c
       | _ ->
         // No shnex function predicate. A blank node may still be a bare
         // rdf:List node expression (its members are sub-expressions, e.g.
         // `( 1 2 3 )` -> [1;2;3]) or an EMPTY expression `[]` -> []. An
         // IRI (incl. rdf:nil from `()`) or literal is a constant -> itself.
         (match find_objects g es rdf_first with
          | (_ :: _) -> eval_ne_list g focus scope (rdf_list_terms g expr fuel') fuel'
          | [] -> (match expr with T_BNode _ -> [] | _ -> [expr])))))))))))))
    in
    // Slicing modifiers apply after the generator.
    let after_offset = (match first_int (find_objects g es shnex_offset) with Some n -> list_drop n base | None -> base) in
    (match first_int (find_objects g es shnex_limit) with Some n -> list_take n after_offset | None -> after_offset)

// Evaluate each expression in `es` and concatenate the results (order
// preserved). Mutually recursive with eval_ne; the lexicographic
// measure %[fuel; _; length] lets eval_ne recurse into the list at a
// smaller fuel while the list walk decreases on its own length.
and eval_ne_list (g : rdf_graph) (focus : option rdf_term) (scope : list (string & rdf_term))
                 (es : list rdf_term) (fuel : nat)
  : Tot (list rdf_term) (decreases %[fuel; 1; List.Tot.length es])
  =
  match es with
  | [] -> []
  | e :: rest -> eval_ne g focus scope e fuel @ eval_ne_list g focus scope rest fuel
#pop-options

// Entry point for the runner: evaluate `expr` against `g` with an
// optional focus node and a variable scope, returning the value list.
let eval_node_expr_top (g : rdf_graph) (focus : option rdf_term)
                       (scope : list (string & rdf_term)) (expr : rdf_term)
  : list rdf_term
  = eval_ne g focus scope expr (graph_len g + 100)
