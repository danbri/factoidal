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

let shnex_intersection : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#intersection");
  "http://www.w3.org/ns/shacl-node-expr#intersection"

let shnex_remove : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#remove");
  "http://www.w3.org/ns/shacl-node-expr#remove"

let shnex_flatMap : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#flatMap");
  "http://www.w3.org/ns/shacl-node-expr#flatMap"

let shnex_orderBy : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#orderBy");
  "http://www.w3.org/ns/shacl-node-expr#orderBy"

let shnex_desc : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#desc");
  "http://www.w3.org/ns/shacl-node-expr#desc"

let shnex_filterShape : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#filterShape");
  "http://www.w3.org/ns/shacl-node-expr#filterShape"

let shnex_matchAll : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#matchAll");
  "http://www.w3.org/ns/shacl-node-expr#matchAll"

let shnex_findFirst : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#findFirst");
  "http://www.w3.org/ns/shacl-node-expr#findFirst"

let shnex_nodesMatching : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl-node-expr#nodesMatching");
  "http://www.w3.org/ns/shacl-node-expr#nodesMatching"

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

// shnex:instancesOf C -> the subjects that are rdf:type C, INCLUDING
// instances of subclasses of C (rdfs:subClassOf closure, via
// shacl_class_closure which materialises inferred rdf:type triples).
let instances_of (g : rdf_graph) (c : wf_iri) : list rdf_term =
  let closed = shacl_class_closure g (graph_len g + 20) in
  dedup_terms (List.Tot.map subject_to_term (find_subjects closed rdf_type (T_IRI c)))

// Does value node `v` conform to the shape denoted by `shape_term`
// (an IRI/blank-node shape reference resolved against `g`)? Reuses the
// SHACL.Validation conformance judgment (empty violation list = conforms).
// An unresolvable / non-shape reference conforms vacuously. Used by
// shnex:filterShape / matchAll / findFirst / nodesMatching.
let node_conforms (g : rdf_graph) (shape_term : rdf_term) (v : rdf_term) : bool =
  match term_to_shape_ref shape_term with
  | None -> true
  | Some r ->
    let sg = (parse_shape_from_graph_pure g).shapes in
    (match lookup_shape r sg with
     | None -> true
     | Some sh ->
       let closed_cls = shacl_class_closure g (graph_len g + 20) in
       Nil? (collect_shape_violations g sg closed_cls v sh (graph_len g + 100)))

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

// Term membership by structural RDF-term equality (shnex remove /
// intersection compare TERMS, not values: "01"^^xsd:integer is NOT the
// same term as "1"^^xsd:integer even though value-equal).
let rec term_mem (t : rdf_term) (l : list rdf_term) : Tot bool (decreases l) =
  match l with [] -> false | h :: r -> rdf_term_eq t h || term_mem t r

// Ordering for shnex:orderBy sort keys: numeric when both are integer
// literals; otherwise treated as equal (stable / no reorder), which
// covers the suite's integer orderBy fixtures.
let term_cmp (a b : rdf_term) : int =
  match parse_int_term a, parse_int_term b with
  | Some x, Some y -> if x < y then (-1) else if x > y then 1 else 0
  | _, _ -> 0

// --- the evaluator ---------------------------------------------------

#push-options "--z3rlimit 300"
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
    // A shnex:focusNode on THIS node overrides the start node(s) for its
    // pathValues (constant, or a nested expression evaluated against the
    // ambient focus); absent it, the ambient focus is the start.
    let start_nodes : list rdf_term =
      (match find_objects g es shnex_focusNode with
       | (fe :: _) -> eval_ne g focus scope fe fuel'
       | [] -> (match focus with Some f -> [f] | None -> [])) in
    let base : list rdf_term =
      match find_objects g es shnex_var with
      | (T_Literal l) :: _ ->
        if l.lexical_form = "focusNode"
        then (match focus with Some f -> [f] | None -> [])
        else (match List.Tot.find (fun (n, _) -> n = l.lexical_form) scope with
              | Some (_, t) -> [t] | None -> [])
      | _ ->
      (match find_objects g es shnex_pathValues with
       | (p :: _) -> List.Tot.concatMap (fun st -> eval_path g st (parse_path g p fuel')) start_nodes
       | [] ->
      (match find_objects g es shnex_nodes with
       // shnex:nodes takes ONE node expression (often a bare rdf:List,
       // which itself evaluates to its members) — not a list of exprs.
       | (l :: _) -> eval_ne g focus scope l fuel'
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
      (match find_objects g es shnex_intersection with
       | (l :: _) -> dedup_terms (eval_ne_intersect g focus scope (rdf_list_terms g l fuel') fuel')
       | [] ->
      (match find_objects g es shnex_nodesMatching with
       | (s :: _) -> dedup_terms (List.Tot.filter (fun v -> node_conforms g s v)
                                    (List.Tot.map subject_to_term (distinct_subjects g)))
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
          | [] -> (match expr with T_BNode _ -> [] | _ -> [expr])))))))))))))))
    in
    // Modifiers apply after the generator: flatMap (per-element re-focus),
    // remove (set difference by term), then offset/limit slicing.
    let after_flatmap =
      (match find_objects g es shnex_flatMap with
       | (m :: _) -> eval_ne_flatmap g scope m base fuel'
       | [] -> base) in
    let after_remove =
      (match find_objects g es shnex_remove with
       | (r :: _) -> let rm = eval_ne g focus scope r fuel' in
                     List.Tot.filter (fun x -> not (term_mem x rm)) after_flatmap
       | [] -> after_flatmap) in
    let after_orderby =
      (match find_objects g es shnex_orderBy with
       | (k :: _) ->
         let desc = (match first_bool (find_objects g es shnex_desc) with Some true -> true | _ -> false) in
         let keyed = eval_ne_keyed g scope k after_remove fuel' in
         let sorted = List.Tot.sortWith (fun (p1 : (rdf_term & rdf_term)) (p2 : (rdf_term & rdf_term)) -> term_cmp (snd p1) (snd p2)) keyed in
         let ordered = List.Tot.map (fun (p : (rdf_term & rdf_term)) -> fst p) sorted in
         if desc then List.Tot.rev ordered else ordered
       | [] -> after_remove) in
    // Conformance modifiers (SHACL 1.2 shnex): filterShape keeps the
    // source elements that conform to a shape; matchAll reduces to a
    // single boolean (do ALL conform?); findFirst yields the first
    // conforming element.
    let after_filter =
      (match find_objects g es shnex_filterShape with
       | (s :: _) -> List.Tot.filter (fun v -> node_conforms g s v) after_orderby
       | [] -> after_orderby) in
    let after_matchall =
      (match find_objects g es shnex_matchAll with
       | (s :: _) -> [ mk_bool_lit (List.Tot.for_all (fun v -> node_conforms g s v) after_filter) ]
       | [] -> after_filter) in
    let after_findfirst =
      (match find_objects g es shnex_findFirst with
       | (s :: _) -> (match List.Tot.find (fun v -> node_conforms g s v) after_matchall with Some v -> [v] | None -> [])
       | [] -> after_matchall) in
    let after_offset = (match first_int (find_objects g es shnex_offset) with Some n -> list_drop n after_findfirst | None -> after_findfirst) in
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

// shnex:intersection: evaluate each member expression separately and
// keep only the terms present in ALL of them (term equality).
and eval_ne_intersect (g : rdf_graph) (focus : option rdf_term) (scope : list (string & rdf_term))
                      (members : list rdf_term) (fuel : nat)
  : Tot (list rdf_term) (decreases %[fuel; 1; List.Tot.length members])
  =
  match members with
  | [] -> []
  | [m] -> eval_ne g focus scope m fuel
  | m :: rest ->
    let hd = eval_ne g focus scope m fuel in
    let tl = eval_ne_intersect g focus scope rest fuel in
    List.Tot.filter (fun x -> term_mem x tl) hd

// shnex:flatMap: for each element of the source, re-evaluate the mapper
// expression with that element as the focus node, concatenating results.
and eval_ne_flatmap (g : rdf_graph) (scope : list (string & rdf_term))
                    (mapper : rdf_term) (elems : list rdf_term) (fuel : nat)
  : Tot (list rdf_term) (decreases %[fuel; 1; List.Tot.length elems])
  =
  match elems with
  | [] -> []
  | el :: rest -> eval_ne g (Some el) scope mapper fuel @ eval_ne_flatmap g scope mapper rest fuel

// shnex:orderBy: pair each source element with its sort key (the key
// expression re-evaluated with that element as focus; the element
// itself when the key is empty), for a subsequent sortWith.
and eval_ne_keyed (g : rdf_graph) (scope : list (string & rdf_term))
                  (keyexpr : rdf_term) (elems : list rdf_term) (fuel : nat)
  : Tot (list (rdf_term & rdf_term)) (decreases %[fuel; 1; List.Tot.length elems])
  =
  match elems with
  | [] -> []
  | el :: rest ->
    let k = (match eval_ne g (Some el) scope keyexpr fuel with kk :: _ -> kk | [] -> el) in
    (el, k) :: eval_ne_keyed g scope keyexpr rest fuel
#pop-options

// Entry point for the runner: evaluate `expr` against `g` with an
// optional focus node and a variable scope, returning the value list.
let eval_node_expr_top (g : rdf_graph) (focus : option rdf_term)
                       (scope : list (string & rdf_term)) (expr : rdf_term)
  : list rdf_term
  = eval_ne g focus scope expr (graph_len g + 100)
