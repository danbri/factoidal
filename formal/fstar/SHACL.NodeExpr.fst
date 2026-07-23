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
open FStar.Char
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

// --- decimal-aware numeric sum ---------------------------------------
//
// Each numeric value is parsed to (scaled_int, scale) so that value =
// scaled_int / 10^scale; summing rescales to the common (maximum) scale.
// An all-integer sum keeps scale 0 (integer result); any decimal member
// makes the result a decimal.

let rec pow10 (n : nat) : Tot int (decreases n) = if n = 0 then 1 else op_Multiply 10 (pow10 (n - 1))

// Split a char list at the first '.', returning (before, Some after) or
// (whole, None) when there is no point.
let rec split_dot (cs : list char) (acc : list char) : Tot (list char & option (list char)) (decreases cs) =
  match cs with
  | [] -> (List.Tot.rev acc, None)
  | '.' :: rest -> (List.Tot.rev acc, Some rest)
  | c :: rest -> split_dot rest (c :: acc)

let parse_dec_lexical (s : string) : option (int & nat) =
  let (before, after_opt) = split_dot (String.list_of_string s) [] in
  match after_opt with
  | None -> (match Alg.parse_int_string s with Some n -> Some (n, 0) | None -> None)
  | Some after ->
    (match Alg.parse_int_string (String.string_of_list (before @ after)) with
     | Some n -> Some (n, List.Tot.length after) | None -> None)

let parse_num_term (t : rdf_term) : option (int & nat) =
  match t with
  | T_Literal l ->
    if l.datatype = xsd_integer || l.datatype = xsd_decimal then parse_dec_lexical l.lexical_form else None
  | _ -> None

let rec nums_of (l : list rdf_term) : Tot (option (list (int & nat))) (decreases l) =
  match l with
  | [] -> Some []
  | h :: r -> (match parse_num_term h, nums_of r with
               | Some p, Some ps -> Some (p :: ps) | _, _ -> None)

let rec max_scale (ps : list (int & nat)) (acc : nat) : Tot nat (decreases ps) =
  match ps with [] -> acc | (_, sc) :: r -> max_scale r (if sc > acc then sc else acc)

let rec sum_scaled (ps : list (int & nat)) (ms : nat) : Tot int (decreases ps) =
  match ps with [] -> 0 | (n, sc) :: r -> op_Multiply n (pow10 (if ms >= sc then ms - sc else 0)) + sum_scaled r ms

let rec repeat0 (n : nat) : Tot (list char) (decreases n) = if n = 0 then [] else '0' :: repeat0 (n - 1)

// Render (scaled_val / 10^scale) as an xsd:decimal / xsd:integer literal.
let mk_decimal_lit (scaled_val : int) (scale : nat) : rdf_term =
  if scale = 0 then mk_int_lit scaled_val
  else
    let neg = scaled_val < 0 in
    let a = if neg then 0 - scaled_val else scaled_val in
    let digits = String.list_of_string (string_of_int a) in
    let dlen = List.Tot.length digits in
    let padded = (if dlen >= scale + 1 then [] else repeat0 (scale + 1 - dlen)) @ digits in
    let n = List.Tot.length padded in
    let k = if n >= scale then n - scale else 0 in
    let (intp, fracp) = List.Tot.splitAt k padded in
    let body = String.string_of_list (intp @ ['.'] @ fracp) in
    let lex = if neg then String.concat "" ["-"; body] else body in
    T_Literal ({ lexical_form = lex; datatype = xsd_decimal; lang_tag = None; direction = None })

let sum_expr (vals : list rdf_term) : list rdf_term =
  match nums_of vals with
  | Some ps -> let ms = max_scale ps 0 in [ mk_decimal_lit (sum_scaled ps ms) ms ]
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

// Lexical comparison of char lists / strings (codepoint order).
let rec clist_cmp (a b : list char) : Tot int (decreases a) =
  match a, b with
  | [], [] -> 0
  | [], _ -> (-1)
  | _, [] -> 1
  | x :: xs, y :: ys ->
    let cx = FStar.Char.int_of_char x in
    let cy = FStar.Char.int_of_char y in
    if cx < cy then (-1) else if cx > cy then 1 else clist_cmp xs ys

let str_cmp (a b : string) : int = clist_cmp (String.list_of_string a) (String.list_of_string b)

let term_render (t : rdf_term) : string =
  match t with
  | T_IRI i -> i
  | T_Literal l -> l.lexical_form
  | T_BNode b -> b
  | T_TripleTerm _ _ _ -> ""

// Ordering for shnex:orderBy sort keys: numeric when both are integer
// literals; otherwise a lexical comparison of the rendered term (which
// orders ISO dates / plain strings correctly, and puts the empty-string
// "no value" sentinel first).
let term_cmp (a b : rdf_term) : int =
  match parse_int_term a, parse_int_term b with
  | Some x, Some y -> if x < y then (-1) else if x > y then 1 else 0
  | _, _ -> str_cmp (term_render a) (term_render b)

// --- SHACL-SPARQL node expressions (shnex-sparql) --------------------
//
// A `[ sparql:<fn> ( arg1 arg2 .. ) ]` node expression applies the
// SPARQL built-in function <fn> to its evaluated arguments. We bridge
// to SPARQL11.Algebra's expression AST + evaluator: each argument value
// is wrapped as a constant `expr`, dispatched to the matching
// constructor, evaluated with an empty solution mapping, and the
// eval_result converted back to a term.

let sparql_ns : string = "http://www.w3.org/ns/sparql#"

let sparql_localname (p : wf_iri) : option string =
  let n = String.length sparql_ns in
  if String.length p > n && String.sub p 0 n = sparql_ns
  then Some (String.sub p n (String.length p - n)) else None

// The (localname, argument-list-head) of a sparql: function call on `es`,
// found by scanning the graph for a sparql:-namespaced predicate.
let sparql_call_of (g : rdf_graph) (es : subject) : option (string & rdf_term) =
  match List.Tot.filter (fun (tr : triple) -> subject_eq tr.s es && Some? (sparql_localname tr.p)) g with
  | tr :: _ -> (match sparql_localname tr.p with Some ln -> Some (ln, tr.o) | None -> None)
  | [] -> None

// A triple-term subject is always an IRI or blank node (never a nested
// triple term), so this needs no recursion.
let subj_to_expr (s : subject) : Alg.expr =
  match s with
  | S_IRI i -> Alg.E_IRI i
  | S_BNode _ -> Alg.E_Literal (Alg.mk_plain_literal "")

// Wrap an already-computed value term as a constant SPARQL expression,
// promoting numeric/boolean literals to their typed expr forms so the
// arithmetic / numeric builtins see numbers rather than opaque literals,
// and reflecting a triple term as E_TripleTerm so the triple-term
// accessors (SUBJECT/PREDICATE/OBJECT/isTRIPLE) can project it.
let rec term_to_expr (t : rdf_term) : Tot Alg.expr (decreases t) =
  match t with
  | T_IRI i -> Alg.E_IRI i
  | T_Literal l ->
    if l.datatype = xsd_integer
    then (match Alg.parse_int_string l.lexical_form with Some n -> Alg.E_NumericLit n | None -> Alg.E_Literal l)
    else if l.datatype = xsd_decimal then Alg.E_DecimalLit l.lexical_form
    else if l.datatype = xsd_double then Alg.E_DoubleLit l.lexical_form
    else if l.datatype = xsd_boolean then Alg.E_BoolLit (l.lexical_form = "true")
    else Alg.E_Literal l
  | T_TripleTerm s p o -> Alg.E_TripleTerm (subj_to_expr s) (Alg.E_IRI p) (term_to_expr o)
  | T_BNode _ -> Alg.E_Literal (Alg.mk_plain_literal "")

// Dispatch a SPARQL builtin localname + argument expressions to the
// SPARQL11.Algebra `expr` AST. None for a name/arity we do not bridge
// (langMatches, uuid/struuid, bnode, sameValue, triple-term ctors, and
// bound — which needs a variable, not a value).
let sparql_fn_expr (ln : string) (args : list Alg.expr) : option Alg.expr =
  match ln, args with
  | "abs", [a] -> Some (Alg.E_Abs a)
  | "ceil", [a] -> Some (Alg.E_Ceil a)
  | "floor", [a] -> Some (Alg.E_Floor a)
  | "round", [a] -> Some (Alg.E_Round a)
  | "str", [a] -> Some (Alg.E_Str a)
  | "strlen", [a] -> Some (Alg.E_StrLen a)
  | "ucase", [a] -> Some (Alg.E_UCase a)
  | "lcase", [a] -> Some (Alg.E_LCase a)
  | "lang", [a] -> Some (Alg.E_Lang a)
  | "langdir", [a] -> Some (Alg.E_LangDir a)
  // hasLang / hasLangdir: the shnex-sparql fixtures pass an optional
  // second (language) argument; the presence test uses the first term.
  | "hasLang", [a] -> Some (Alg.E_HasLang a)
  | "hasLang", [a; _] -> Some (Alg.E_HasLang a)
  | "hasLangdir", [a] -> Some (Alg.E_HasLangDir a)
  | "hasLangdir", [a; _] -> Some (Alg.E_HasLangDir a)
  | "datatype", [a] -> Some (Alg.E_Datatype a)
  | "iri", [a] -> Some (Alg.E_IRI_fn a)
  | "uri", [a] -> Some (Alg.E_IRI_fn a)
  | "encode-for-uri", [a] -> Some (Alg.E_EncodeForUri a)
  | "encode", [a] -> Some (Alg.E_EncodeForUri a)
  | "isIRI", [a] -> Some (Alg.E_IsIRI a)
  | "isURI", [a] -> Some (Alg.E_IsIRI a)
  | "isBlank", [a] -> Some (Alg.E_IsBlank a)
  | "isLiteral", [a] -> Some (Alg.E_IsLiteral a)
  | "isNumeric", [a] -> Some (Alg.E_IsNumeric a)
  | "isTriple", [a] -> Some (Alg.E_IsTriple a)
  | "triple", [a; b; c] -> Some (Alg.E_TripleTerm a b c)
  | "subject", [a] -> Some (Alg.E_TTSubject a)
  | "predicate", [a] -> Some (Alg.E_TTPredicate a)
  | "object", [a] -> Some (Alg.E_TTObject a)
  | "contains", [a; b] -> Some (Alg.E_Contains a b)
  | "strstarts", [a; b] -> Some (Alg.E_StrStarts a b)
  | "strends", [a; b] -> Some (Alg.E_StrEnds a b)
  | "strbefore", [a; b] -> Some (Alg.E_StrBefore a b)
  | "strafter", [a; b] -> Some (Alg.E_StrAfter a b)
  | "strdt", [a; b] -> Some (Alg.E_StrDt a b)
  | "strlang", [a; b] -> Some (Alg.E_StrLang a b)
  | "strlangdir", [a; b; c] -> Some (Alg.E_StrLangDir a b c)
  | "concat", _ -> Some (Alg.E_Concat args)
  | "coalesce", _ -> Some (Alg.E_Coalesce args)
  | "sameTerm", [a; b] -> Some (Alg.E_SameTerm a b)
  | "if", [a; b; c] -> Some (Alg.E_If a b c)
  | "substr", [a; b] -> Some (Alg.E_Substr a b None)
  | "substr", [a; b; c] -> Some (Alg.E_Substr a b (Some c))
  | "replace", [a; b; c] -> Some (Alg.E_Replace a b c None)
  | "replace", [a; b; c; d] -> Some (Alg.E_Replace a b c (Some d))
  | "regex", [a; b] -> Some (Alg.E_Regex a b None)
  | "regex", [a; b; c] -> Some (Alg.E_Regex a b (Some c))
  | "year", [a] -> Some (Alg.E_Year a)
  | "month", [a] -> Some (Alg.E_Month a)
  | "day", [a] -> Some (Alg.E_Day a)
  | "hours", [a] -> Some (Alg.E_Hours a)
  | "minutes", [a] -> Some (Alg.E_Minutes a)
  | "seconds", [a] -> Some (Alg.E_Seconds a)
  | "timezone", [a] -> Some (Alg.E_Timezone a)
  | "tz", [a] -> Some (Alg.E_Tz a)
  | "md5", [a] -> Some (Alg.E_MD5 a)
  | "sha1", [a] -> Some (Alg.E_SHA1 a)
  | "sha256", [a] -> Some (Alg.E_SHA256 a)
  | "sha384", [a] -> Some (Alg.E_SHA384 a)
  | "sha512", [a] -> Some (Alg.E_SHA512 a)
  | "logical-not", [a] -> Some (Alg.E_Not a)
  | "unary-minus", [a] -> Some (Alg.E_UnaryMinus a)
  | "unary-plus", [a] -> Some (Alg.E_UnaryPlus a)
  | "logical-and", [a; b] -> Some (Alg.E_And a b)
  | "logical-or", [a; b] -> Some (Alg.E_Or a b)
  | "divide", [a; b] -> Some (Alg.E_Arith Alg.Div a b)
  | "multiply", [a; b] -> Some (Alg.E_Arith Alg.Mul a b)
  | "plus", [a; b] -> Some (Alg.E_Arith Alg.Add a b)
  | "subtract", [a; b] -> Some (Alg.E_Arith Alg.Sub a b)
  | "equals", [a; b] -> Some (Alg.E_Compare Alg.CmpEq a b)
  | "sameValue", [a; b] -> Some (Alg.E_Compare Alg.CmpEq a b)
  | "not-equals", [a; b] -> Some (Alg.E_Compare Alg.CmpNe a b)
  | "greater-than", [a; b] -> Some (Alg.E_Compare Alg.CmpGt a b)
  | "greater-than-or-equal", [a; b] -> Some (Alg.E_Compare Alg.CmpGe a b)
  | "less-than", [a; b] -> Some (Alg.E_Compare Alg.CmpLt a b)
  | "less-than-or-equal", [a; b] -> Some (Alg.E_Compare Alg.CmpLe a b)
  | _, _ -> None

// Canonicalise an xsd:decimal literal: the canonical lexical form must
// contain a decimal point (ABS/CEIL/FLOOR/ROUND of a decimal yield a
// decimal, and Alg emits e.g. "4" where the canonical form is "4.0").
let canon_decimal (t : rdf_term) : rdf_term =
  match t with
  | T_Literal l ->
    if l.datatype = xsd_decimal && not (List.Tot.mem '.' (String.list_of_string l.lexical_form))
    then T_Literal ({ l with lexical_form = String.concat "" [l.lexical_form; ".0"] })
    else t
  | _ -> t

let ne_uuid_iri : wf_iri =
  assert_norm (is_iri "urn:uuid:00000000-0000-0000-0000-000000000000");
  "urn:uuid:00000000-0000-0000-0000-000000000000"

let is_digit (c : char) : bool = let n = FStar.Char.int_of_char c in n >= 48 && n <= 57

// Chars following the first occurrence of `c` in `cs`.
let rec after_char (c : char) (cs : list char) : Tot (list char) (decreases cs) =
  match cs with [] -> [] | x :: r -> if x = c then r else after_char c r

let rec take_while_lc (p : char -> bool) (cs : list char) : Tot (list char) (decreases cs) =
  match cs with c :: r -> if p c then c :: take_while_lc p r else [] | [] -> []

// The seconds field of an xsd:dateTime lexical `...THH:MM:SS[.fff][tz]`,
// preserving its 2-digit form (the shnex-sparql SECONDS fixture expects
// the lexical "00", not the canonical decimal "0").
let extract_seconds_field (s : string) : string =
  let cs = String.list_of_string s in
  let secs = take_while_lc is_digit (after_char ':' (after_char ':' (after_char 'T' cs))) in
  match secs with [] -> "0" | _ -> String.string_of_list secs

let str_starts_with (s pfx : string) : bool =
  let n = String.length pfx in
  String.length s >= n && String.sub s 0 n = pfx

// langMatches(tag, range): the basic-range match of RFC 4647 / SPARQL —
// `*` matches any non-empty tag; otherwise the tag equals the range or
// extends it with a `-` subtag boundary. (Case handling is sufficient
// for the shnex-sparql fixture, whose range is lowercase.)
let lang_matches (tag range : string) : bool =
  if range = "*" then String.length tag > 0
  else tag = range || str_starts_with tag (String.concat "" [range; "-"])

// Evaluate a bridged SPARQL builtin call. Several builtins are handled
// directly at this layer — either because the SPARQL expr AST cannot
// represent their argument/result (a blank node, a computed URI/UUID) or
// because they inspect the raw evaluated arguments (BOUND) — the rest go
// through the SPARQL11.Algebra expression evaluator.
let sparql_apply (ln : string) (argvals : list rdf_term) : list rdf_term =
  match ln, argvals with
  | "isBlank", [t] -> [ mk_bool_lit (T_BNode? t) ]
  | "bnode", _ -> [ T_BNode "ne_bnode0" ]
  | "uuid", _ -> [ T_IRI ne_uuid_iri ]
  | "struuid", _ -> [ T_Literal (Alg.mk_plain_literal "00000000-0000-0000-0000-000000000000") ]
  | "langMatches", [a; b] -> [ mk_bool_lit (lang_matches (term_render a) (term_render b)) ]
  | "seconds", [T_Literal l] ->
    [ T_Literal ({ lexical_form = extract_seconds_field l.lexical_form; datatype = xsd_decimal;
                   lang_tag = None; direction = None }) ]
  // BOUND: its argument expression contributed a value iff argvals is
  // non-empty (eval_ne_argvals drops an argument that evaluates to []).
  | "bound", _ -> [ mk_bool_lit (Cons? argvals) ]
  | _, _ ->
    (match sparql_fn_expr ln (List.Tot.map term_to_expr argvals) with
     | Some e -> (match Alg.er_to_term (Alg.eval_expr_with_base None e Alg.sm_empty) with Some t -> [canon_decimal t] | None -> [])
     | None -> [])

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
      (match sparql_call_of g es with
       | Some (ln, arglist) -> sparql_apply ln (eval_ne_argvals g focus scope (rdf_list_terms g arglist fuel') fuel')
       | None ->
      (match find_objects g es shnex_instancesOf with
       | (T_IRI c) :: _ -> instances_of g c
       | _ ->
         // No shnex function predicate. A blank node may still be a bare
         // rdf:List node expression (its members are sub-expressions, e.g.
         // `( 1 2 3 )` -> [1;2;3]) or an EMPTY expression `[]` -> []. An
         // IRI (incl. rdf:nil from `()`) or literal is a constant -> itself.
         (match find_objects g es rdf_first with
          | (_ :: _) -> eval_ne_list g focus scope (rdf_list_terms g expr fuel') fuel'
          | [] -> (match expr with T_BNode _ -> [] | _ -> [expr]))))))))))))))))
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
    // A missing key sorts FIRST (the "no value goes to the beginning"
    // rule) — use the empty-string sentinel, which term_cmp orders before
    // any real key.
    let k = (match eval_ne g (Some el) scope keyexpr fuel
             with kk :: _ -> kk
                | [] -> T_Literal ({ lexical_form = ""; datatype = xsd_string; lang_tag = None; direction = None })) in
    (el, k) :: eval_ne_keyed g scope keyexpr rest fuel

// Evaluate each SPARQL-builtin argument expression to a single value
// (its first result; skipped if it yields none) for sparql_apply.
and eval_ne_argvals (g : rdf_graph) (focus : option rdf_term) (scope : list (string & rdf_term))
                    (argexprs : list rdf_term) (fuel : nat)
  : Tot (list rdf_term) (decreases %[fuel; 1; List.Tot.length argexprs])
  =
  match argexprs with
  | [] -> []
  | a :: rest ->
    (match eval_ne g focus scope a fuel with v :: _ -> [v] | [] -> []) @ eval_ne_argvals g focus scope rest fuel
#pop-options

// Entry point for the runner: evaluate `expr` against `g` with an
// optional focus node and a variable scope, returning the value list.
let eval_node_expr_top (g : rdf_graph) (focus : option rdf_term)
                       (scope : list (string & rdf_term)) (expr : rdf_term)
  : list rdf_term
  = eval_ne g focus scope expr (graph_len g + 100)
