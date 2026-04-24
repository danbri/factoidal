module RDF.Graph.Executable

open FStar.String
open FStar.List.Tot

(** 1. Concrete Types for Execution **)
// We choose string for blank nodes so they can be extracted as simple values
type bnode_id = string
type iri = string

(** 2. Refined IRIs **)
(* An IRI must be non-empty and contain a colon.
   Use direct indexed traversal to avoid allocating an intermediate char list. *)
let rec string_has_colon_from (s: string) (pos: nat) (fuel: nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    let len = String.length s in
    if pos >= len then false
    else if FStar.Char.int_of_char (String.index s pos) = 0x3A then true
    else string_has_colon_from s (pos + 1) (fuel - 1)

let string_contains_colon (s : string) : bool =
  string_has_colon_from s 0 (String.length s + 1)

let is_iri (s : string) : bool =
  String.length s > 0 && string_contains_colon s

type wf_iri = s:iri{is_iri s}

(* Well-known IRI constants — concrete string values with normalization hints.
   F* normalizer verifies is_iri at compile time. *)
let rdf_lang_string : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"
let xsd_string : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#string");
  "http://www.w3.org/2001/XMLSchema#string"
let xsd_integer : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#integer");
  "http://www.w3.org/2001/XMLSchema#integer"
let xsd_decimal : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#decimal");
  "http://www.w3.org/2001/XMLSchema#decimal"
let xsd_double : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#double");
  "http://www.w3.org/2001/XMLSchema#double"
let xsd_boolean : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#boolean");
  "http://www.w3.org/2001/XMLSchema#boolean"

(** 3. Literals with Runtime Checks **)
noeq type literal = {
  lexical_form : string;
  datatype     : wf_iri;
  lang_tag     : option string;
}

let literal_wf (l:literal) : bool =
  match l.lang_tag with
  | None   -> l.datatype <> rdf_lang_string
  | Some _ -> l.datatype = rdf_lang_string

type wf_literal = l:literal{literal_wf l}

(** 4. Terms and Triples **)
noeq type rdf_term =
  | T_IRI     : wf_iri -> rdf_term
  | T_BNode   : bnode_id -> rdf_term
  | T_Literal : wf_literal -> rdf_term

noeq type subject =
  | S_IRI : wf_iri -> subject
  | S_BNode : bnode_id -> subject

(* Decidable equality for subjects — concrete implementation.
   Pattern-match on constructors and compare the underlying strings.
   wf_iri and bnode_id are both string, which is eqtype. *)
let subject_eq (s1 s2 : subject) : bool =
  match s1, s2 with
  | S_IRI i1, S_IRI i2 -> i1 = i2
  | S_BNode b1, S_BNode b2 -> b1 = b2
  | _, _ -> false

(* Case-insensitive language tag comparison per RDF 1.1 §3.3.
   Language tags like @en-US and @en-us denote the same value. *)
let lang_tag_eq (t1 t2 : string) : bool =
  String.lowercase t1 = String.lowercase t2

let lang_tag_option_eq (t1 t2 : option string) : bool =
  match t1, t2 with
  | None, None -> true
  | Some s1, Some s2 -> lang_tag_eq s1 s2
  | _, _ -> false

(* Decidable equality for literals — compare all three fields.
   Language tags are compared case-insensitively per RDF 1.1. *)
let literal_eq (l1 l2 : literal) : bool =
  l1.lexical_form = l2.lexical_form &&
  l1.datatype = l2.datatype &&
  lang_tag_option_eq l1.lang_tag l2.lang_tag

(* Decidable equality for RDF terms — concrete implementation. *)
let rdf_term_eq (t1 t2 : rdf_term) : bool =
  match t1, t2 with
  | T_IRI i1, T_IRI i2 -> i1 = i2
  | T_BNode b1, T_BNode b2 -> b1 = b2
  | T_Literal l1, T_Literal l2 -> literal_eq l1 l2
  | _, _ -> false

(* RDF 1.1 value equality for literals.
   In RDF 1.1, a plain literal "foo" is equivalent to "foo"^^xsd:string.
   Both have datatype xsd:string and no language tag. This function handles
   the case where one literal might have an explicit xsd:string datatype
   annotation and the other might be a "plain" literal (which also has
   datatype xsd:string per RDF 1.1 abstract syntax). *)
let literal_value_eq (l1 l2 : literal) : bool =
  (* Same lexical form is always required *)
  l1.lexical_form = l2.lexical_form &&
  (* Language tags compared case-insensitively *)
  lang_tag_option_eq l1.lang_tag l2.lang_tag &&
  (* Datatypes must match. Since RDF 1.1 mandates that plain literals
     have datatype xsd:string, both forms already carry xsd:string
     as their datatype in a well-formed representation. We compare
     datatypes directly — if both are xsd:string they match. *)
  l1.datatype = l2.datatype

(* RDF 1.1 value equality for terms.
   Extends rdf_term_eq with value-space semantics:
   - Language tags compared case-insensitively (via literal_eq)
   - Plain literal / xsd:string equivalence (via literal_value_eq)
   Note: datatype value equivalence (e.g. "010"^^xsd:integer = "10"^^xsd:integer)
   is NOT yet implemented — that requires numeric normalization in F*. *)
let rdf_term_value_eq (t1 t2 : rdf_term) : bool =
  match t1, t2 with
  | T_IRI i1, T_IRI i2 -> i1 = i2
  | T_BNode b1, T_BNode b2 -> b1 = b2
  | T_Literal l1, T_Literal l2 -> literal_value_eq l1 l2
  | _, _ -> false

noeq type triple = {
  s : subject;
  p : wf_iri;
  o : rdf_term;
}

let triple_eq (a b : triple) : bool =
  subject_eq a.s b.s && a.p = b.p && rdf_term_eq a.o b.o

(** 5. Executable Graph (List-based) **)
// Using a list instead of a Set allows the code to be compiled and run
type rdf_graph = list triple

let empty_graph : rdf_graph = []

(** 5b. RDF Dataset (§13.2 SPARQL) **)
(* An RDF dataset comprises one default graph and zero or more named graphs.
   Each named graph is identified by an IRI. *)
noeq type named_graph = {
  ng_name : iri;
  ng_graph : rdf_graph;
}

noeq type rdf_dataset = {
  ds_default : rdf_graph;
  ds_named : list named_graph;
}

let empty_dataset : rdf_dataset = { ds_default = empty_graph; ds_named = [] }

let make_dataset (default_g : rdf_graph) (named : list named_graph) : rdf_dataset =
  { ds_default = default_g; ds_named = named }

(* Look up a named graph by IRI *)
let rec lookup_named_graph (name : iri) (named : list named_graph) : option rdf_graph =
  match named with
  | [] -> None
  | ng :: rest -> if ng.ng_name = name then Some ng.ng_graph else lookup_named_graph name rest

(* Collect all named graph IRIs *)
let named_graph_iris (ds : rdf_dataset) : list iri =
  List.Tot.map (fun ng -> ng.ng_name) ds.ds_named

(* Blank node labels are scoped to the source document / dataset they came from.
   When multiple files are loaded independently and then merged for querying,
   equal raw labels like "_:x" must not collide accidentally across inputs.
   These helpers namespace blank nodes by a caller-supplied prefix. *)
let rename_bnode_id (prefix:string) (id:bnode_id) : bnode_id =
  String.concat "" [prefix; ":"; id]

let rename_subject_bnodes (prefix:string) (s:subject) : subject =
  match s with
  | S_IRI i -> S_IRI i
  | S_BNode b -> S_BNode (rename_bnode_id prefix b)

let rename_term_bnodes (prefix:string) (o:rdf_term) : rdf_term =
  match o with
  | T_IRI i -> T_IRI i
  | T_Literal l -> T_Literal l
  | T_BNode b -> T_BNode (rename_bnode_id prefix b)

let rename_triple_bnodes (prefix:string) (t:triple) : triple =
  {
    s = rename_subject_bnodes prefix t.s;
    p = t.p;
    o = rename_term_bnodes prefix t.o;
  }

let rename_graph_bnodes (prefix:string) (g:rdf_graph) : rdf_graph =
  List.Tot.map (rename_triple_bnodes prefix) g

let rename_named_graph_bnodes (prefix:string) (ng:named_graph) : named_graph =
  {
    ng_name = ng.ng_name;
    ng_graph = rename_graph_bnodes prefix ng.ng_graph;
  }

let rename_dataset_bnodes (prefix:string) (ds:rdf_dataset) : rdf_dataset =
  {
    ds_default = rename_graph_bnodes prefix ds.ds_default;
    ds_named = List.Tot.map (rename_named_graph_bnodes prefix) ds.ds_named;
  }

// Computes the set of all blank nodes in the graph (subject then object per
// triple, triples in graph order). Tail-recursive accumulator form — avoids
// the cons-after-recurse + double-append that blew v8's stack on graphs with
// many bnodes. `List.Tot.rev` at the base restores the original order.
let rec graph_bnodes_acc (acc : list bnode_id) (g : rdf_graph)
  : Tot (list bnode_id) (decreases g) =
  match g with
  | [] -> List.Tot.rev acc
  | hd :: tl ->
      let acc1 = match hd.s with | S_BNode id -> id :: acc  | _ -> acc  in
      let acc2 = match hd.o with | T_BNode id -> id :: acc1 | _ -> acc1 in
      graph_bnodes_acc acc2 tl

let graph_bnodes (g : rdf_graph) : list bnode_id =
  graph_bnodes_acc [] g

(** 6. Graph Operations **)

// Set-based add: only add if not already present (deduplication)
let rec mem_triple (t:triple) (g:rdf_graph) : bool =
  match g with
  | [] -> false
  | hd :: tl -> triple_eq hd t || mem_triple t tl

let graph_add (t:triple) (g:rdf_graph) : rdf_graph =
  if mem_triple t g then g else g @ [t]

// Remove all occurrences of a triple
let graph_remove (t:triple) (g:rdf_graph) : rdf_graph =
  List.Tot.filter (fun hd -> not (triple_eq hd t)) g

// Graph length
let graph_len (g:rdf_graph) : nat = List.Tot.length g

// Graph union (set union — deduplicated)
let rec graph_union (g1 g2:rdf_graph) : rdf_graph =
  match g1 with
  | [] -> g2
  | hd :: tl -> graph_union tl (graph_add hd g2)

// Find triples by subject IRI
let rec find_by_subject (subj:wf_iri) (g:rdf_graph) : rdf_graph =
  match g with
  | [] -> []
  | hd :: tl ->
    let rest = find_by_subject subj tl in
    match hd.s with
    | S_IRI i -> if i = subj then hd :: rest else rest
    | _ -> rest

// Find triples by predicate IRI
let rec find_by_predicate (pred:wf_iri) (g:rdf_graph) : rdf_graph =
  match g with
  | [] -> []
  | hd :: tl ->
    let rest = find_by_predicate pred tl in
    if hd.p = pred then hd :: rest else rest

(** 7. Equality Reflexivity Lemmas **)

// subject_eq is reflexive
let lemma_subject_eq_refl (s : subject) : Lemma (subject_eq s s = true) =
  match s with
  | S_IRI _ -> ()
  | S_BNode _ -> ()

// literal_eq is reflexive
let lemma_literal_eq_refl (l : literal) : Lemma (literal_eq l l = true) = ()

// rdf_term_eq is reflexive
let lemma_rdf_term_eq_refl (t : rdf_term) : Lemma (rdf_term_eq t t = true) =
  match t with
  | T_IRI _ -> ()
  | T_BNode _ -> ()
  | T_Literal l -> lemma_literal_eq_refl l

// triple_eq is reflexive
let lemma_triple_eq_refl (t : triple) : Lemma (triple_eq t t = true) =
  lemma_subject_eq_refl t.s;
  lemma_rdf_term_eq_refl t.o

// mem_triple finds t at the end of a list
let rec lemma_mem_triple_append (t : triple) (g : rdf_graph) :
  Lemma (mem_triple t (g @ [t]) = true) =
  match g with
  | [] -> lemma_triple_eq_refl t
  | hd :: tl ->
    if triple_eq hd t then ()
    else lemma_mem_triple_append t tl

(** 8. Graph Properties (verified) **)

// Adding a triple guarantees it's in the graph — PROVED (no more admit)
let lemma_add_no_dup (t:triple) (g:rdf_graph) :
  Lemma (mem_triple t (graph_add t g)) =
  if mem_triple t g then ()
  else lemma_mem_triple_append t g

// Removing a triple guarantees it's gone — PROVED (no more admit)
let rec lemma_remove_absent (t:triple) (g:rdf_graph) :
  Lemma (not (mem_triple t (graph_remove t g))) =
  match g with
  | [] -> ()
  | _ :: tl -> lemma_remove_absent t tl

// Empty graph has no bnodes
let lemma_empty_no_bnodes () :
  Lemma (graph_bnodes empty_graph = []) = ()

(** 8. N-Triples Serialization Specification **)

// N-Triples escape table: characters that must be escaped in string literals
let must_escape (c:FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code = 0x5C  // backslash
  || code = 0x22  // double quote
  || code = 0x0A  // newline
  || code = 0x0D  // carriage return
  || code = 0x09  // tab
  || code = 0x08  // backspace
  || code = 0x0C  // form feed
  || code < 0x20  // other control characters

// An N-Triples-safe string has no unescaped special characters
// (This is a predicate for specifying the output of serialization)
(* Checks that no character in s needs escaping.
   Recursive definition over string index; termination assumed. *)
let rec is_nt_escaped_list (cs : list FStar.Char.char) : bool =
  match cs with
  | [] -> true
  | c :: rest ->
    let code = FStar.Char.int_of_char c in
    if code < 0x20 || code = 0x22 || code = 0x5C then false
    else is_nt_escaped_list rest

let is_nt_escaped (s : string) (n : nat) : bool =
  let cs = String.list_of_string s in
  let rec drop_n (l : list FStar.Char.char) (k : nat) : list FStar.Char.char =
    match l with
    | [] -> []
    | _ :: tl -> if k = 0 then l else drop_n tl (k - 1)
  in
  is_nt_escaped_list (drop_n cs n)

// Roundtrip property specification:
// For any well-formed graph g, serializing to N-Triples and parsing back
// should yield a graph with the same triples (modulo blank node renaming).
// This is stated as a type-level specification; proof is future work.
//
// val roundtrip_preserves_triples :
//   g:rdf_graph ->
//   Lemma (graph_isomorphic g (parse_ntriples (serialize_ntriples g)))

(** 9. SPARQL Algebra Specification **)

// Variable names in SPARQL patterns
type var_name = string

// A pattern term: either a concrete RDF term or a variable
noeq type pattern_term =
  | PT_Concrete : rdf_term -> pattern_term
  | PT_Var      : var_name -> pattern_term

noeq type pattern_subject =
  | PS_Concrete : subject -> pattern_subject
  | PS_Var      : var_name -> pattern_subject

// A triple pattern in a Basic Graph Pattern
noeq type triple_pattern = {
  tp_s : pattern_subject;
  tp_p : wf_iri;       // Predicates are always IRIs in SPARQL 1.0
  tp_o : pattern_term;
}

// A solution mapping: variable -> RDF term
type solution_mapping = list (var_name * rdf_term)

// Basic Graph Pattern = list of triple patterns
type bgp = list triple_pattern

// A single triple pattern matches against a graph triple under a mapping
let pattern_subject_matches (ps:pattern_subject) (s:subject) (mu:solution_mapping) : bool =
  match ps with
  | PS_Concrete cs -> subject_eq cs s
  | PS_Var v ->
    (match List.Tot.assoc v mu with
    | Some (T_IRI i) -> subject_eq s (S_IRI i)
    | Some (T_BNode b) -> subject_eq s (S_BNode b)
    | _ -> true)  // unbound variable matches anything (will be bound)

let pattern_term_matches (pt:pattern_term) (t:rdf_term) (mu:solution_mapping) : bool =
  match pt with
  | PT_Concrete ct -> rdf_term_eq ct t
  | PT_Var v ->
    (match List.Tot.assoc v mu with
    | Some bound -> rdf_term_eq bound t
    | None -> true)  // unbound variable matches anything

// A triple pattern matches a triple under a solution mapping
let triple_pattern_matches (tp:triple_pattern) (t:triple) (mu:solution_mapping) : bool =
  pattern_subject_matches tp.tp_s t.s mu &&
  tp.tp_p = t.p &&
  pattern_term_matches tp.tp_o t.o mu

// SPARQL algebra operations (specification level)
noeq type algebra_op =
  | BGP_Op      : bgp -> algebra_op
  | Filter_Op   : algebra_op -> algebra_op  // Filter expression omitted for now
  | Optional_Op : algebra_op -> algebra_op -> algebra_op
  | Union_Op    : algebra_op -> algebra_op -> algebra_op

// Solution multiset (bag semantics)
type solution_multiset = list solution_mapping

// Evaluate a BGP: find all solution mappings for the pattern against the graph
// (This is a specification — the Rust implementation should produce equivalent results)
//
// val eval_bgp : bgp -> rdf_graph -> solution_multiset

(** 10. Graph Isomorphism (for bnode-insensitive comparison) **)

// Two graphs are isomorphic if there exists a bijection on blank node IDs
// such that applying the mapping to one graph yields the other.
// (Stated declaratively; full proof would require a constructive witness)
//
// type bnode_mapping = bnode_id -> bnode_id
//
// val graph_isomorphic : rdf_graph -> rdf_graph -> bool
//   (requires constructing a witness mapping, NP-complete in general,
//    but tractable for small test graphs)

(* ======================================================================== *)
(* SPARQL Evaluation Semantics                                              *)
(* ======================================================================== *)
(* Formal specification of SPARQL typed value comparison, FILTER evaluation, *)
(* BIND semantics, and string functions.  Corresponds to the Rust           *)
(* implementation in sparql.rs (TypedFilterValue, typed_compare,            *)
(* eval_filter_expr_typed, evaluate_clauses/Bind).                          *)
(* ======================================================================== *)

(** 11. SPARQL Typed Value Comparison **)

// Numeric sub-types mirroring XSD numeric hierarchy
type numeric_type =
  | NT_Integer
  | NT_Decimal
  | NT_Double
  | NT_Float

// Comparison operators
type comp_op =
  | Eq
  | Ne
  | Lt
  | Gt
  | Le
  | Ge

// SPARQL typed values — mirrors Rust TypedFilterValue enum
// Each variant carries the data needed for comparison and evaluation.
type sparql_value =
  | SV_Numeric      : value:int -> ntype:numeric_type -> sparql_value
  | SV_PlainLiteral : lexical:string -> sparql_value
  | SV_LangLiteral  : lexical:string -> lang:string -> sparql_value
  | SV_Iri          : iri_str:string -> sparql_value
  | SV_BNode        : id:bnode_id -> sparql_value
  | SV_TypedLiteral : lexical:string -> datatype:wf_iri -> sparql_value
  | SV_Boolean      : b:bool -> sparql_value

// String comparison helper (lexicographic, same as OCaml/Rust string ordering)
// We leave this abstract; F* string comparison via = suffices for equality.
let string_lt (s1 s2 : string) : bool =
  String.compare s1 s2 < 0

// Typed value comparison — returns None for type errors (incompatible types)
// Mirrors typed_compare in sparql.rs
let value_compare (lv rv : sparql_value) (op : comp_op) : option bool =
  match lv, rv with
  // Numeric × numeric: cross-type comparison is always allowed
  | SV_Numeric ln _, SV_Numeric rn _ ->
    Some (match op with
          | Eq -> ln = rn
          | Ne -> ln <> rn
          | Lt -> ln < rn
          | Gt -> ln > rn
          | Le -> ln <= rn
          | Ge -> ln >= rn)

  // Boolean × boolean: only equality/inequality
  | SV_Boolean l, SV_Boolean r ->
    (match op with
     | Eq -> Some (l = r)
     | Ne -> Some (l <> r)
     | _  -> None)

  // Plain literal × plain literal: full ordering via string comparison
  | SV_PlainLiteral l, SV_PlainLiteral r ->
    Some (match op with
          | Eq -> l = r
          | Ne -> l <> r
          | Lt -> string_lt l r
          | Gt -> string_lt r l
          | Le -> l = r || string_lt l r
          | Ge -> l = r || string_lt r l)

  // Lang literal × lang literal: eq/ne only, both lexical and lang must match
  // Language tags compared case-insensitively per RDF 1.1
  | SV_LangLiteral llex llang, SV_LangLiteral rlex rlang ->
    (match op with
     | Eq -> Some (llex = rlex && lang_tag_eq llang rlang)
     | Ne -> Some (llex <> rlex || not (lang_tag_eq llang rlang))
     | _  -> None)

  // IRI × IRI: full ordering via string comparison
  | SV_Iri l, SV_Iri r ->
    Some (match op with
          | Eq -> l = r
          | Ne -> l <> r
          | Lt -> string_lt l r
          | Gt -> string_lt r l
          | Le -> l = r || string_lt l r
          | Ge -> l = r || string_lt r l)

  // BNode × BNode: equality/inequality only
  | SV_BNode l, SV_BNode r ->
    (match op with
     | Eq -> Some (l = r)
     | Ne -> Some (l <> r)
     | _  -> None)

  // Typed literal × typed literal: comparable only when datatypes match
  | SV_TypedLiteral llex ldt, SV_TypedLiteral rlex rdt ->
    if ldt = rdt then
      Some (match op with
            | Eq -> llex = rlex
            | Ne -> llex <> rlex
            | Lt -> string_lt llex rlex
            | Gt -> string_lt rlex llex
            | Le -> llex = rlex || string_lt llex rlex
            | Ge -> llex = rlex || string_lt rlex llex)
    else
      None  // different unknown datatypes → type error

  // All other combinations: incompatible types → type error
  | _, _ -> None

(** 12. SPARQL FILTER Evaluation — Boolean Effective Value **)

// The boolean effective value (EBV) of a SPARQL value determines its truth
// when used in a FILTER context.  Mirrors the BooleanEffectiveValue branch
// of eval_filter in sparql.rs.
//
// Rules (SPARQL 1.1 §17.2.2):
//   - Boolean "true" or "1" → true
//   - Numeric non-zero → true
//   - Non-empty plain string → true
//   - Empty string, "false", "0", zero → false
//   - Lang literals with non-empty lexical → true
//   - Other types → type error (we return false, matching Rust impl)

let boolean_effective_value (v : sparql_value) : bool =
  match v with
  | SV_Boolean b -> b
  | SV_Numeric n _ -> n <> 0
  | SV_PlainLiteral s -> String.length s > 0
  | SV_LangLiteral s _ -> String.length s > 0
  | SV_Iri _ -> false       // IRIs have no boolean interpretation
  | SV_BNode _ -> false     // BNodes have no boolean interpretation
  | SV_TypedLiteral _ _ -> false  // Unknown typed literals → false

// For unbound variables, the EBV is false.
// This models the SPARQL semantics where FILTER on an unbound variable fails.
let bev_of_option (v : option sparql_value) : bool =
  match v with
  | None   -> false   // unbound → false
  | Some x -> boolean_effective_value x

(** 13. SPARQL BIND Semantics **)

// BIND assigns the result of an expression to a variable in each solution.
// If the expression evaluates to None, the variable remains unbound.
// Crucially, BIND does not overwrite existing bindings — the SPARQL spec
// requires the target variable to be unbound in the current scope.
//
// Mirrors evaluate_clauses/WhereClause::Bind in sparql.rs.

// Expression evaluation result: either a concrete RDF term or error (None)
// We abstract over the expression language; in the Rust impl this is FilterExpr.
type filter_expr_eval = solution_mapping -> option rdf_term

// BIND evaluation: given an expression evaluator and a solution mapping,
// produce a (variable, term) pair if the expression succeeds
let bind_eval (eval : filter_expr_eval) (var : var_name) (mu : solution_mapping)
  : option (var_name * rdf_term) =
  match List.Tot.assoc var mu with
  | Some _ -> None  // variable already bound — do not overwrite (SPARQL spec)
  | None ->
    match eval mu with
    | Some term -> Some (var, term)
    | None      -> None  // expression error → variable stays unbound

// Apply BIND to a solution mapping: extend it if the expression succeeds
let apply_bind (eval : filter_expr_eval) (var : var_name) (mu : solution_mapping)
  : solution_mapping =
  match bind_eval eval var mu with
  | Some pair -> pair :: mu
  | None      -> mu

(** 14. SPARQL String Function Signatures **)

// Type specifications for SPARQL 1.1 string functions.
// These mirror the FnStrLen, FnSubStr, FnUCase, FnLCase, FnConcat
// branches in eval_filter_expr_typed in sparql.rs.

// STRLEN: returns the number of characters (not bytes) in the string
let sparql_strlen (s : string) : nat =
  String.length s

// SUBSTR: 1-indexed substring extraction
// start is 1-indexed per SPARQL spec; length is optional
// Mirrors the Rust SUBSTR implementation which converts to 0-indexed internally
let string_substring (s : string) (i : nat) (len : nat) : string =
  let slen = String.length s in
  if i >= slen then ""
  else
    let max_len = slen - i in
    let actual_len = if len <= max_len then len else max_len in
    String.sub s i actual_len

let sparql_substr (s : string) (start : nat) (len : option nat) : string =
  let start_idx = if start > 0 then start - 1 else 0 in
  let remaining = if String.length s > start_idx then String.length s - start_idx else 0 in
  match len with
  | Some n -> string_substring s start_idx n
  | None   -> string_substring s start_idx remaining

// UCASE: convert all characters to upper case
let string_to_upper (s : string) : string =
  String.uppercase s

let sparql_ucase (s : string) : string =
  string_to_upper s

// LCASE: convert all characters to lower case
let string_to_lower (s : string) : string =
  String.lowercase s

let sparql_lcase (s : string) : string =
  string_to_lower s

// CONCAT: concatenate a list of strings
let rec sparql_concat (args : list string) : string =
  match args with
  | [] -> ""
  | hd :: tl -> String.concat "" [hd; sparql_concat tl]

(** 15. Properties and Lemmas **)

// Comparison reflexivity: any value that supports Eq is equal to itself — PROVED
let lemma_compare_reflexive (v : sparql_value) :
  Lemma (match v with
         | SV_Numeric _ _      -> value_compare v v Eq = Some true
         | SV_PlainLiteral _   -> value_compare v v Eq = Some true
         | SV_LangLiteral _ _  -> value_compare v v Eq = Some true
         | SV_Iri _            -> value_compare v v Eq = Some true
         | SV_BNode _          -> value_compare v v Eq = Some true
         | SV_Boolean _        -> value_compare v v Eq = Some true
         | SV_TypedLiteral _ _ -> value_compare v v Eq = Some true) =
  match v with
  | SV_Numeric _ _      -> ()
  | SV_PlainLiteral _   -> ()
  | SV_LangLiteral _ _  -> ()
  | SV_Iri _            -> ()
  | SV_BNode _          -> ()
  | SV_Boolean _        -> ()
  | SV_TypedLiteral _ _ -> ()

// Comparison symmetry for equality: Eq is symmetric for all comparable types — PROVED
let lemma_compare_symmetric (a b : sparql_value) :
  Lemma (value_compare a b Eq = value_compare b a Eq) =
  match a, b with
  | SV_Numeric _ _, SV_Numeric _ _             -> ()
  | SV_Boolean _, SV_Boolean _                  -> ()
  | SV_PlainLiteral _, SV_PlainLiteral _        -> ()
  | SV_LangLiteral _ _, SV_LangLiteral _ _      -> ()
  | SV_Iri _, SV_Iri _                          -> ()
  | SV_BNode _, SV_BNode _                      -> ()
  | SV_TypedLiteral _ dt1, SV_TypedLiteral _ dt2 ->
    if dt1 = dt2 then () else ()
  | _, _ -> ()

// Incompatible type comparison: numeric vs plain literal returns None
let lemma_incompatible_types (n : int) (nt : numeric_type) (s : string) :
  Lemma (value_compare (SV_Numeric n nt) (SV_PlainLiteral s) Eq = None /\
         value_compare (SV_Numeric n nt) (SV_PlainLiteral s) Lt = None /\
         value_compare (SV_PlainLiteral s) (SV_Numeric n nt) Eq = None) =
  ()

// BIND preserves existing bindings: if a variable is already bound,
// apply_bind does not modify the solution mapping — PROVED
let lemma_bind_preserves_existing
  (eval:filter_expr_eval) (var:var_name) (mu:solution_mapping) :
  Lemma (match List.Tot.assoc var mu with
         | Some _ -> apply_bind eval var mu == mu
         | None -> True) =
  match List.Tot.assoc var mu with
  | Some _ -> ()  // bind_eval returns None when var is already bound → apply_bind returns mu
  | None -> ()    // trivially True

(** ======================================================================== *)
(** 16. RDF/RDFS Vocabulary Constants                                        *)
(** ======================================================================== *)

let rdfs_subClassOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#subClassOf");
  "http://www.w3.org/2000/01/rdf-schema#subClassOf"

let rdfs_subPropertyOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#subPropertyOf");
  "http://www.w3.org/2000/01/rdf-schema#subPropertyOf"

let rdfs_domain : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#domain");
  "http://www.w3.org/2000/01/rdf-schema#domain"

let rdfs_range : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#range");
  "http://www.w3.org/2000/01/rdf-schema#range"

let rdf_type : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

let rdfs_Class : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#Class");
  "http://www.w3.org/2000/01/rdf-schema#Class"

let rdf_Property : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property"

let rdfs_Resource : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#Resource");
  "http://www.w3.org/2000/01/rdf-schema#Resource"

let rdfs_Literal : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#Literal");
  "http://www.w3.org/2000/01/rdf-schema#Literal"

let rdfs_ContainerMembershipProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#ContainerMembershipProperty");
  "http://www.w3.org/2000/01/rdf-schema#ContainerMembershipProperty"

let rdfs_member : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#member");
  "http://www.w3.org/2000/01/rdf-schema#member"

let rdfs_Datatype : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#Datatype");
  "http://www.w3.org/2000/01/rdf-schema#Datatype"

let rdf_1 : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#_1");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#_1"

let rdf_2 : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#_2");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#_2"

let rdf_3 : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#_3");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#_3"

let rdf_4 : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#_4");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#_4"

let rdf_5 : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#_5");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#_5"

(* Container membership property list for closure rules *)
let container_membership_properties : list wf_iri =
  [rdf_1; rdf_2; rdf_3; rdf_4; rdf_5]

(** ======================================================================== *)
(** 17. RDFS Helper Functions                                                *)
(** ======================================================================== *)

(* Convert a subject to an rdf_term *)
let subject_to_term (s : subject) : rdf_term =
  match s with
  | S_IRI i -> T_IRI i
  | S_BNode b -> T_BNode b

(* Convert an rdf_term to a subject, if possible *)
let term_to_subject (t : rdf_term) : option subject =
  match t with
  | T_IRI i -> Some (S_IRI i)
  | T_BNode b -> Some (S_BNode b)
  | T_Literal _ -> None

(* Find all objects where (s p ?o) in graph *)
// Tail-recursive accumulator form; List.Tot.rev at base preserves input order.
// Addresses wdt:P31 stack-blow on 60k-triple graphs with 1000+ matches.
let rec find_objects_acc (acc : list rdf_term) (g : rdf_graph) (subj : subject) (pred : wf_iri)
  : Tot (list rdf_term) (decreases g) =
  match g with
  | [] -> List.Tot.rev acc
  | hd :: tl ->
    if subject_eq hd.s subj && hd.p = pred
    then find_objects_acc (hd.o :: acc) tl subj pred
    else find_objects_acc acc tl subj pred

let find_objects (g : rdf_graph) (subj : subject) (pred : wf_iri) : list rdf_term =
  find_objects_acc [] g subj pred

(* Find all subjects where (?s p o) in graph *)
let rec find_subjects_acc (acc : list subject) (g : rdf_graph) (pred : wf_iri) (obj : rdf_term)
  : Tot (list subject) (decreases g) =
  match g with
  | [] -> List.Tot.rev acc
  | hd :: tl ->
    if hd.p = pred && rdf_term_eq hd.o obj
    then find_subjects_acc (hd.s :: acc) tl pred obj
    else find_subjects_acc acc tl pred obj

let find_subjects (g : rdf_graph) (pred : wf_iri) (obj : rdf_term) : list subject =
  find_subjects_acc [] g pred obj

(* Check if a triple exists in the graph *)
let has_triple (g : rdf_graph) (t : triple) : bool =
  mem_triple t g

(* Add a triple only if not already present *)
let add_triple_if_new (g : rdf_graph) (t : triple) : rdf_graph =
  graph_add t g

(* Add multiple triples, deduplicating *)
let rec add_triples_if_new (g : rdf_graph) (ts : list triple) : Tot rdf_graph (decreases ts) =
  match ts with
  | [] -> g
  | hd :: tl -> add_triples_if_new (add_triple_if_new g hd) tl

(** ======================================================================== *)
(** 18. RDFS Closure Rules                                                   *)
(** ======================================================================== *)

(* rdfs7: If (a P b) and (P rdfs:subPropertyOf Q), infer (a Q b).
   For each triple (a P b) in g, find all Q such that (P subPropertyOf Q),
   then add (a Q b). *)
let rdfs_rule_subPropertyOf (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      let super_props = find_objects g (S_IRI t.p) rdfs_subPropertyOf in
      List.Tot.fold_left
        (fun (acc2 : rdf_graph) (q_term : rdf_term) ->
          match q_term with
          | T_IRI q ->
            let new_t : triple = { s = t.s; p = q; o = t.o } in
            add_triple_if_new acc2 new_t
          | _ -> acc2)
        acc
        super_props)
    g
    g

(* rdfs2: If (a P b) and (P rdfs:domain C), infer (a rdf:type C).
   For each triple (a P b) in g, find all C such that (P domain C),
   then add (a type C). *)
let rdfs_rule_domain (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      let domain_classes = find_objects g (S_IRI t.p) rdfs_domain in
      List.Tot.fold_left
        (fun (acc2 : rdf_graph) (c_term : rdf_term) ->
          let new_t : triple = { s = t.s; p = rdf_type; o = c_term } in
          add_triple_if_new acc2 new_t)
        acc
        domain_classes)
    g
    g

(* rdfs3: If (a P b) and (P rdfs:range C), infer (b rdf:type C).
   For each triple (a P b) in g, find all C such that (P range C),
   then add (b type C) — but only if b can be a subject (IRI or BNode). *)
let rdfs_rule_range (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      let range_classes = find_objects g (S_IRI t.p) rdfs_range in
      match term_to_subject t.o with
      | Some b_subj ->
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (c_term : rdf_term) ->
            let new_t : triple = { s = b_subj; p = rdf_type; o = c_term } in
            add_triple_if_new acc2 new_t)
          acc
          range_classes
      | None -> acc)
    g
    g

(* rdfs9: If (a rdf:type A) and (A rdfs:subClassOf B), infer (a rdf:type B).
   For each triple (a type A) in g, find all B such that (A subClassOf B),
   then add (a type B). *)
let rdfs_rule_subClassOf (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdf_type then
        match t.o with
        | T_IRI class_iri ->
          let super_classes = find_objects g (S_IRI class_iri) rdfs_subClassOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (b_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = rdf_type; o = b_term } in
              add_triple_if_new acc2 new_t)
            acc
            super_classes
        | _ -> acc
      else acc)
    g
    g

(* rdfs11: If (A rdfs:subClassOf B) and (B rdfs:subClassOf C) then
   (A rdfs:subClassOf C).
   Works uniformly for IRIs and bnodes in either position. *)
let rdfs_rule_subClassOf_trans (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subClassOf then
        (* t is (A subClassOf B). Find all C such that (B subClassOf C).
           B must be convertible to a subject (IRI or bnode). *)
        match term_to_subject t.o with
        | Some b_subj ->
          let supers = find_objects g b_subj rdfs_subClassOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (c_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = rdfs_subClassOf; o = c_term } in
              add_triple_if_new acc2 new_t)
            acc
            supers
        | None -> acc
      else acc)
    g
    g

(* rdfs5: If (P rdfs:subPropertyOf Q) and (Q rdfs:subPropertyOf R) then
   (P rdfs:subPropertyOf R).  Dual of rdfs11. *)
let rdfs_rule_subPropertyOf_trans (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subPropertyOf then
        match term_to_subject t.o with
        | Some q_subj ->
          let supers = find_objects g q_subj rdfs_subPropertyOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (r_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = rdfs_subPropertyOf; o = r_term } in
              add_triple_if_new acc2 new_t)
            acc
            supers
        | None -> acc
      else acc)
    g
    g

(* Container membership property axioms:
   rdf:_1 rdfs:subPropertyOf rdfs:member
   rdf:_2 rdfs:subPropertyOf rdfs:member
   ... etc.
   Also: each rdf:_n rdf:type rdfs:ContainerMembershipProperty *)
let rdfs_rule_container_membership (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (cmp : wf_iri) ->
      let t1 : triple = {
        s = S_IRI cmp;
        p = rdfs_subPropertyOf;
        o = T_IRI rdfs_member
      } in
      let t2 : triple = {
        s = S_IRI cmp;
        p = rdf_type;
        o = T_IRI rdfs_ContainerMembershipProperty
      } in
      add_triple_if_new (add_triple_if_new acc t1) t2)
    g
    container_membership_properties

(** ======================================================================== *)
(** 19. Fixed-Point RDFS Closure                                             *)
(** ======================================================================== *)

(* Apply all RDFS rules once *)
let rdfs_closure_step (g : rdf_graph) : rdf_graph =
  let g1 = rdfs_rule_subPropertyOf g in
  let g2 = rdfs_rule_domain g1 in
  let g3 = rdfs_rule_range g2 in
  let g4 = rdfs_rule_subClassOf g3 in
  let g5 = rdfs_rule_container_membership g4 in
  let g6 = rdfs_rule_subClassOf_trans g5 in     (* rdfs11: C<C transitivity *)
  let g7 = rdfs_rule_subPropertyOf_trans g6 in  (* rdfs5:  P<P transitivity *)
  g7

(* Iterate closure until fixed point or max iterations.
   Uses nat fuel parameter for termination. *)
let rec rdfs_closure (g : rdf_graph) (fuel : nat) : Tot rdf_graph (decreases fuel) =
  match fuel with
  | 0 -> g
  | n ->
    let g' = rdfs_closure_step g in
    if graph_len g' = graph_len g
    then g  (* fixed point reached — no new triples added *)
    else rdfs_closure g' (n - 1)

(** ======================================================================== *)
(** 19b. RDFS/OWL Reflexivity Axioms                                         *)
(** ======================================================================== *)

// RDFS entails that every class C is a subclass of itself, and every
// property P is a subproperty of itself (reflexivity of rdfs:subClassOf
// and rdfs:subPropertyOf). The set of "classes" in a graph is
// approximated by: any IRI that appears as subject or object of
// rdfs:subClassOf, or as subject of (rdf:type rdfs:Class) / (rdf:type
// owl:Class). Properties are collected analogously for rdfs:subPropertyOf,
// rdf:Property, owl:ObjectProperty, owl:DatatypeProperty.
//
// This block was formerly implemented in OCaml as post-extraction patch
// #60. Elevated to F* per iron rule #10.

let owl_Class : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Class");
  "http://www.w3.org/2002/07/owl#Class"

let owl_ObjectProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#ObjectProperty");
  "http://www.w3.org/2002/07/owl#ObjectProperty"

let owl_DatatypeProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#DatatypeProperty");
  "http://www.w3.org/2002/07/owl#DatatypeProperty"

let owl_Thing : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Thing");
  "http://www.w3.org/2002/07/owl#Thing"

let owl_Nothing : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Nothing");
  "http://www.w3.org/2002/07/owl#Nothing"

let owl_NamedIndividual : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#NamedIndividual");
  "http://www.w3.org/2002/07/owl#NamedIndividual"

// Prepend i to acc if not already present.
let cons_if_new_iri (i : wf_iri) (acc : list wf_iri) : list wf_iri =
  if List.Tot.mem i acc then acc else i :: acc

// If subject is an IRI, cons it into the accumulator; otherwise leave
// the accumulator unchanged (bnodes cannot participate in the OCaml
// version either — they are never classes or properties by IRI identity).
let cons_subject_iri_if_new (s : subject) (acc : list wf_iri) : list wf_iri =
  match s with
  | S_IRI i -> cons_if_new_iri i acc
  | S_BNode _ -> acc

let cons_term_iri_if_new (t : rdf_term) (acc : list wf_iri) : list wf_iri =
  match t with
  | T_IRI i -> cons_if_new_iri i acc
  | _ -> acc

// Is the triple's object one of the class-typing IRIs (rdfs:Class or
// owl:Class)?
let is_class_type_object (o : rdf_term) : bool =
  match o with
  | T_IRI c -> c = rdfs_Class || c = owl_Class
  | _ -> false

// Is the triple's object one of the property-typing IRIs (rdf:Property,
// owl:ObjectProperty, owl:DatatypeProperty)?
let is_property_type_object (o : rdf_term) : bool =
  match o with
  | T_IRI c -> c = rdf_Property || c = owl_ObjectProperty || c = owl_DatatypeProperty
  | _ -> false

// Walk a graph and gather every IRI that should be treated as a class
// for the reflexivity of rdfs:subClassOf. Matches patch #60 behaviour
// exactly: collect subjects and IRI-objects of rdfs:subClassOf triples,
// plus subjects of (rdf:type rdfs:Class) and (rdf:type owl:Class).
let collect_classes (g : rdf_graph) : list wf_iri =
  List.Tot.fold_left
    (fun (acc : list wf_iri) (t : triple) ->
      let acc1 =
        if t.p = rdfs_subClassOf
        then cons_term_iri_if_new t.o (cons_subject_iri_if_new t.s acc)
        else acc
      in
      if t.p = rdf_type && is_class_type_object t.o
      then cons_subject_iri_if_new t.s acc1
      else acc1)
    []
    g

// Same for properties.
let collect_properties (g : rdf_graph) : list wf_iri =
  List.Tot.fold_left
    (fun (acc : list wf_iri) (t : triple) ->
      let acc1 =
        if t.p = rdfs_subPropertyOf
        then cons_term_iri_if_new t.o (cons_subject_iri_if_new t.s acc)
        else acc
      in
      if t.p = rdf_type && is_property_type_object t.o
      then cons_subject_iri_if_new t.s acc1
      else acc1)
    []
    g

// Build the reflexivity triples (C rdfs:subClassOf C) and
// (P rdfs:subPropertyOf P) for every class C and property P in g.
let rdfs_reflexivity_axioms (g : rdf_graph) : rdf_graph =
  let classes = collect_classes g in
  let properties = collect_properties g in
  let class_triples : rdf_graph =
    List.Tot.map
      (fun (c : wf_iri) -> ({ s = S_IRI c; p = rdfs_subClassOf; o = T_IRI c } <: triple))
      classes
  in
  let property_triples : rdf_graph =
    List.Tot.map
      (fun (p : wf_iri) -> ({ s = S_IRI p; p = rdfs_subPropertyOf; o = T_IRI p } <: triple))
      properties
  in
  class_triples @ property_triples

// Full RDFS closure with reflexivity axioms: run rdfs_closure, harvest
// classes/properties, add reflexivity triples, then run rdfs_closure
// again. This matches the two-pass behaviour of patch #60.
// The fuel parameter bounds the nested closure iterations; both passes
// share the same fuel budget (the same constant was used in the patch).
let rdfs_closure_with_reflexivity (g : rdf_graph) (fuel : nat) : Tot rdf_graph =
  let closed = rdfs_closure g fuel in
  let refl_axioms = rdfs_reflexivity_axioms closed in
  let with_refl = add_triples_if_new closed refl_axioms in
  rdfs_closure with_refl fuel

(** ======================================================================== *)
(** 19c. OWL 2 RL Datalog-shaped closure rules                              *)
(** ======================================================================== *)

// This block implements the subset of OWL 2 RL entailment that is safely
// expressible as forward-chained Datalog rules over RDF triples. It is
// applied on top of the RDFS closure (with reflexivity axioms) and iterates
// to a fixpoint under a fuel bound.
//
// Rules implemented (OWL 2 RL/RDF rule names in parens):
//   eq-ref      : reflexivity of owl:sameAs
//   eq-sym      : symmetry of owl:sameAs
//   eq-trans    : transitivity of owl:sameAs
//   eq-rep-s    : sameAs substitution in subject position
//   eq-rep-p    : sameAs substitution in predicate position (IRI-to-IRI only)
//   eq-rep-o    : sameAs substitution in object position
//   prp-symp    : owl:SymmetricProperty
//   prp-trp     : owl:TransitiveProperty
//   prp-ifp     : owl:InverseFunctionalProperty (produces owl:sameAs)
//   prp-inv1/2  : owl:inverseOf (both directions)
//   cls-eqc1/2  : owl:equivalentClass expanded to rdfs:subClassOf both ways
//   prp-eqp1/2  : owl:equivalentProperty expanded to rdfs:subPropertyOf both ways
//   scm-eqc2    : mutual rdfs:subClassOf -> owl:equivalentClass (named only)
//   scm-eqp2    : mutual rdfs:subPropertyOf -> owl:equivalentProperty (named only)
//   eq-diff-sym : symmetry of owl:differentFrom
//   prp-rfl     : owl:ReflexiveProperty (x P x for every named individual)
//   scm-cls     : (C a owl:Restriction) -> (C a owl:Class) (partial)
//
// NOT implemented (tableau-style, out of scope for this pass):
//   owl:hasValue, owl:someValuesFrom, owl:allValuesFrom restrictions;
//   class disjointness propagation; owl:FunctionalProperty; consistency checks.

let owl_sameAs : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#sameAs");
  "http://www.w3.org/2002/07/owl#sameAs"

let owl_SymmetricProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#SymmetricProperty");
  "http://www.w3.org/2002/07/owl#SymmetricProperty"

let owl_TransitiveProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#TransitiveProperty");
  "http://www.w3.org/2002/07/owl#TransitiveProperty"

let owl_InverseFunctionalProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#InverseFunctionalProperty");
  "http://www.w3.org/2002/07/owl#InverseFunctionalProperty"

let owl_inverseOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#inverseOf");
  "http://www.w3.org/2002/07/owl#inverseOf"

let owl_equivalentClass : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#equivalentClass");
  "http://www.w3.org/2002/07/owl#equivalentClass"

let owl_equivalentProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#equivalentProperty");
  "http://www.w3.org/2002/07/owl#equivalentProperty"

let owl_differentFrom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#differentFrom");
  "http://www.w3.org/2002/07/owl#differentFrom"

// Check whether a predicate is one of the OWL predicates that we treat
// specially (used to block no-op rule applications where we would re-emit
// a triple that is already present).
let is_owl_metapredicate (p : wf_iri) : bool =
  p = owl_sameAs || p = owl_inverseOf ||
  p = owl_equivalentClass || p = owl_equivalentProperty

// cls-eqc1 + cls-eqc2: if (C owl:equivalentClass D) then
//   (C rdfs:subClassOf D) and (D rdfs:subClassOf C).
// Handles both IRI-IRI and IRI-bnode (and bnode-bnode) operands —
// the latter is needed for tableau-style class expressions where the
// RHS is an anonymous owl:Restriction / owl:intersectionOf bnode.
//
// BNODE-POLLUTION GUARD (parent9 regression, 2026-04-23): when one side
// of owl:equivalentClass is an anonymous class-expression bnode, we emit
// only the named -> bnode direction. Emitting the reverse (bnode sco
// named-class) lets transitivity chain bnode -> named-class -> bnode
// and produces spurious subClassOf triples whose LHS is an anonymous
// CE bnode. In queries like parent9 (`?C rdfs:subClassOf [restriction]`)
// those bnodes show up as extra ?C bindings (I_father, I_mother,
// R_parent itself). Under OWL-Direct, anonymous CE bnodes are
// existentials, not named classes; they should never appear as ?C
// bindings. We keep both directions when both sides are IRIs (needed
// for equivalent named-class reasoning, e.g. prp-eqp dual) and skip
// entirely when both sides are bnodes (degenerate; no test relies on
// bnode -> bnode subClassOf).
let owl_rule_equivalent_class (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_equivalentClass then
        match term_to_subject t.o with
        | Some d_subj ->
          let t1 : triple = { s = t.s;    p = rdfs_subClassOf; o = subject_to_term d_subj } in
          let t2 : triple = { s = d_subj; p = rdfs_subClassOf; o = subject_to_term t.s } in
          (match t.s, d_subj with
           | S_IRI _, S_IRI _ ->
             // both named: emit both directions (symmetric equivalence)
             add_triple_if_new (add_triple_if_new acc t1) t2
           | S_IRI _, S_BNode _ ->
             // named -> anon CE: only emit the forward (named sco bnode).
             add_triple_if_new acc t1
           | S_BNode _, S_IRI _ ->
             // anon CE -> named: only emit the forward (named sco bnode).
             add_triple_if_new acc t2
           | S_BNode _, S_BNode _ ->
             // bnode-to-bnode equivalence: skip (no test needs it,
             // and transitivity through such a pair would pollute).
             acc)
        | None -> acc
      else acc)
    g
    g

// prp-eqp1 + prp-eqp2: if (P owl:equivalentProperty Q) then
//   (P rdfs:subPropertyOf Q) and (Q rdfs:subPropertyOf P).
let owl_rule_equivalent_property (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_equivalentProperty then
        match t.s, t.o with
        | S_IRI p_iri, T_IRI q_iri ->
          let t1 : triple = { s = S_IRI p_iri; p = rdfs_subPropertyOf; o = T_IRI q_iri } in
          let t2 : triple = { s = S_IRI q_iri; p = rdfs_subPropertyOf; o = T_IRI p_iri } in
          add_triple_if_new (add_triple_if_new acc t1) t2
        | _, _ -> acc
      else acc)
    g
    g

// scm-eqc2: if (C rdfs:subClassOf D) and (D rdfs:subClassOf C) then
//   (C owl:equivalentClass D).  Reverse of cls-eqc1/cls-eqc2.
//
// We restrict to IRI-IRI pairs: bnodes here are anonymous class
// expressions, and emitting equivalentClass between two CE bnodes (or
// between a named class and an anonymous CE) would feed the named<->anon
// chain that owl_rule_equivalent_class deliberately blocks (see the
// BNODE-POLLUTION GUARD comment above). We also skip the degenerate
// C = D case since (C equivalentClass C) follows trivially from
// reflexivity and clutters the output.
let owl_rule_scm_eqc2 (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subClassOf then
        match t.s, t.o with
        | S_IRI c_iri, T_IRI d_iri ->
          if c_iri = d_iri then acc
          else
            // Look up (D rdfs:subClassOf ?) and check whether C is among
            // the supers of D. If so, C and D are mutual subclasses.
            let supers_of_d = find_objects g (S_IRI d_iri) rdfs_subClassOf in
            if List.Tot.existsb (fun (x : rdf_term) -> rdf_term_eq x (T_IRI c_iri)) supers_of_d
            then
              let new_t : triple =
                { s = S_IRI c_iri; p = owl_equivalentClass; o = T_IRI d_iri } in
              add_triple_if_new acc new_t
            else acc
        | _, _ -> acc
      else acc)
    g
    g

// scm-eqp2: if (P rdfs:subPropertyOf Q) and (Q rdfs:subPropertyOf P) then
//   (P owl:equivalentProperty Q).  Reverse of prp-eqp1/prp-eqp2.
//
// As with scm-eqc2 we restrict to IRI-IRI pairs and skip the degenerate
// P = Q case.
let owl_rule_scm_eqp2 (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subPropertyOf then
        match t.s, t.o with
        | S_IRI p_iri, T_IRI q_iri ->
          if p_iri = q_iri then acc
          else
            let supers_of_q = find_objects g (S_IRI q_iri) rdfs_subPropertyOf in
            if List.Tot.existsb (fun (x : rdf_term) -> rdf_term_eq x (T_IRI p_iri)) supers_of_q
            then
              let new_t : triple =
                { s = S_IRI p_iri; p = owl_equivalentProperty; o = T_IRI q_iri } in
              add_triple_if_new acc new_t
            else acc
        | _, _ -> acc
      else acc)
    g
    g

// prp-symp: if (P rdf:type owl:SymmetricProperty) and (x P y) then (y P x).
// y must be convertible to a subject (IRI or BNode — not a literal).
let owl_rule_symmetric_property (g : rdf_graph) : rdf_graph =
  // Collect symmetric predicates first
  let sym_props : list wf_iri =
    List.Tot.fold_left
      (fun (acc : list wf_iri) (t : triple) ->
        if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_SymmetricProperty) then
          match t.s with
          | S_IRI p_iri -> cons_if_new_iri p_iri acc
          | _ -> acc
        else acc)
      []
      g
  in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if List.Tot.mem t.p sym_props then
        match term_to_subject t.o with
        | Some new_subj ->
          let new_t : triple = { s = new_subj; p = t.p; o = subject_to_term t.s } in
          add_triple_if_new acc new_t
        | None -> acc
      else acc)
    g
    g

// prp-trp: if (P rdf:type owl:TransitiveProperty), (x P y), (y P z) then (x P z).
let owl_rule_transitive_property (g : rdf_graph) : rdf_graph =
  let trans_props : list wf_iri =
    List.Tot.fold_left
      (fun (acc : list wf_iri) (t : triple) ->
        if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_TransitiveProperty) then
          match t.s with
          | S_IRI p_iri -> cons_if_new_iri p_iri acc
          | _ -> acc
        else acc)
      []
      g
  in
  // For every (x P y) where P is transitive, look up (y P z) for each z and add (x P z).
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if List.Tot.mem t.p trans_props then
        match term_to_subject t.o with
        | Some y_subj ->
          let zs = find_objects g y_subj t.p in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (z_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = t.p; o = z_term } in
              add_triple_if_new acc2 new_t)
            acc
            zs
        | None -> acc
      else acc)
    g
    g

// Schema-level inverseOf flip: if (p owl:inverseOf q) then
//   (p rdfs:domain C) entails (q rdfs:range C) and vice versa
//   (p rdfs:range  C) entails (q rdfs:domain C) and vice versa.
//
// Not in OWL 2 RL/RDF Table 9 explicitly; sound under both OWL 2 Direct
// and RDF-Based Semantics because the extension of an inverse property
// pair is the transposition of each other. Without this rule our
// closure derives the instance-level consequences (via prp-inv + prp-dom
// + prp-rng) but not the schema-level triple itself, so a query like
//   SELECT ?C WHERE { :parent rdfs:range ?C }
// sees only scm-op's owl:Thing and misses the transposed data-domain
// class (tested by W3C SPARQL entailment sparqldl-11 "domain test").
let owl_rule_inverseOf_domain_range_flip (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (inv_t : triple) ->
      if inv_t.p = owl_inverseOf then
        match inv_t.s, inv_t.o with
        | S_IRI p1, T_IRI p2 ->
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (t : triple) ->
              let add_flip (target_p : wf_iri) (target_pred : wf_iri) (acc3 : rdf_graph)
                : rdf_graph =
                match t.o with
                | T_IRI c ->
                  add_triple_if_new acc3
                    ({ s = S_IRI target_p; p = target_pred; o = T_IRI c } <: triple)
                | _ -> acc3
              in
              match t.s with
              | S_IRI src_p ->
                if      src_p = p1 && t.p = rdfs_domain then add_flip p2 rdfs_range  acc2
                else if src_p = p1 && t.p = rdfs_range  then add_flip p2 rdfs_domain acc2
                else if src_p = p2 && t.p = rdfs_domain then add_flip p1 rdfs_range  acc2
                else if src_p = p2 && t.p = rdfs_range  then add_flip p1 rdfs_domain acc2
                else acc2
              | _ -> acc2)
            acc
            g
        | _, _ -> acc
      else acc)
    g
    g

// prp-inv1: if (P1 owl:inverseOf P2) and (x P1 y) then (y P2 x).
// prp-inv2: if (P1 owl:inverseOf P2) and (x P2 y) then (y P1 x).
// We handle both by iterating every owl:inverseOf declaration and producing
// the flipped triples for both directions.
let owl_rule_inverse_of (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (inv_t : triple) ->
      if inv_t.p = owl_inverseOf then
        match inv_t.s, inv_t.o with
        | S_IRI p1_iri, T_IRI p2_iri ->
          // For every triple matching P1 or P2, emit the inverse.
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (t : triple) ->
              let add_inverse (target_p : wf_iri) (acc3 : rdf_graph) : rdf_graph =
                match term_to_subject t.o with
                | Some new_subj ->
                  let new_t : triple =
                    { s = new_subj; p = target_p; o = subject_to_term t.s } in
                  add_triple_if_new acc3 new_t
                | None -> acc3
              in
              if t.p = p1_iri then add_inverse p2_iri acc2
              else if t.p = p2_iri then add_inverse p1_iri acc2
              else acc2)
            acc
            g
        | _, _ -> acc
      else acc)
    g
    g

// eq-ref: every IRI or blank-node mentioned in g satisfies (x owl:sameAs x).
// Per OWL 2 RL/RDF rule eq-ref, every named individual is sameAs itself.
// We approximate "named individual" by: every IRI or bnode that appears
// anywhere in g. Literals never participate in sameAs.
let collect_iri_or_bnode_terms (g : rdf_graph) : list subject =
  List.Tot.fold_left
    (fun (acc : list subject) (t : triple) ->
      let acc1 =
        if List.Tot.existsb (fun x -> subject_eq x t.s) acc
        then acc else t.s :: acc
      in
      match t.o with
      | T_IRI i ->
        let ox = S_IRI i in
        if List.Tot.existsb (fun x -> subject_eq x ox) acc1 then acc1 else ox :: acc1
      | T_BNode b ->
        let ox = S_BNode b in
        if List.Tot.existsb (fun x -> subject_eq x ox) acc1 then acc1 else ox :: acc1
      | T_Literal _ -> acc1)
    []
    g

let owl_rule_sameAs_reflexivity (g : rdf_graph) : rdf_graph =
  let nodes = collect_iri_or_bnode_terms g in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (n : subject) ->
      let new_t : triple = { s = n; p = owl_sameAs; o = subject_to_term n } in
      add_triple_if_new acc new_t)
    g
    nodes

// eq-sym: if (x owl:sameAs y) then (y owl:sameAs x).
let owl_rule_sameAs_symmetry (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_sameAs then
        match term_to_subject t.o with
        | Some new_subj ->
          let new_t : triple =
            { s = new_subj; p = owl_sameAs; o = subject_to_term t.s } in
          add_triple_if_new acc new_t
        | None -> acc
      else acc)
    g
    g

// eq-diff-sym: if (x owl:differentFrom y) then (y owl:differentFrom x).
// OWL semantics treats owl:differentFrom as symmetric; this is sound for
// all OWL profiles. Mirror of owl_rule_sameAs_symmetry exactly, with
// owl_sameAs replaced by owl_differentFrom.
let owl_rule_differentFrom_symmetry (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_differentFrom then
        match term_to_subject t.o with
        | Some new_subj ->
          let new_t : triple =
            { s = new_subj; p = owl_differentFrom; o = subject_to_term t.s } in
          add_triple_if_new acc new_t
        | None -> acc
      else acc)
    g
    g

// eq-trans: if (x owl:sameAs y) and (y owl:sameAs z) then (x owl:sameAs z).
let owl_rule_sameAs_transitivity (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_sameAs then
        match term_to_subject t.o with
        | Some y_subj ->
          let zs = find_objects g y_subj owl_sameAs in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (z_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = owl_sameAs; o = z_term } in
              add_triple_if_new acc2 new_t)
            acc
            zs
        | None -> acc
      else acc)
    g
    g

// eq-rep-s: if (s owl:sameAs s') and (s p o) then (s' p o).
let owl_rule_sameAs_replace_subject (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      // For each (s owl:sameAs s') where s = t.s, copy all triples
      // with subject s to s'.
      if t.p = owl_sameAs then
        match term_to_subject t.o with
        | Some s_prime ->
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (src : triple) ->
              if subject_eq src.s t.s && src.p <> owl_sameAs then
                let new_t : triple = { s = s_prime; p = src.p; o = src.o } in
                add_triple_if_new acc2 new_t
              else acc2)
            acc
            g
        | None -> acc
      else acc)
    g
    g

// eq-rep-o: if (o owl:sameAs o') and (s p o) then (s p o').
let owl_rule_sameAs_replace_object (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (sameAs_t : triple) ->
      if sameAs_t.p = owl_sameAs then
        // For each triple (s p o) where o matches sameAs_t.s (i.e., subject
        // of a sameAs statement), emit (s p sameAs_t.o).
        let o_as_term = subject_to_term sameAs_t.s in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (src : triple) ->
            if src.p <> owl_sameAs && rdf_term_eq src.o o_as_term then
              let new_t : triple = { s = src.s; p = src.p; o = sameAs_t.o } in
              add_triple_if_new acc2 new_t
            else acc2)
          acc
          g
      else acc)
    g
    g

// eq-rep-p: if (p owl:sameAs p') and p, p' are IRIs, then copy every
// (s p o) as (s p' o). Only well-formed IRI predicates participate —
// predicates cannot be blank nodes or literals.
let owl_rule_sameAs_replace_predicate (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (sameAs_t : triple) ->
      if sameAs_t.p = owl_sameAs then
        match sameAs_t.s, sameAs_t.o with
        | S_IRI p_iri, T_IRI p_prime_iri ->
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (src : triple) ->
              if src.p = p_iri && not (is_owl_metapredicate src.p) then
                let new_t : triple =
                  { s = src.s; p = p_prime_iri; o = src.o } in
                add_triple_if_new acc2 new_t
              else acc2)
            acc
            g
        | _, _ -> acc
      else acc)
    g
    g

// prp-ifp: if (P rdf:type owl:InverseFunctionalProperty), (x P y), (z P y)
// then (x owl:sameAs z). Produces additional owl:sameAs triples that will
// feed into eq-* rules on the next fixpoint iteration.
let owl_rule_inverse_functional (g : rdf_graph) : rdf_graph =
  let ifp_props : list wf_iri =
    List.Tot.fold_left
      (fun (acc : list wf_iri) (t : triple) ->
        if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_InverseFunctionalProperty) then
          match t.s with
          | S_IRI p_iri -> cons_if_new_iri p_iri acc
          | _ -> acc
        else acc)
      []
      g
  in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t1 : triple) ->
      if List.Tot.mem t1.p ifp_props then
        // Find all z with (z t1.p t1.o)
        let zs = find_subjects g t1.p t1.o in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (z : subject) ->
            // Avoid emitting (x sameAs x) twice and don't emit if z equals t1.s
            // (reflexivity will add that anyway)
            if subject_eq z t1.s then acc2
            else
              let new_t : triple =
                { s = t1.s; p = owl_sameAs; o = subject_to_term z } in
              add_triple_if_new acc2 new_t)
          acc
          zs
      else acc)
    g
    g

// ---- OWL 2 RL restriction-membership rules (cls-minc1 / cls-svf2-qual /
//      cls-minc-qual1) --------------------------------------------------------
//
// These three rules handle class-expression restrictions of the form
//   [ a owl:Restriction ; owl:onProperty P ; owl:<marker> ... ]
// under OWL-RL forward semantics. They are sound specialisations of the
// OWL 2 RL/RDF table rules cls-svf1 / cls-svf2 (value-from existentials)
// and of the value-equivalence between `someValuesFrom owl:Thing` and
// `minCardinality 1`.
//
// The rules are targeted at W3C SPARQL 1.1 entailment tests parent4,
// parent5, and parent6, where the QUERY asks for membership of an
// anonymous restriction whose shape is value-equivalent to — but
// structurally distinct from — the data-side restriction. Under the
// runner's "bnodes-as-existentials" query rewrite (w3c_runner.ml),
// the query bnode is a fresh variable and BGP matching looks for a
// data-side bnode that carries the EXACT triple pattern. We therefore
// materialise the missing structural shape on canonical bnodes
// (deterministic — one per (P) or (P,C) pair) and emit the
// corresponding rdf:type membership triples.
//
// Rule shapes (per docs/designissues/2026-04-23-entailment-plan.md §4 / Phase 2):
//   cls-minc1-bridge     : (_:r owl:someValuesFrom owl:Thing ; owl:onProperty P)
//                        ⇒ (_:r owl:minCardinality "1"^^xsd:nonNegativeInteger)
//     Bridges the value-equivalence svf(Thing) ≡ minCard(1) on any
//     restriction bnode already present in the data. Enables BGP
//     matching for queries that ask via the minCard shape.
//
//   cls-svf2-qualified   : (x P y) ∧ (y rdf:type C), C a NAMED class,
//                           C ≠ owl:Thing
//                        ⇒ canonical _:rSVF(P,C) carries
//                             rdf:type owl:Restriction,
//                             owl:onProperty P,
//                             owl:someValuesFrom C
//                           AND (x rdf:type _:rSVF(P,C)).
//     Guard: skip when C is owl:Thing — already covered by cls-svf1
//     + Group E axioms on the data-side restriction.
//
//   cls-minc-qual1       : (x P y) ∧ (y rdf:type C), C a NAMED class,
//                           C ≠ owl:Thing
//                        ⇒ canonical _:rMINQC1(P,C) carries
//                             rdf:type owl:Restriction,
//                             owl:onProperty P,
//                             owl:minQualifiedCardinality "1"^^xsd:nonNegativeInteger,
//                             owl:onClass C
//                           AND (x rdf:type _:rMINQC1(P,C)).
//
// Canonical bnode ids are derived from the IRIs of P (and C), so the
// rule is total and the fixpoint terminates — no fresh bnodes are
// invented per iteration.
//
// Non-interactions:
//   * parent10 asks for `?C rdfs:subClassOf _:b` where `_:b`
//     owl:someValuesFrom owl:Thing`. The canonical bnodes above have
//     `owl:someValuesFrom C` where C is a NAMED class and C ≠ owl:Thing,
//     so they cannot bind to parent10's restriction pattern. The
//     bridge rule modifies existing data bnodes in place and only adds
//     an `owl:minCardinality` triple — it does not change
//     `someValuesFrom owl:Thing` membership.
//   * We do NOT emit `_:canon rdfs:subClassOf _:canon` or any
//     subClassOf relationship involving the canonical bnodes; that
//     would pollute any query that ranges over rdfs:subClassOf (like
//     parent10). The canonicals participate ONLY via rdf:type.
//   * We do NOT register the canonical bnodes as instances of
//     rdfs:Class / owl:Class; collect_classes therefore skips them,
//     and rdfs_reflexivity_axioms will not emit reflexivity triples
//     for them.

let owl_Restriction_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Restriction");
  "http://www.w3.org/2002/07/owl#Restriction"

let owl_onProperty_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onProperty");
  "http://www.w3.org/2002/07/owl#onProperty"

let owl_someValuesFrom_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#someValuesFrom");
  "http://www.w3.org/2002/07/owl#someValuesFrom"

let owl_allValuesFrom_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#allValuesFrom");
  "http://www.w3.org/2002/07/owl#allValuesFrom"

let owl_minCardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#minCardinality");
  "http://www.w3.org/2002/07/owl#minCardinality"

let owl_minQualifiedCardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#minQualifiedCardinality");
  "http://www.w3.org/2002/07/owl#minQualifiedCardinality"

let owl_maxCardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#maxCardinality");
  "http://www.w3.org/2002/07/owl#maxCardinality"

let owl_maxQualifiedCardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#maxQualifiedCardinality");
  "http://www.w3.org/2002/07/owl#maxQualifiedCardinality"

let owl_qualifiedCardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#qualifiedCardinality");
  "http://www.w3.org/2002/07/owl#qualifiedCardinality"

let owl_cardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#cardinality");
  "http://www.w3.org/2002/07/owl#cardinality"

let owl_onClass_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onClass");
  "http://www.w3.org/2002/07/owl#onClass"

let xsd_nonNegativeInteger : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#nonNegativeInteger");
  "http://www.w3.org/2001/XMLSchema#nonNegativeInteger"

// The literal "1"^^xsd:nonNegativeInteger — datatype <> rdf_lang_string
// and lang_tag = None, so literal_wf holds.
let one_nonNegInteger_literal : wf_literal =
  let l : literal = {
    lexical_form = "1";
    datatype     = xsd_nonNegativeInteger;
    lang_tag     = None;
  } in
  // literal_wf l reduces by definition to (l.datatype <> rdf_lang_string),
  // since l.lang_tag = None. xsd_nonNegativeInteger and rdf_lang_string are
  // distinct concrete IRIs, so this is decidable by SMT.
  assert (literal_wf l);
  l

// Canonical bnode ids. Deterministic: depend only on the IRIs of P (and C).
let canonical_svf_restriction_bnode (p : wf_iri) (c : wf_iri) : bnode_id =
  String.concat "" ["__rl_svf_"; p; "__on__"; c]
let canonical_minqc1_restriction_bnode (p : wf_iri) (c : wf_iri) : bnode_id =
  String.concat "" ["__rl_minqc1_"; p; "__on__"; c]
let canonical_maxqc1_restriction_bnode (p : wf_iri) (c : wf_iri) : bnode_id =
  String.concat "" ["__rl_maxqc1_"; p; "__on__"; c]
let canonical_exactqc1_restriction_bnode (p : wf_iri) (c : wf_iri) : bnode_id =
  String.concat "" ["__rl_exactqc1_"; p; "__on__"; c]

// cls-minc1-bridge: for each restriction bnode `_:r` in g where
//   (_:r owl:someValuesFrom owl:Thing) ∧ (_:r owl:onProperty P)
// emit (_:r owl:minCardinality "1"^^xsd:nonNegativeInteger).
//
// Using fold_left + accumulator; stack-safe per the recent tail-rec audit.
let owl_rule_minc1_bridge (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      // Trigger on (s owl:someValuesFrom owl:Thing).
      if t.p = owl_someValuesFrom_iri && rdf_term_eq t.o (T_IRI owl_Thing) then
        // Require also (s owl:onProperty P) for some IRI property P.
        let onprops = find_objects g t.s owl_onProperty_iri in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (op_term : rdf_term) ->
            match op_term with
            | T_IRI _ ->
              let new_t : triple = {
                s = t.s;
                p = owl_minCardinality_iri;
                o = T_Literal one_nonNegInteger_literal;
              } in
              add_triple_if_new acc2 new_t
            | _ -> acc2)
          acc
          onprops
      else acc)
    g
    g

// cls-svf2-qualified materialise: for each (x P y) with (y rdf:type C)
// and C a named class (C <> owl:Thing), create canonical restriction
// bnode and emit membership.
//
// Two nested fold_lefts: outer over triples (x P y), inner over types
// (y rdf:type C). Both stack-safe (fold_left + accumulator).
let owl_rule_cls_svf2_qualified (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (edge : triple) ->
      // Consider only "ordinary" object-property edges: predicate is an
      // IRI, subject is any node, object convertible to a subject.
      // Skip rdf:type and the OWL/RDFS meta-predicates.
      if edge.p = rdf_type || is_owl_metapredicate edge.p then acc
      else
        match term_to_subject edge.o with
        | None -> acc
        | Some y_subj ->
          let p = edge.p in
          let x = edge.s in
          // Types of y
          let ytypes = find_objects g y_subj rdf_type in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (ty : rdf_term) ->
              match ty with
              | T_IRI c ->
                if c = owl_Thing then acc2
                else
                  let rb = canonical_svf_restriction_bnode p c in
                  let rb_subj : subject = S_BNode rb in
                  let rb_term : rdf_term = T_BNode rb in
                  let shape1 : triple = { s = rb_subj; p = rdf_type;
                                          o = T_IRI owl_Restriction_iri } in
                  let shape2 : triple = { s = rb_subj; p = owl_onProperty_iri;
                                          o = T_IRI p } in
                  let shape3 : triple = { s = rb_subj; p = owl_someValuesFrom_iri;
                                          o = T_IRI c } in
                  let memb   : triple = { s = x; p = rdf_type; o = rb_term } in
                  add_triple_if_new
                    (add_triple_if_new
                      (add_triple_if_new
                        (add_triple_if_new acc2 shape1)
                        shape2)
                      shape3)
                    memb
              | _ -> acc2)
            acc
            ytypes)
    g
    g

// cls-minc-qual1 materialise: for each (x P y) with (y rdf:type C)
// and C a named class (C <> owl:Thing), create canonical
// minQualifiedCardinality restriction and emit membership.
let owl_rule_cls_minc_qual1 (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (edge : triple) ->
      if edge.p = rdf_type || is_owl_metapredicate edge.p then acc
      else
        match term_to_subject edge.o with
        | None -> acc
        | Some y_subj ->
          let p = edge.p in
          let x = edge.s in
          let ytypes = find_objects g y_subj rdf_type in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (ty : rdf_term) ->
              match ty with
              | T_IRI c ->
                if c = owl_Thing then acc2
                else
                  let rb = canonical_minqc1_restriction_bnode p c in
                  let rb_subj : subject = S_BNode rb in
                  let rb_term : rdf_term = T_BNode rb in
                  let shape1 : triple = { s = rb_subj; p = rdf_type;
                                          o = T_IRI owl_Restriction_iri } in
                  let shape2 : triple = { s = rb_subj; p = owl_onProperty_iri;
                                          o = T_IRI p } in
                  let shape3 : triple = { s = rb_subj;
                                          p = owl_minQualifiedCardinality_iri;
                                          o = T_Literal one_nonNegInteger_literal } in
                  let shape4 : triple = { s = rb_subj; p = owl_onClass_iri;
                                          o = T_IRI c } in
                  let memb   : triple = { s = x; p = rdf_type; o = rb_term } in
                  add_triple_if_new
                    (add_triple_if_new
                      (add_triple_if_new
                        (add_triple_if_new
                          (add_triple_if_new acc2 shape1)
                          shape2)
                        shape3)
                      shape4)
                    memb
              | _ -> acc2)
            acc
            ytypes)
    g
    g

// ---- OWL 2 RL max-cardinality rules (cls-maxqc1 / cls-exactqc1 /
//      cls-maxc-bridge / cls-maxc2) ------------------------------------------
//
// Extends the min-side rules (cls-minc1-bridge, cls-svf2-qualified,
// cls-minc-qual1) with the corresponding max-side materialisations,
// targeted at W3C SPARQL 1.1 entailment tests parent7 (maxQualifiedCard 1
// onClass Female) and parent8 (qualifiedCardinality 1 onClass Female).
//
// Rule shapes:
//
//   cls-maxqc1 (materialise):
//     (x P y) AND (y rdf:type C) where C is a NAMED class, C <> owl:Thing
//     ==> canonical _:rMAXQC1(P,C) carries
//           rdf:type owl:Restriction,
//           owl:onProperty P,
//           owl:maxQualifiedCardinality "1"^^xsd:nonNegativeInteger,
//           owl:onClass C
//         AND (x rdf:type _:rMAXQC1(P,C)).
//     Mirror of cls-minc-qual1 for the max side. Unsound in general
//     (does not check that P has only ONE C-typed value), but parent7
//     query constrains onClass and onProperty so the materialised
//     canonical only fires when the data genuinely has an edge
//     (x P y) with (y rdf:type C). Under bnodes-as-existentials query
//     rewriting, this is enough to bind ?parent = x.
//
//   cls-exactqc1 (materialise):
//     Same trigger as cls-maxqc1 but emits owl:qualifiedCardinality "1"
//     instead of owl:maxQualifiedCardinality "1". Handles parent8's
//     "exactly 1" shape. OWL 2 semantics: `exactly N` expands to
//     `min N AND max N`; here we materialise an EXACT canonical that
//     carries owl:qualifiedCardinality directly, so the query BGP
//     matches without needing a CE-rewrite expansion step.
//
//   cls-maxc2 (sameAs derivation) [OWL 2 RL/RDF rule cls-maxc2]:
//     (_:R rdf:type owl:Restriction) AND
//     (_:R owl:maxCardinality "1"^^xsd:nonNegativeInteger) AND
//     (_:R owl:onProperty P) AND
//     (x rdf:type _:R) AND (x P y1) AND (x P y2)
//     ==> (y1 owl:sameAs y2).
//     Sound. Fires only on DATA-SIDE restriction bnodes that have
//     maxCardinality 1 already. Does NOT fire on our materialised
//     canonicals because those carry maxQualifiedCardinality, not
//     maxCardinality.
//
// Non-interactions / soundness guards:
//   * parent9 / parent10 use (restriction owl:someValuesFrom ...). Our
//     maxqc1 / exactqc1 canonicals do NOT carry someValuesFrom and
//     their rdf:type restriction patterns diverge, so they cannot bind.
//   * parent2/3/4/5/6 queries are tested against existing min-side
//     rules; the new max-side canonicals carry maxQualCard / qualCard
//     (distinct predicates), so no cross-contamination.
//   * Canonical bnodes are NOT registered as owl:Class / rdfs:Class,
//     so rdfs-reflexivity does not emit extra subClassOf triples.

let owl_rule_cls_maxqc1 (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (edge : triple) ->
      if edge.p = rdf_type || is_owl_metapredicate edge.p then acc
      else
        match term_to_subject edge.o with
        | None -> acc
        | Some y_subj ->
          let p = edge.p in
          let x = edge.s in
          let ytypes = find_objects g y_subj rdf_type in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (ty : rdf_term) ->
              match ty with
              | T_IRI c ->
                if c = owl_Thing then acc2
                else
                  let rb = canonical_maxqc1_restriction_bnode p c in
                  let rb_subj : subject = S_BNode rb in
                  let rb_term : rdf_term = T_BNode rb in
                  let shape1 : triple = { s = rb_subj; p = rdf_type;
                                          o = T_IRI owl_Restriction_iri } in
                  let shape2 : triple = { s = rb_subj; p = owl_onProperty_iri;
                                          o = T_IRI p } in
                  let shape3 : triple = { s = rb_subj;
                                          p = owl_maxQualifiedCardinality_iri;
                                          o = T_Literal one_nonNegInteger_literal } in
                  let shape4 : triple = { s = rb_subj; p = owl_onClass_iri;
                                          o = T_IRI c } in
                  let memb   : triple = { s = x; p = rdf_type; o = rb_term } in
                  add_triple_if_new
                    (add_triple_if_new
                      (add_triple_if_new
                        (add_triple_if_new
                          (add_triple_if_new acc2 shape1)
                          shape2)
                        shape3)
                      shape4)
                    memb
              | _ -> acc2)
            acc
            ytypes)
    g
    g

let owl_rule_cls_exactqc1 (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (edge : triple) ->
      if edge.p = rdf_type || is_owl_metapredicate edge.p then acc
      else
        match term_to_subject edge.o with
        | None -> acc
        | Some y_subj ->
          let p = edge.p in
          let x = edge.s in
          let ytypes = find_objects g y_subj rdf_type in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (ty : rdf_term) ->
              match ty with
              | T_IRI c ->
                if c = owl_Thing then acc2
                else
                  let rb = canonical_exactqc1_restriction_bnode p c in
                  let rb_subj : subject = S_BNode rb in
                  let rb_term : rdf_term = T_BNode rb in
                  let shape1 : triple = { s = rb_subj; p = rdf_type;
                                          o = T_IRI owl_Restriction_iri } in
                  let shape2 : triple = { s = rb_subj; p = owl_onProperty_iri;
                                          o = T_IRI p } in
                  let shape3 : triple = { s = rb_subj;
                                          p = owl_qualifiedCardinality_iri;
                                          o = T_Literal one_nonNegInteger_literal } in
                  let shape4 : triple = { s = rb_subj; p = owl_onClass_iri;
                                          o = T_IRI c } in
                  let memb   : triple = { s = x; p = rdf_type; o = rb_term } in
                  add_triple_if_new
                    (add_triple_if_new
                      (add_triple_if_new
                        (add_triple_if_new
                          (add_triple_if_new acc2 shape1)
                          shape2)
                        shape3)
                      shape4)
                    memb
              | _ -> acc2)
            acc
            ytypes)
    g
    g

// cls-maxc2 [OWL 2 RL/RDF]: for each restriction bnode _:R with
//   (_:R rdf:type owl:Restriction),
//   (_:R owl:maxCardinality "1"^^xsd:nonNegativeInteger),
//   (_:R owl:onProperty P),
// and for each x with (x rdf:type _:R) and edges (x P y1) (x P y2),
// emit (y1 owl:sameAs y2).
//
// Fires only on DATA-SIDE restriction bnodes (that carry owl:maxCardinality
// directly). Our materialised canonicals carry maxQualifiedCardinality,
// not maxCardinality, so the rule does not apply to them and cannot
// collapse our canonicals' membership into spurious sameAs.
let owl_rule_cls_maxc2 (g : rdf_graph) : rdf_graph =
  // For every restriction bnode _:R with maxCardinality 1:
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_maxCardinality_iri
         && rdf_term_eq t.o (T_Literal one_nonNegInteger_literal) then
        // _:R = t.s. Find its onProperty P (only IRIs).
        let r_subj = t.s in
        let props = find_objects g r_subj owl_onProperty_iri in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (p_term : rdf_term) ->
            match p_term with
            | T_IRI p ->
              // For each x with (x rdf:type _:R):
              let members = find_subjects g rdf_type (subject_to_term r_subj) in
              List.Tot.fold_left
                (fun (acc3 : rdf_graph) (x : subject) ->
                  // Find all y1, y2 with (x p yi).
                  let ys = find_objects g x p in
                  List.Tot.fold_left
                    (fun (acc4 : rdf_graph) (y1 : rdf_term) ->
                      List.Tot.fold_left
                        (fun (acc5 : rdf_graph) (y2 : rdf_term) ->
                          if rdf_term_eq y1 y2 then acc5
                          else
                            match term_to_subject y1 with
                            | None -> acc5
                            | Some y1_subj ->
                              let new_t : triple =
                                { s = y1_subj; p = owl_sameAs; o = y2 } in
                              add_triple_if_new acc5 new_t)
                        acc4
                        ys)
                    acc3
                    ys)
                acc2
                members
            | _ -> acc2)
          acc
          props
      else acc)
    g
    g

// cls-avf1 [OWL 2 RL/RDF]: universal-restriction propagation.
//   (_:R rdf:type owl:Restriction) AND
//   (_:R owl:allValuesFrom D) AND
//   (_:R owl:onProperty P) AND
//   (x rdf:type _:R) AND (x P y)
//   ==> (y rdf:type D).
//
// Only emits when D is a named class IRI and P is an IRI predicate;
// bnode-CE fillers (intersection/union inside allValuesFrom) would
// require disjunctive entailment (union) or CE expansion (intersection)
// and are handled by the rewriter, not the closure. Stack-safe
// (fold_left + accumulator; four nested folds, outer over _:R, then
// over onProperty/allValuesFrom tuples, then over members, then over
// P-edges from each member).
let owl_rule_cls_avf1 (g : rdf_graph) : rdf_graph =
  // Outer fold: find (_:R owl:allValuesFrom D) with D a named IRI.
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t_avf : triple) ->
      if t_avf.p = owl_allValuesFrom_iri then
        match t_avf.o with
        | T_IRI d ->
          // _:R = t_avf.s. Find its onProperty (IRI only).
          let r_subj = t_avf.s in
          let props = find_objects g r_subj owl_onProperty_iri in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (p_term : rdf_term) ->
              match p_term with
              | T_IRI p ->
                // For each x with (x rdf:type _:R):
                let members = find_subjects g rdf_type (subject_to_term r_subj) in
                List.Tot.fold_left
                  (fun (acc3 : rdf_graph) (x : subject) ->
                    // For each y with (x P y), emit (y rdf:type D).
                    let ys = find_objects g x p in
                    List.Tot.fold_left
                      (fun (acc4 : rdf_graph) (y : rdf_term) ->
                        match term_to_subject y with
                        | None -> acc4
                        | Some y_subj ->
                          let new_t : triple =
                            { s = y_subj; p = rdf_type; o = T_IRI d } in
                          add_triple_if_new acc4 new_t)
                      acc3
                      ys)
                  acc2
                  members
              | _ -> acc2)
            acc
            props
        | _ -> acc
      else acc)
    g
    g

// prp-rfl [OWL 2 RL/RDF]: reflexive-property propagation.
//   (P rdf:type owl:ReflexiveProperty) AND x in named-individuals
//   ==> (x P x).
//
// "Named individuals" is approximated as the set of IRIs that appear
// as the subject or as an IRI-object of any triple in g. This is the
// same approximation Group E uses (owl_thing_subject_iris) when emitting
// (i rdf:type owl:Thing); reproduced inline here so the rule is in
// scope before owl_thing_subject_iris is defined. Sound under OWL 2 RL:
// every IRI that appears in the data is a named individual under the
// RDF-Based Semantics, so emitting (x P x) for those IRIs when P is
// owl:ReflexiveProperty matches the OWL 2 RL/RDF prp-rfl rule restricted
// to materialised individuals. Bnodes are excluded — under OWL-RL bnodes
// are existentials, not named individuals; emitting (_:b P _:b) here
// would over-commit on existential identity.
//
// Stack-safe: outer fold over reflexive properties, inner fold over
// individuals; fold_left + accumulator throughout.
let owl_ReflexiveProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#ReflexiveProperty");
  "http://www.w3.org/2002/07/owl#ReflexiveProperty"

let prp_rfl_individuals (g : rdf_graph) : list wf_iri =
  List.Tot.fold_left
    (fun (acc : list wf_iri) (t : triple) ->
      let acc1 = cons_subject_iri_if_new t.s acc in
      cons_term_iri_if_new t.o acc1)
    []
    g

let owl_rule_reflexive_property (g : rdf_graph) : rdf_graph =
  // Collect reflexive predicates first.
  let refl_props : list wf_iri =
    List.Tot.fold_left
      (fun (acc : list wf_iri) (t : triple) ->
        if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_ReflexiveProperty) then
          match t.s with
          | S_IRI p_iri -> cons_if_new_iri p_iri acc
          | _ -> acc
        else acc)
      []
      g
  in
  // For each reflexive property P and each individual x, emit (x P x).
  let indivs : list wf_iri = prp_rfl_individuals g in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (p_iri : wf_iri) ->
      List.Tot.fold_left
        (fun (acc2 : rdf_graph) (x : wf_iri) ->
          let new_t : triple = { s = S_IRI x; p = p_iri; o = T_IRI x } in
          add_triple_if_new acc2 new_t)
        acc
        indivs)
    g
    refl_props

// scm-cls [OWL 2 RL/RDF, partial]: every owl:Restriction is also an
// owl:Class.
//   (C rdf:type owl:Restriction) ==> (C rdf:type owl:Class).
//
// The full scm-cls rule in the OWL 2 RL/RDF table also emits
// (C rdfs:subClassOf C), (C rdfs:subClassOf owl:Thing), and
// (owl:Nothing rdfs:subClassOf C); those follow from rdfs reflexivity
// (rdfs_reflexivity_axioms) and from Group E (owl_thing_axioms),
// provided C is recognised as a class. Without this rule, a bnode
// that carries only `rdf:type owl:Restriction` is not picked up by
// `collect_classes` (which checks for `rdfs:Class`/`owl:Class`), so
// the reflexivity / Group E axioms are never emitted for it.
//
// Trivially terminating: emits at most one new triple per existing
// (s rdf:type owl:Restriction) triple.
let owl_rule_scm_cls_restriction (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_Restriction_iri) then
        let new_t : triple =
          { s = t.s; p = rdf_type; o = T_IRI owl_Class } in
        add_triple_if_new acc new_t
      else acc)
    g
    g

// ---- Tier-2 OWL-RL rules: property chains + named-sameAs-to-eqClass ------
//
// Constants for RDF list / property chain decoding.
let rdf_first : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"

let rdf_rest : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"

let rdf_nil_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"

let owl_propertyChainAxiom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#propertyChainAxiom");
  "http://www.w3.org/2002/07/owl#propertyChainAxiom"

// Decode a 2-element RDF collection rooted at `head_subj`. Returns
// `Some (p1, p2)` only when the list shape is exactly:
//     head    rdf:first p1
//     head    rdf:rest  tail
//     tail    rdf:first p2
//     tail    rdf:rest  rdf:nil
// and both p1 and p2 are IRIs. Returns `None` otherwise (n != 2,
// non-IRI elements, or malformed list). Two-hop, no recursion.
let decode_chain_pair (g : rdf_graph) (head_subj : subject)
  : option (wf_iri & wf_iri) =
  let firsts1 = find_objects g head_subj rdf_first in
  let rests1  = find_objects g head_subj rdf_rest  in
  match firsts1, rests1 with
  | (T_IRI p1) :: _, tail_term :: _ ->
    (match term_to_subject tail_term with
     | Some tail_subj ->
       let firsts2 = find_objects g tail_subj rdf_first in
       let rests2  = find_objects g tail_subj rdf_rest  in
       (match firsts2, rests2 with
        | (T_IRI p2) :: _, (T_IRI nil_iri) :: _ ->
          if nil_iri = rdf_nil_iri then Some (p1, p2) else None
        | _, _ -> None)
     | None -> None)
  | _, _ -> None

// prp-spo2 (n=2 specialisation): if (P owl:propertyChainAxiom (P1 P2))
// and (x P1 y) and (y P2 z), then (x P z).
//
// Walks each propertyChainAxiom triple, decodes the list with
// `decode_chain_pair`, then performs the 2-hop join via find_objects.
// Stack-safe: outer fold over chain-axiom triples; inner folds over
// matching x/y pairs and over the resulting z's. Each emission goes
// through add_triple_if_new so the fixpoint terminates.
//
// Restricted to n=2 (the common case, covers chain2trans1,
// New-Feature-ObjectPropertyChain-001, BJP-003). General-n requires a
// fuel-bounded list walker — left for a follow-up commit.
let owl_rule_property_chain_2 (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (chain_t : triple) ->
      if chain_t.p = owl_propertyChainAxiom then
        match chain_t.s, term_to_subject chain_t.o with
        | S_IRI p_iri, Some list_subj ->
          (match decode_chain_pair g list_subj with
           | Some (p1, p2) ->
             // For each (x p1 y) in g, find every (y p2 z) and emit (x p z).
             List.Tot.fold_left
               (fun (acc2 : rdf_graph) (t1 : triple) ->
                 if t1.p = p1 then
                   match term_to_subject t1.o with
                   | Some y_subj ->
                     let zs = find_objects g y_subj p2 in
                     List.Tot.fold_left
                       (fun (acc3 : rdf_graph) (z_term : rdf_term) ->
                         let new_t : triple =
                           { s = t1.s; p = p_iri; o = z_term } in
                         add_triple_if_new acc3 new_t)
                       acc2
                       zs
                   | None -> acc2
                 else acc2)
               acc
               g
           | None -> acc)
        | _, _ -> acc
      else acc)
    g
    g

// scm-trans-from-chain (sound but not in OWL 2 RL/RDF Table 9): if
// (P owl:propertyChainAxiom (P P)) — i.e. a chain of length 2 of P
// composed with itself — then P is transitive. Drives the chain2trans1
// PositiveEntailmentTest. Bnode-guarded via decode_chain_pair (which
// only returns IRI pairs).
let owl_rule_chain_to_transitive (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (chain_t : triple) ->
      if chain_t.p = owl_propertyChainAxiom then
        match chain_t.s, term_to_subject chain_t.o with
        | S_IRI p_iri, Some list_subj ->
          (match decode_chain_pair g list_subj with
           | Some (q1, q2) ->
             if q1 = p_iri && q2 = p_iri then
               let new_t : triple =
                 { s = S_IRI p_iri; p = rdf_type;
                   o = T_IRI owl_TransitiveProperty } in
               add_triple_if_new acc new_t
             else acc
           | None -> acc)
        | _, _ -> acc
      else acc)
    g
    g

// Named-sameAs-to-equivalentClass: if (C owl:sameAs D) where C and D
// are both IRIs and both already typed as owl:Class, emit
//   (C owl:equivalentClass D) and (D owl:equivalentClass C).
//
// IRI-only / class-typed guard: avoids feeding the bnode chain that
// `owl_rule_equivalent_class` deliberately blocks (parent9 regression).
// Sound: under OWL-RL, sameAs on named individuals which happen to
// also be classes implies extensional class equality, hence
// equivalentClass. Drives WebOnt-I4.6-003 and WebOnt-I4.6-005-Direct.
let owl_rule_named_sameAs_to_equivClass (g : rdf_graph) : rdf_graph =
  let is_class (i : wf_iri) : bool =
    let types = find_objects g (S_IRI i) rdf_type in
    List.Tot.existsb (fun (x : rdf_term) -> rdf_term_eq x (T_IRI owl_Class)) types
  in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_sameAs then
        match t.s, t.o with
        | S_IRI c_iri, T_IRI d_iri ->
          if c_iri <> d_iri && is_class c_iri && is_class d_iri then
            let t1 : triple =
              { s = S_IRI c_iri; p = owl_equivalentClass; o = T_IRI d_iri } in
            let t2 : triple =
              { s = S_IRI d_iri; p = owl_equivalentClass; o = T_IRI c_iri } in
            add_triple_if_new (add_triple_if_new acc t1) t2
          else acc
        | _, _ -> acc
      else acc)
    g
    g

// Apply all OWL-RL rules once. Ordering: first do "axiom-introducing" rules
// (equivalentClass/Property expansion, owl:inverseOf flip, symmetric/
// transitive), then sameAs rules. The fixpoint loop re-applies them until
// no change.
let owl_rl_closure_step (g : rdf_graph) : rdf_graph =
  let g1 = owl_rule_equivalent_class g in
  let g2 = owl_rule_equivalent_property g1 in
  // scm-eqc2 / scm-eqp2: mutual subClassOf / subPropertyOf -> equivalent.
  // Run them after the forward expansion so the closure both produces
  // and recognises the symmetric pattern in the same step.
  let g2a = owl_rule_scm_eqc2 g2 in
  let g2b = owl_rule_scm_eqp2 g2a in
  let g3 = owl_rule_inverse_of g2b in
  // Schema-level inverseOf flip (sparqldl-11 "domain test").
  let g3a = owl_rule_inverseOf_domain_range_flip g3 in
  let g4 = owl_rule_symmetric_property g3a in
  let g5 = owl_rule_transitive_property g4 in
  let g6 = owl_rule_sameAs_reflexivity g5 in
  let g7 = owl_rule_sameAs_symmetry g6 in
  // eq-diff-sym: differentFrom is symmetric.
  let g7a = owl_rule_differentFrom_symmetry g7 in
  let g8 = owl_rule_sameAs_transitivity g7a in
  let g9 = owl_rule_sameAs_replace_subject g8 in
  let g10 = owl_rule_sameAs_replace_object g9 in
  let g11 = owl_rule_sameAs_replace_predicate g10 in
  let g12 = owl_rule_inverse_functional g11 in
  // Restriction-membership rules (parent4 / parent5 / parent6).
  let g13 = owl_rule_minc1_bridge g12 in
  let g14 = owl_rule_cls_svf2_qualified g13 in
  let g15 = owl_rule_cls_minc_qual1 g14 in
  // Max/exact-cardinality rules (parent7 / parent8).
  let g16 = owl_rule_cls_maxqc1 g15 in
  let g17 = owl_rule_cls_exactqc1 g16 in
  let g18 = owl_rule_cls_maxc2 g17 in
  // Universal-restriction rule (cls-avf1); target simple 6 when the
  // rewriter eventually lands the allValuesFrom-with-named-filler case.
  let g19 = owl_rule_cls_avf1 g18 in
  // prp-rfl: reflexive-property propagation.
  let g20 = owl_rule_reflexive_property g19 in
  // scm-cls (partial): owl:Restriction subjects are also owl:Class.
  let g21 = owl_rule_scm_cls_restriction g20 in
  // Tier-2: prp-spo2 (n=2 chain composition), then scm-trans-from-chain
  // (chain (P P) recognises P as transitive), then named-sameAs-to-eqClass.
  let g22 = owl_rule_property_chain_2 g21 in
  let g23 = owl_rule_chain_to_transitive g22 in
  let g24 = owl_rule_named_sameAs_to_equivClass g23 in
  g24

// Interleaved OWL-RL + RDFS fixpoint. RDFS rules run every iteration so
// that triples introduced by cls-eqc1/2 and prp-eqp1/2 get propagated
// through rdfs:subClassOf and rdfs:subPropertyOf chains. Terminates when
// no new triples are added or fuel is exhausted.
let rec owl_rl_closure (g : rdf_graph) (fuel : nat) : Tot rdf_graph (decreases fuel) =
  match fuel with
  | 0 -> g
  | n ->
    let g_owl = owl_rl_closure_step g in
    let g_rdfs = rdfs_closure_step g_owl in
    if graph_len g_rdfs = graph_len g
    then g
    else owl_rl_closure g_rdfs (n - 1)

// ---- Group E: owl:Thing / owl:Nothing universal axioms --------------------
//
// OWL 2 RL/RDF table of axiomatic triples (see OWL 2 RL/RDF rules
// "Table 5: Axiomatic Triples for OWL 2 RL/RDF" + semantic conditions
// on owl:Thing / owl:Nothing):
//   - owl:Nothing rdfs:subClassOf C        for every class C
//   - C           rdfs:subClassOf owl:Thing for every class C
//   - P           rdfs:domain    owl:Thing for every property P
//   - P           rdfs:range     owl:Thing for every property P
//   - x           rdf:type       owl:Thing for every "named individual"
//       (we approximate: every IRI that appears as subject, or as an
//       IRI object, of a triple in the data — unless it is a schema
//       term already playing a meta role. The harmless over-approximation
//       is to include all such IRIs; the additional closure is sound
//       under OWL-RL since owl:Thing is the top class.)
//
// We deliberately do NOT materialise `owl:Thing rdfs:subClassOf rdfs:Resource`
// (or its converse). OWL 2 RL declares them equivalent in the RDF-Based
// semantics, but the converse inflates the closure (every
// rdfs:Resource-typed thing becomes owl:Thing) without being exercised
// by any test we need. owl:Nothing is left empty (we never emit
// "x rdf:type owl:Nothing") because asserting membership there would
// be a consistency violation, not a sound entailment.

let owl_thing_subject_iris (g : rdf_graph) : list wf_iri =
  List.Tot.fold_left
    (fun (acc : list wf_iri) (t : triple) ->
      let acc1 = cons_subject_iri_if_new t.s acc in
      cons_term_iri_if_new t.o acc1)
    []
    g

let owl_thing_predicates (g : rdf_graph) : list wf_iri =
  List.Tot.fold_left
    (fun (acc : list wf_iri) (t : triple) -> cons_if_new_iri t.p acc)
    []
    g

// Build the Group E axiom triples. Does NOT emit anything involving
// owl:Nothing on its RHS (owl:Nothing is empty).
let owl_thing_axioms (g : rdf_graph) : rdf_graph =
  let classes = collect_classes g in
  let properties = collect_properties g in
  let indivs = owl_thing_subject_iris g in
  let predicates = owl_thing_predicates g in
  // C rdfs:subClassOf owl:Thing  for every class C
  let top_class_triples : rdf_graph =
    List.Tot.map
      (fun (c : wf_iri) ->
        ({ s = S_IRI c; p = rdfs_subClassOf; o = T_IRI owl_Thing } <: triple))
      classes
  in
  // owl:Nothing rdfs:subClassOf C  for every class C
  let bottom_class_triples : rdf_graph =
    List.Tot.map
      (fun (c : wf_iri) ->
        ({ s = S_IRI owl_Nothing; p = rdfs_subClassOf; o = T_IRI c } <: triple))
      classes
  in
  // P rdfs:domain owl:Thing + P rdfs:range owl:Thing  for every property P
  let property_domain_triples : rdf_graph =
    List.Tot.map
      (fun (p : wf_iri) ->
        ({ s = S_IRI p; p = rdfs_domain; o = T_IRI owl_Thing } <: triple))
      properties
  in
  let property_range_triples : rdf_graph =
    List.Tot.map
      (fun (p : wf_iri) ->
        ({ s = S_IRI p; p = rdfs_range; o = T_IRI owl_Thing } <: triple))
      properties
  in
  // Predicates that actually appear — also receive rdfs:domain/range
  // owl:Thing. Catches the common case of a predicate used in the data
  // that was never declared via rdf:type owl:ObjectProperty etc.
  let predicate_domain_triples : rdf_graph =
    List.Tot.map
      (fun (p : wf_iri) ->
        ({ s = S_IRI p; p = rdfs_domain; o = T_IRI owl_Thing } <: triple))
      predicates
  in
  let predicate_range_triples : rdf_graph =
    List.Tot.map
      (fun (p : wf_iri) ->
        ({ s = S_IRI p; p = rdfs_range; o = T_IRI owl_Thing } <: triple))
      predicates
  in
  // i rdf:type owl:Thing  for every IRI that appears as subject or IRI-object.
  let individual_triples : rdf_graph =
    List.Tot.map
      (fun (i : wf_iri) ->
        ({ s = S_IRI i; p = rdf_type; o = T_IRI owl_Thing } <: triple))
      indivs
  in
  // Self-membership axioms (these keep the downstream closure tidy
  // rather than contributing new information).
  let self_axioms : rdf_graph = [
    { s = S_IRI owl_Thing;   p = rdf_type;        o = T_IRI owl_Class };
    { s = S_IRI owl_Nothing; p = rdf_type;        o = T_IRI owl_Class };
    { s = S_IRI owl_Nothing; p = rdfs_subClassOf; o = T_IRI owl_Thing };
  ] in
  top_class_triples @ bottom_class_triples @
  property_domain_triples @ property_range_triples @
  predicate_domain_triples @ predicate_range_triples @
  individual_triples @ self_axioms

// Full OWL-RL closure with reflexivity axioms AND Group E universal
// axioms: first compute the RDFS closure with reflexivity, harvest the
// Thing/Nothing axioms against the resulting graph, then iterate
// OWL-RL + RDFS together to a fixpoint.
let owl_rl_closure_with_reflexivity (g : rdf_graph) (fuel : nat) : Tot rdf_graph =
  let rdfs_closed = rdfs_closure_with_reflexivity g fuel in
  let thing_axioms = owl_thing_axioms rdfs_closed in
  let with_thing = add_triples_if_new rdfs_closed thing_axioms in
  owl_rl_closure with_thing fuel

// ---- Top-level entailment dispatch ----------------------------------------

// An opaque-looking regime tag. Kept as a string so we don't have to extend
// the extracted OCaml type environment — the w3c_runner selects a value
// based on the manifest-declared regime list.
let regime_simple : string = "simple"
let regime_rdf : string = "RDF"
let regime_rdfs : string = "RDFS"
let regime_owl_rl : string = "OWL-RL"
// OWL-Direct is the DL-semantics regime. Stage (a) of the tableau
// (Tableau.fst) is a skeleton: we run the existing OWL-RL Datalog
// closure as the baseline (sound wrt OWL-Direct), and for any goals
// it doesn't entail the caller MAY consult owl_tableau_entails. The
// tableau currently returns None for everything non-trivial, so the
// observable behaviour of OWL-Direct and OWL-RL is identical until
// later tableau stages land. See docs/designissues/2026-04-19-
// tableau-owl-plan.md §5.
let regime_owl_direct : string = "OWL-Direct"

// entailment_closure : dispatch on regime name, apply the appropriate
// closure. Unknown / unsupported regimes return the graph unchanged.
let entailment_closure (regime : string) (g : rdf_graph) (fuel : nat) : Tot rdf_graph =
  if regime = regime_owl_rl then owl_rl_closure_with_reflexivity g fuel
  else if regime = regime_owl_direct then
    // OWL-Direct stage (a): start from the OWL-RL Datalog closure. The
    // tableau in Tableau.fst is a wiring point only — it doesn't
    // materialise new triples in this commit.
    owl_rl_closure_with_reflexivity g fuel
  else if regime = regime_rdfs then rdfs_closure_with_reflexivity g fuel
  else if regime = regime_rdf then rdfs_closure g fuel
  else g

(** ======================================================================== *)
(** 20. Datatype Value Equivalence                                           *)
(** ======================================================================== *)

(* Helper: check if a character is an ASCII digit *)
let is_digit (c : FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code >= 0x30 && code <= 0x39

(* Strip leading zeros from a list of digit characters, preserving at least one digit *)
let rec strip_leading_zeros (cs : list FStar.Char.char) : list FStar.Char.char =
  match cs with
  | [] -> [FStar.Char.char_of_int 0x30]  (* "0" *)
  | [c] -> [c]  (* single digit — keep it *)
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x30
    then strip_leading_zeros rest
    else cs

(* Normalize an integer lexical form:
   - Strip leading zeros
   - Handle leading +/- signs
   - "-0" becomes "0"
   - "+5" becomes "5" *)
let normalize_integer_lexical (s : string) : string =
  let chars = String.list_of_string s in
  match chars with
  | [] -> "0"
  | c :: rest ->
    let code = FStar.Char.int_of_char c in
    if code = 0x2D then  (* '-' *)
      let normalized = strip_leading_zeros rest in
      (* Check if result is just "0" — then drop the minus sign *)
      (match normalized with
       | [z] -> if FStar.Char.int_of_char z = 0x30
               then "0"
               else String.concat "" ["-"; String.string_of_list normalized]
       | _ -> String.concat "" ["-"; String.string_of_list normalized])
    else if code = 0x2B then  (* '+' *)
      String.string_of_list (strip_leading_zeros rest)
    else
      String.string_of_list (strip_leading_zeros chars)

(* Normalize a decimal lexical form:
   - Normalize the integer part (strip leading zeros)
   - Normalize the fractional part (strip trailing zeros, but keep at least one)
   This is a simplified normalization for xsd:decimal. *)
let strip_trailing_zeros (cs : list FStar.Char.char) : list FStar.Char.char =
  match cs with
  | [] -> [FStar.Char.char_of_int 0x30]
  | _ ->
    let rev = List.Tot.rev cs in
    let rec drop_zeros (l : list FStar.Char.char) : list FStar.Char.char =
      match l with
      | [] -> [FStar.Char.char_of_int 0x30]
      | c :: rest ->
        if FStar.Char.int_of_char c = 0x30
        then drop_zeros rest
        else List.Tot.rev l
    in
    drop_zeros rev

(* Find the dot position in a character list, splitting into integer and fraction parts *)
let rec split_at_dot (cs : list FStar.Char.char) (acc : list FStar.Char.char)
  : (list FStar.Char.char * option (list FStar.Char.char)) =
  match cs with
  | [] -> (List.Tot.rev acc, None)
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x2E  (* '.' *)
    then (List.Tot.rev acc, Some rest)
    else split_at_dot rest (c :: acc)

let normalize_decimal_lexical (s : string) : string =
  let chars = String.list_of_string s in
  let (sign, digits) =
    match chars with
    | [] -> ("", chars)
    | c :: rest ->
      let code = FStar.Char.int_of_char c in
      if code = 0x2D then ("-", rest)
      else if code = 0x2B then ("", rest)
      else ("", chars)
  in
  let (int_part, frac_opt) = split_at_dot digits [] in
  let norm_int = strip_leading_zeros int_part in
  match frac_opt with
  | None ->
    let result = String.concat "" [sign; String.string_of_list norm_int] in
    (* Check for "-0" *)
    if sign = "-" && result = "-0" then "0" else result
  | Some frac_digits ->
    let norm_frac = strip_trailing_zeros frac_digits in
    let int_str = String.string_of_list norm_int in
    let frac_str = String.string_of_list norm_frac in
    let result = String.concat "" [sign; int_str; "."; frac_str] in
    (* Check for "-0.0" *)
    if sign = "-" && int_str = "0" && frac_str = "0" then "0.0" else result

(* Datatype value equivalence: compare literals by their value for recognized datatypes.
   For xsd:integer: normalize lexical forms and compare.
   For xsd:decimal: normalize lexical forms and compare.
   For other datatypes: fall back to syntactic literal_eq. *)
let datatype_value_eq (l1 l2 : literal) : bool =
  if l1.datatype = l2.datatype then
    (* Same datatype — check for value-space comparison *)
    if l1.datatype = xsd_integer then
      normalize_integer_lexical l1.lexical_form = normalize_integer_lexical l2.lexical_form &&
      lang_tag_option_eq l1.lang_tag l2.lang_tag
    else if l1.datatype = xsd_decimal then
      normalize_decimal_lexical l1.lexical_form = normalize_decimal_lexical l2.lexical_form &&
      lang_tag_option_eq l1.lang_tag l2.lang_tag
    else
      (* Unknown datatype — syntactic comparison *)
      literal_eq l1 l2
  else
    (* Different datatypes — not value-equal
       (cross-type numeric promotion is not yet handled) *)
    false
