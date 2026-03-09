module RDF.Graph.Executable

open FStar.String
open FStar.List.Tot

(** 1. Concrete Types for Execution **)
// We choose string for blank nodes so they can be extracted as simple values
type bnode_id = string
type iri = string

(** 2. Refined IRIs **)
(* An IRI must be non-empty and contain a colon.
   We implement the colon check via list_of_string to avoid
   termination issues with string index traversal. *)
let rec list_has_colon (cs : list FStar.Char.char) : bool =
  match cs with
  | [] -> false
  | c :: rest -> FStar.Char.int_of_char c = 0x3A || list_has_colon rest

let string_contains_colon (s : string) : bool =
  list_has_colon (String.list_of_string s)

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
type named_graph = {
  ng_name : iri;
  ng_graph : rdf_graph;
}

type rdf_dataset = {
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

// Computes the set of all blank nodes in the graph
let rec graph_bnodes (g:rdf_graph) : list bnode_id =
  match g with
  | [] -> []
  | hd :: tl ->
      let nodes = match hd.s with | S_BNode id -> [id] | _ -> [] in
      let obj_nodes = match hd.o with | T_BNode id -> [id] | _ -> [] in
      nodes @ obj_nodes @ (graph_bnodes tl)

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
let rec find_objects (g : rdf_graph) (subj : subject) (pred : wf_iri) : list rdf_term =
  match g with
  | [] -> []
  | hd :: tl ->
    let rest = find_objects tl subj pred in
    if subject_eq hd.s subj && hd.p = pred
    then hd.o :: rest
    else rest

(* Find all subjects where (?s p o) in graph *)
let rec find_subjects (g : rdf_graph) (pred : wf_iri) (obj : rdf_term) : list subject =
  match g with
  | [] -> []
  | hd :: tl ->
    let rest = find_subjects tl pred obj in
    if hd.p = pred && rdf_term_eq hd.o obj
    then hd.s :: rest
    else rest

(* Check if a triple exists in the graph *)
let has_triple (g : rdf_graph) (t : triple) : bool =
  mem_triple t g

(* Add a triple only if not already present *)
let add_triple_if_new (g : rdf_graph) (t : triple) : rdf_graph =
  graph_add t g

(* Add multiple triples, deduplicating *)
let rec add_triples_if_new (g : rdf_graph) (ts : list triple) : rdf_graph =
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
  g5

(* Iterate closure until fixed point or max iterations.
   Uses nat fuel parameter for termination. *)
let rec rdfs_closure (g : rdf_graph) (fuel : nat) : rdf_graph =
  match fuel with
  | 0 -> g
  | _ ->
    let g' = rdfs_closure_step g in
    if graph_len g' = graph_len g
    then g  (* fixed point reached — no new triples added *)
    else rdfs_closure g' (fuel - 1)

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

(* Convert an integer lexical form to a canonical decimal form.
   E.g., "10" -> "10", "010" -> "10", "-5" -> "-5".
   The canonical decimal form of an integer is just the normalized integer. *)
let integer_to_decimal_canonical (s : string) : string =
  normalize_integer_lexical s

(* Normalize a numeric literal to a canonical decimal string for cross-type comparison.
   For xsd:integer: normalize and return as-is (integers are a subset of decimals).
   For xsd:decimal: normalize the decimal form and strip trailing ".0" for whole numbers,
   or normalize both to a common representation.
   We compare by normalizing both to decimal canonical form. *)
let numeric_to_canonical_decimal (lexical : string) (datatype : wf_iri) : string =
  if datatype = xsd_integer then
    (* Integer "10" in decimal value space is just "10" *)
    normalize_integer_lexical lexical
  else if datatype = xsd_decimal then
    (* Decimal "10.0" normalized: strip trailing zeros after dot *)
    let norm = normalize_decimal_lexical lexical in
    (* If the fractional part is just "0", strip it for comparison with integers.
       E.g., "10.0" -> "10" so it matches integer "10". *)
    let chars = String.list_of_string norm in
    let (int_part, frac_opt) = split_at_dot chars [] in
    match frac_opt with
    | None -> norm  (* no dot — already in integer form *)
    | Some frac_digits ->
      let stripped = strip_trailing_zeros frac_digits in
      (* If all fractional digits are zero, return just the integer part *)
      (match stripped with
       | [c] -> if FStar.Char.int_of_char c = 0x30
               then String.string_of_list int_part
               else norm
       | _ -> norm)
  else
    lexical  (* unknown type — return as-is *)

(* Datatype value equivalence: compare literals by their value for recognized datatypes.
   For xsd:integer: normalize lexical forms and compare.
   For xsd:decimal: normalize lexical forms and compare.
   For xsd:integer vs xsd:decimal: cross-type numeric comparison.
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
  else if (l1.datatype = xsd_integer && l2.datatype = xsd_decimal) ||
          (l1.datatype = xsd_decimal && l2.datatype = xsd_integer) then
    (* Cross-type numeric comparison: integer and decimal are in the same value space *)
    numeric_to_canonical_decimal l1.lexical_form l1.datatype =
      numeric_to_canonical_decimal l2.lexical_form l2.datatype &&
    lang_tag_option_eq l1.lang_tag l2.lang_tag
  else
    (* Different non-numeric datatypes — not value-equal *)
    false
