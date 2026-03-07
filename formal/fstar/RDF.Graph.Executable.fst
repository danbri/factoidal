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

(* Decidable equality for literals — compare all three fields. *)
let literal_eq (l1 l2 : literal) : bool =
  l1.lexical_form = l2.lexical_form &&
  l1.datatype = l2.datatype &&
  l1.lang_tag = l2.lang_tag

(* Decidable equality for RDF terms — concrete implementation. *)
let rdf_term_eq (t1 t2 : rdf_term) : bool =
  match t1, t2 with
  | T_IRI i1, T_IRI i2 -> i1 = i2
  | T_BNode b1, T_BNode b2 -> b1 = b2
  | T_Literal l1, T_Literal l2 -> literal_eq l1 l2
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
  | SV_LangLiteral llex llang, SV_LangLiteral rlex rlang ->
    (match op with
     | Eq -> Some (llex = rlex && llang = rlang)
     | Ne -> Some (llex <> rlex || llang <> rlang)
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

(** ====================================================================== **)
(** 16. N-Triples Parser — Concrete, Extractable                           **)
(** ====================================================================== **)
(* W3C N-Triples grammar (RDF 1.1 N-Triples):
   ntriplesDoc  ::= (triple | comment | blank_line)*
   triple       ::= subject WS+ predicate WS+ object WS* '.' WS*
   subject      ::= IRIREF | BLANK_NODE_LABEL
   predicate    ::= IRIREF
   object       ::= IRIREF | BLANK_NODE_LABEL | literal
   literal      ::= STRING_LITERAL_QUOTE ('^^' IRIREF | LANGTAG)?
   IRIREF       ::= '<' ([^#x00-#x20<>"{}|^`\] | UCHAR)* '>'
   BLANK_NODE_LABEL ::= '_:' (PN_CHARS_U | [0-9]) ((PN_CHARS | '.')* PN_CHARS)?
   STRING_LITERAL_QUOTE ::= '"' ([^#x22#x5C#xA#xD] | ECHAR | UCHAR)* '"'
   ECHAR        ::= '\' [tbnrf"'\]
   LANGTAG      ::= '@' [a-zA-Z]+ ('-' [a-zA-Z0-9]+)*
   WS           ::= #x20 | #x09

   Parser operates on list FStar.Char.char for extractability.
   Returns option (list triple) — None on parse error. *)

type chars = list FStar.Char.char

let char_code (c : FStar.Char.char) : int = FStar.Char.int_of_char c

(* Safe char construction with valid Unicode code point *)
let is_valid_codepoint (n : int) : bool =
  n >= 0 && n < 0xd7ff || n >= 0xe000 && n <= 0x10ffff

let mk_char_safe (n : nat{n < 0xd7ff \/ (n >= 0xe000 /\ n <= 0x10ffff)})
  : FStar.Char.char = FStar.Char.char_of_int n

let mk_char (n : int) : FStar.Char.char =
  if n >= 0 && n < 0xd7ff then mk_char_safe n
  else if n >= 0xe000 && n <= 0x10ffff then mk_char_safe n
  else mk_char_safe 0xFFFD  (* replacement character *)

(* Parse result: remaining chars + parsed value *)
type parse_result (a:Type) = option (a * chars)

(* Skip whitespace (space and tab only in N-Triples) *)
let rec skip_ws (cs : chars) : Tot chars (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> []
  | c :: rest ->
    let code = char_code c in
    if code = 0x20 || code = 0x09 then skip_ws rest
    else cs

(* Skip to end of line (for comments) *)
let rec skip_to_eol (cs : chars) : Tot chars (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> []
  | c :: rest ->
    let code = char_code c in
    if code = 0x0A || code = 0x0D then cs
    else skip_to_eol rest

(* Skip line ending: LF, CR, or CRLF *)
let skip_eol (cs : chars) : chars =
  match cs with
  | [] -> []
  | c1 :: rest ->
    if char_code c1 = 0x0D then
      (match rest with
       | c2 :: rest2 -> if char_code c2 = 0x0A then rest2 else rest
       | [] -> [])
    else if char_code c1 = 0x0A then rest
    else cs

(* Parse N-Triples escape sequence after backslash *)
let parse_escape (cs : chars) : parse_result FStar.Char.char =
  match cs with
  | [] -> None
  | c :: rest ->
    let code = char_code c in
    if code = 0x74 then Some (mk_char 0x09, rest)       (* \t → tab *)
    else if code = 0x6E then Some (mk_char 0x0A, rest)  (* \n → newline *)
    else if code = 0x72 then Some (mk_char 0x0D, rest)  (* \r → CR *)
    else if code = 0x62 then Some (mk_char 0x08, rest)  (* \b → backspace *)
    else if code = 0x66 then Some (mk_char 0x0C, rest)  (* \f → form feed *)
    else if code = 0x22 then Some (mk_char 0x22, rest)  (* \" → quote *)
    else if code = 0x27 then Some (mk_char 0x27, rest)  (* \' → single quote *)
    else if code = 0x5C then Some (mk_char 0x5C, rest)  (* \\ → backslash *)
    else None  (* invalid escape *)

(* Parse hex digit → int value *)
let hex_digit_val (c : FStar.Char.char) : option int =
  let code = char_code c in
  if code >= 0x30 && code <= 0x39 then Some (code - 0x30)       (* 0-9 *)
  else if code >= 0x41 && code <= 0x46 then Some (code - 0x41 + 10)  (* A-F *)
  else if code >= 0x61 && code <= 0x66 then Some (code - 0x61 + 10)  (* a-f *)
  else None

(* Parse N hex digits, accumulating the code point value *)
let rec parse_hex_chars (cs : chars) (n : nat) (acc : nat)
  : Tot (option (nat * chars)) (decreases n) =
  if n = 0 then Some (acc, cs)
  else match cs with
  | [] -> None
  | c :: rest ->
    (match hex_digit_val c with
     | Some v ->
       let acc' = op_Multiply acc 16 + v in
       parse_hex_chars rest (n - 1) acc'
     | None -> None)

(* Parse a Unicode escape (\uXXXX or \UXXXXXXXX) *)
let parse_unicode_escape (cs : chars) : parse_result FStar.Char.char =
  match cs with
  | [] -> None
  | c :: rest ->
    let code = char_code c in
    if code = 0x75 then  (* \u → 4 hex digits *)
      (match parse_hex_chars rest 4 0 with
       | Some (cp, rest2) -> Some (mk_char cp, rest2)
       | None -> None)
    else if code = 0x55 then  (* \U → 8 hex digits *)
      (match parse_hex_chars rest 8 0 with
       | Some (cp, rest2) -> Some (mk_char cp, rest2)
       | None -> None)
    else None

(* Parse string content between quotes, handling escapes.
   fuel parameter ensures termination. *)
let rec parse_string_chars (cs : chars) (acc : chars) (fuel : nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then None
  else match cs with
  | [] -> None  (* unterminated string *)
  | c :: rest ->
    let code = char_code c in
    if code = 0x22 then  (* closing quote *)
      Some (String.string_of_list (List.Tot.rev acc), rest)
    else if code = 0x5C then  (* backslash — escape *)
      (match rest with
       | [] -> None
       | c2 :: _ ->
         let c2code = char_code c2 in
         if c2code = 0x75 || c2code = 0x55 then  (* \u or \U *)
           (match parse_unicode_escape rest with
            | Some (ch, rest2) -> parse_string_chars rest2 (ch :: acc) (fuel - 1)
            | None -> None)
         else
           (match parse_escape rest with
            | Some (ch, rest2) -> parse_string_chars rest2 (ch :: acc) (fuel - 1)
            | None -> None))
    else if code = 0x0A || code = 0x0D then None  (* bare newline in string *)
    else parse_string_chars rest (c :: acc) (fuel - 1)

(* Parse IRIREF: '<' chars '>' with escape handling *)
let rec parse_iri_chars (cs : chars) (acc : chars) (fuel : nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then None
  else match cs with
  | [] -> None
  | c :: rest ->
    let code = char_code c in
    if code = 0x3E then  (* '>' — end of IRI *)
      Some (String.string_of_list (List.Tot.rev acc), rest)
    else if code = 0x5C then  (* backslash — Unicode escape in IRI *)
      (match parse_unicode_escape rest with
       | Some (ch, rest2) -> parse_iri_chars rest2 (ch :: acc) (fuel - 1)
       | None -> None)
    else if code <= 0x20 then None  (* control chars / space not allowed *)
    else parse_iri_chars rest (c :: acc) (fuel - 1)

let parse_iriref (cs : chars) : parse_result string =
  match cs with
  | [] -> None
  | c :: rest ->
    if char_code c = 0x3C then  (* '<' *)
      parse_iri_chars rest [] (List.Tot.length rest)
    else None

(* Parse blank node label: '_:' name *)
let is_pn_chars_u (code : int) : bool =
  (code >= 0x41 && code <= 0x5A) ||  (* A-Z *)
  (code >= 0x61 && code <= 0x7A) ||  (* a-z *)
  code = 0x5F                         (* _ *)

let is_pn_chars (code : int) : bool =
  is_pn_chars_u code ||
  (code >= 0x30 && code <= 0x39) ||  (* 0-9 *)
  code = 0x2D ||                      (* - *)
  code = 0xB7                         (* middle dot *)

(* Strip trailing dots from accumulated blank node label chars.
   W3C grammar: BLANK_NODE_LABEL cannot end with '.'
   Returns (trimmed_acc, dots_to_return_to_input) *)
let rec strip_trailing_dots (acc : chars) (dots : chars)
  : Tot (chars * chars) (decreases (List.Tot.length acc)) =
  match acc with
  | c :: rest ->
    if char_code c = 0x2E then strip_trailing_dots rest (c :: dots)
    else (acc, dots)
  | [] -> (acc, dots)

let rec parse_bnode_label_chars (cs : chars) (acc : chars) (fuel : nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then
    let (trimmed, dots) = strip_trailing_dots acc [] in
    Some (String.string_of_list (List.Tot.rev trimmed), List.Tot.append dots cs)
  else match cs with
  | [] ->
    let (trimmed, _dots) = strip_trailing_dots acc [] in
    Some (String.string_of_list (List.Tot.rev trimmed), [])
  | c :: rest ->
    let code = char_code c in
    if is_pn_chars code || code = 0x2E then
      parse_bnode_label_chars rest (c :: acc) (fuel - 1)
    else
      let (trimmed, dots) = strip_trailing_dots acc [] in
      Some (String.string_of_list (List.Tot.rev trimmed), List.Tot.append dots cs)

let parse_blank_node (cs : chars) : parse_result string =
  match cs with
  | c1 :: c2 :: rest ->
    if char_code c1 = 0x5F && char_code c2 = 0x3A then  (* '_:' *)
      (match rest with
       | c3 :: _ ->
         let code3 = char_code c3 in
         if is_pn_chars_u code3 || (code3 >= 0x30 && code3 <= 0x39) then
           parse_bnode_label_chars rest [] (List.Tot.length rest)
         else None
       | [] -> None)
    else None
  | _ -> None

(* Parse language tag: '@' [a-zA-Z]+ ('-' [a-zA-Z0-9]+)* *)
let is_alpha (code : int) : bool =
  (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A)

let is_alnum (code : int) : bool =
  is_alpha code || (code >= 0x30 && code <= 0x39)

let rec parse_lang_rest (cs : chars) (acc : chars) (fuel : nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then Some (String.string_of_list (List.Tot.rev acc), cs)
  else match cs with
  | [] -> Some (String.string_of_list (List.Tot.rev acc), [])
  | c :: rest ->
    let code = char_code c in
    if is_alnum code || code = 0x2D then  (* alphanumeric or '-' *)
      parse_lang_rest rest (c :: acc) (fuel - 1)
    else
      Some (String.string_of_list (List.Tot.rev acc), cs)

let parse_langtag (cs : chars) : parse_result string =
  match cs with
  | [] -> None
  | c :: rest ->
    if char_code c = 0x40 then  (* '@' *)
      (match rest with
       | c2 :: _ ->
         if is_alpha (char_code c2) then
           parse_lang_rest rest [] (List.Tot.length rest)
         else None
       | [] -> None)
    else None

(* Parse N-Triples subject: IRIREF | BLANK_NODE_LABEL *)
let parse_nt_subject (cs : chars) : parse_result subject =
  match parse_iriref cs with
  | Some (iri_str, rest) ->
    if is_iri iri_str then Some (S_IRI iri_str, rest) else None
  | None ->
    (match parse_blank_node cs with
     | Some (label, rest) -> Some (S_BNode label, rest)
     | None -> None)

(* Parse N-Triples predicate: IRIREF only *)
let parse_nt_predicate (cs : chars) : parse_result wf_iri =
  match parse_iriref cs with
  | Some (iri_str, rest) ->
    if is_iri iri_str then Some (iri_str, rest) else None
  | None -> None

(* Construct a well-formed literal, returning None if invariants fail *)
let mk_wf_literal (lex : string) (dt : wf_iri) (lang : option string) : option wf_literal =
  let l = { lexical_form = lex; datatype = dt; lang_tag = lang } in
  if literal_wf l then Some l else None

(* Parse N-Triples literal: '"' string '"' [ '^^' IRIREF | '@' langtag ] *)
let parse_nt_literal (cs : chars) : parse_result wf_literal =
  match cs with
  | [] -> None
  | c :: rest ->
    if char_code c <> 0x22 then None  (* must start with quote *)
    else
      (match parse_string_chars rest [] (List.Tot.length rest) with
       | None -> None
       | Some (lexical, after_str) ->
         (* Check for datatype or language tag *)
         let mk_result (lit : option wf_literal) (rest : chars) : parse_result wf_literal =
           match lit with Some l -> Some (l, rest) | None -> None
         in
         (match after_str with
          | c1 :: c2 :: rest2 ->
            if char_code c1 = 0x5E && char_code c2 = 0x5E then  (* '^^' *)
              (match parse_iriref rest2 with
               | Some (dt, rest3) ->
                 if is_iri dt then mk_result (mk_wf_literal lexical dt None) rest3
                 else None
               | None -> None)
            else if char_code c1 = 0x40 then  (* '@' *)
              (match parse_langtag after_str with
               | Some (lang, rest3) ->
                 mk_result (mk_wf_literal lexical rdf_lang_string (Some lang)) rest3
               | None -> None)
            else  (* plain string literal *)
              mk_result (mk_wf_literal lexical xsd_string None) after_str
          | [c1] ->
            if char_code c1 = 0x40 then
              (match parse_langtag after_str with
               | Some (lang, rest3) ->
                 mk_result (mk_wf_literal lexical rdf_lang_string (Some lang)) rest3
               | None -> None)
            else
              mk_result (mk_wf_literal lexical xsd_string None) after_str
          | [] ->
            mk_result (mk_wf_literal lexical xsd_string None) []))

(* Parse N-Triples object: IRIREF | BLANK_NODE_LABEL | literal *)
let parse_nt_object (cs : chars) : parse_result rdf_term =
  match parse_iriref cs with
  | Some (iri_str, rest) ->
    if is_iri iri_str then Some (T_IRI iri_str, rest) else None
  | None ->
    (match parse_blank_node cs with
     | Some (label, rest) -> Some (T_BNode label, rest)
     | None ->
       (match parse_nt_literal cs with
        | Some (lit, rest) -> Some (T_Literal lit, rest)
        | None -> None))

(* Require at least one whitespace character *)
let require_ws (cs : chars) : option chars =
  match cs with
  | [] -> None
  | c :: _ ->
    let code = char_code c in
    if code = 0x20 || code = 0x09 then Some (skip_ws cs)
    else None

(* Parse a single N-Triples triple: subject WS* predicate WS* object WS* '.'
   N-Triples tokens are self-delimiting (<...>, _:..., "...") so whitespace
   between them is consumed but not strictly required. *)
let parse_nt_triple (cs : chars) : parse_result triple =
  match parse_nt_subject cs with
  | None -> None
  | Some (subj, after_s) ->
    let after_ws1 = skip_ws after_s in
    (match parse_nt_predicate after_ws1 with
     | None -> None
     | Some (pred, after_p) ->
       let after_ws2 = skip_ws after_p in
       (match parse_nt_object after_ws2 with
        | None -> None
        | Some (obj, after_o) ->
          let after_ws3 = skip_ws after_o in
          (match after_ws3 with
           | c :: rest ->
             if char_code c = 0x2E then  (* '.' *)
               Some ({ s = subj; p = pred; o = obj }, skip_ws rest)
             else None
           | [] -> None)))

(* Parse an entire N-Triples document into a list of triples.
   Handles blank lines and # comments.
   fuel parameter ensures termination. *)
let rec parse_nt_lines (cs : chars) (acc : list triple) (fuel : nat)
  : Tot (option (list triple)) (decreases fuel) =
  if fuel = 0 then Some (List.Tot.rev acc)
  else
    let cs = skip_ws cs in
    match cs with
    | [] -> Some (List.Tot.rev acc)
    | c :: rest ->
      let code = char_code c in
      if code = 0x0A || code = 0x0D then  (* blank line *)
        parse_nt_lines (skip_eol cs) acc (fuel - 1)
      else if code = 0x23 then  (* '#' comment *)
        parse_nt_lines (skip_eol (skip_to_eol rest)) acc (fuel - 1)
      else
        (match parse_nt_triple cs with
         | Some (t, rest2) ->
           parse_nt_lines (skip_eol rest2) (t :: acc) (fuel - 1)
         | None -> None)

(* Top-level N-Triples parser: string → option rdf_graph *)
let parse_ntriples (s : string) : option rdf_graph =
  let cs = String.list_of_string s in
  parse_nt_lines cs [] (List.Tot.length cs)

(* Build graph from parsed triples (with deduplication) *)
let parse_ntriples_graph (s : string) : option rdf_graph =
  match parse_ntriples s with
  | Some triples ->
    Some (List.Tot.fold_left (fun g t -> graph_add t g) empty_graph triples)
  | None -> None
