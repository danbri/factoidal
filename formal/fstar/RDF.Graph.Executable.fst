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

(* Well-known IRI constants. We assert they satisfy is_iri via axioms. *)
assume val rdf_lang_string : wf_iri
assume val xsd_string : wf_iri
assume val xsd_integer : wf_iri
assume val xsd_decimal : wf_iri
assume val xsd_double : wf_iri
assume val xsd_boolean : wf_iri

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
assume val is_nt_escaped : string -> nat -> bool

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
assume val string_lt : string -> string -> bool

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
assume val string_substring : string -> nat -> nat -> string

let sparql_substr (s : string) (start : nat) (len : option nat) : string =
  let start_idx = if start > 0 then start - 1 else 0 in
  let remaining = if String.length s > start_idx then String.length s - start_idx else 0 in
  match len with
  | Some n -> string_substring s start_idx n
  | None   -> string_substring s start_idx remaining

// UCASE: convert all characters to upper case
assume val string_to_upper : string -> string

let sparql_ucase (s : string) : string =
  string_to_upper s

// LCASE: convert all characters to lower case
assume val string_to_lower : string -> string

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
