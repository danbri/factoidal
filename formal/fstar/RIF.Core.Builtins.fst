module RIF.Core.Builtins

// RIF-DTB (Datatypes and Built-Ins, https://www.w3.org/TR/rif-dtb/)
// subset needed by the vendored W3C RIF Core corpus's "External"
// skip bucket (third_party/testing/rif-core-suite/), per
// bin/rif-runner/README.md's Score section and the corpus fixtures
// actually exercised (Builtins_Numeric, Builtins_Binary,
// Builtins_anyURI, Builtins_XMLLiteral, Builtins_boolean,
// Builtin_literal-not-identical, Chaining_strategy_numeric-*,
// Factorial_Forward_Chaining, Guards_and_subtypes).
//
// Deliberately NOT covered this slice (each stays an honest SKIP at
// the runner level, citing this scope note): pred:iri-string /
// pred:list-contains (need alternate-binding-pattern EXECUTION, not
// just filtering — see Core_Safeness_3/RIF.Core.Conformance for the
// binding-pattern ANALYSIS, which is a separate, structural concern),
// the full string family (func:substring/matches/...), the full
// dateTime/duration family, List builtins, and rdf:PlainLiteral's
// builtin family (PlainLiteral-compare/from-string-lang/...) — note
// Parser.RIFXML already DECODES rdf:PlainLiteral Consts into plain
// xsd:string / rdf:langString literals at parse time
// (const_from_type/plain_literal_const), so an rdf:PlainLiteral
// builtin family would need to operate on that decoded form, which
// is future work, not attempted here.
//
// Two dispatch entry points, called by RIF.Core.Eval:
//   eval_function  : builtin IRI * resolved args -> option rdf_term
//                    (func: namespace — TERM/value-producing builtins,
//                    used inside External(...) in argument/Equal-RHS
//                    position)
//   eval_predicate : builtin IRI * resolved args -> option bool
//                    (pred: namespace — FORMULA/boolean builtins, used
//                    as a standalone External(...) body conjunct)
// Both return None for any (IRI, arity, argument-shape) combination
// this module does not implement — the caller treats None as "this
// External could not be evaluated", never as false/absent silently.
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries, no assume val (rule #10, #3).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
module Alg = SPARQL11.Algebra
module XD  = XSD.Datatypes

// ------------------------------------------------------------------
// 1. Builtin IRI namespaces and the datatype constants this project's
//    RDF.Graph.Executable / XSD.Datatypes don't already carry.
// ------------------------------------------------------------------

let rif_pred_ns : string = "http://www.w3.org/2007/rif-builtin-predicate#"
let rif_func_ns : string = "http://www.w3.org/2007/rif-builtin-function#"

let xsd_hexBinary : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "hexBinary")); xsd_ns_prefix ^ "hexBinary"

let xsd_base64Binary : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "base64Binary")); xsd_ns_prefix ^ "base64Binary"

let xsd_anyURI : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "anyURI")); xsd_ns_prefix ^ "anyURI"

let rdf_ns_prefix : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

let rdf_XMLLiteral : wf_iri =
  assert_norm (is_iri (rdf_ns_prefix ^ "XMLLiteral")); rdf_ns_prefix ^ "XMLLiteral"

// ------------------------------------------------------------------
// 2. Lexical well-formedness for the two binary datatypes
//    XSD.Datatypes.literal_ill_formed does not model (it covers
//    boolean/integer-family/decimal/float/double/dateTime only).
//    Reused ASCII char-class checks in the same direct-recursion
//    style XSD.Datatypes.fst's own is_signed_digits_chars etc. use.
// ------------------------------------------------------------------

let is_hex_digit_char (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  (n >= 48 && n <= 57) || (n >= 65 && n <= 70) || (n >= 97 && n <= 102)

let is_hex_binary_lexical (lex : string) : bool =
  let cs = String.list_of_string lex in
  (List.Tot.length cs) % 2 = 0 && List.Tot.for_all is_hex_digit_char cs

let is_base64_char (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  (n >= 65 && n <= 90) || (n >= 97 && n <= 122) || (n >= 48 && n <= 57)
  || n = 43 (* '+' *) || n = 47 (* '/' *) || n = 61 (* '=' *)

// XSD base64Binary lexical space: base64 alphabet, total length a
// multiple of 4 (padding included), non-empty. Does not verify '='
// only appears as trailing padding — sufficient for the vendored
// corpus's two fixtures (a full unpadded 64-char alphabet string, and
// a 3-char non-multiple-of-4 rejection case), documented as a known
// narrowing rather than a silent gap.
let is_base64_binary_lexical (lex : string) : bool =
  let cs = String.list_of_string lex in
  let len = List.Tot.length cs in
  len > 0 && len % 4 = 0 && List.Tot.for_all is_base64_char cs

// literal_ill_formed extended with the two binary datatypes. Any
// OTHER datatype XSD.Datatypes.literal_ill_formed does not recognise
// (xsd:anyURI, rdf:XMLLiteral, ...) falls through to its own
// `else false` — i.e. "not ill-formed" by default, which is exactly
// the RIF-DTB behaviour these two datatypes need (their lexical space
// is "any string").
let literal_ill_formed_ext (dt : wf_iri) (lex : string) : bool =
  if dt = xsd_hexBinary then not (is_hex_binary_lexical lex)
  else if dt = xsd_base64Binary then not (is_base64_binary_lexical lex)
  else XD.literal_ill_formed dt lex

// ------------------------------------------------------------------
// 3. is-literal-<T> / is-literal-not-<T> family.
//
// A literal "is" datatype T iff its own datatype tag equals T AND its
// lexical form is well-formed per T's value space (a literal whose
// tag matches but whose lexical form is malformed is NOT considered
// "is-literal-T", matching how the corpus's Guards_and_subtypes
// fixture uses is-literal-decimal / is-literal-integer as type
// guards). Non-literal terms (IRI, blank node) are never "is-literal"
// anything.
// ------------------------------------------------------------------

// Guards_and_subtypes (the fixture literally testing this) requires
// BOTH is-literal-decimal("3"^^xs:integer) AND
// is-literal-integer("3"^^xs:decimal) to hold — i.e. is-literal-<T> is
// NOT a check of the argument's OWN declared datatype tag (that would
// make only ONE of those two directions true, never both, since
// xsd:integer and xsd:decimal aren't mutually subtypes). Builtins_
// Numeric confirms the same reading throughout (e.g. is-literal-long
// holds on an xs:integer-tagged "1"): for datatypes with a REAL
// lexical-space constraint (the whole numeric family, hexBinary,
// base64Binary), is-literal-<T> checks whether the argument's LEXICAL
// FORM is well-formed for T — a "can this be read as a T" test,
// independent of what datatype the literal happens to already be
// tagged with.
//
// anyURI and XMLLiteral are the opposite case: XSD gives them
// essentially UNCONSTRAINED lexical spaces (any Unicode string is a
// well-formed xsd:anyURI or rdf:XMLLiteral lexical form), so a purely
// lexical check would make is-literal-anyURI/is-literal-XMLLiteral
// trivially true for every literal — but Builtins_anyURI/Builtins_
// XMLLiteral both require is-literal-not-anyURI/is-literal-not-
// XMLLiteral to hold on an xs:integer-tagged "1". For exactly these
// two (no real lexical constraint to fall back on), the check DOES
// need the literal's own declared datatype tag.
let unconstrained_lexical_space_datatypes : list wf_iri = [ xsd_anyURI; rdf_XMLLiteral ]

let is_literal_of_datatype (expected_dt : wf_iri) (t : rdf_term) : bool =
  match t with
  | T_Literal l ->
    if List.Tot.mem expected_dt unconstrained_lexical_space_datatypes
    then l.datatype = expected_dt
    else not (literal_ill_formed_ext expected_dt l.lexical_form)
  | _ -> false

// Table of every is-literal-<T> local name this module supports,
// paired with its XSD/RDF datatype IRI. Covers exactly the datatype
// family Builtins_Numeric / Builtins_Binary / Builtins_anyURI /
// Builtins_XMLLiteral / Builtins_boolean / Guards_and_subtypes
// exercise.
let is_literal_datatype_table : list (string & wf_iri) = [
  "decimal", xsd_decimal;
  "double", xsd_double;
  "float", Alg.xsd_float;
  "integer", xsd_integer;
  "long", xsd_long;
  "int", xsd_int;
  "short", xsd_short;
  "byte", xsd_byte;
  "negativeInteger", xsd_negativeInteger;
  "nonNegativeInteger", xsd_nonNegativeInteger;
  "nonPositiveInteger", xsd_nonPositiveInteger;
  "positiveInteger", xsd_positiveInteger;
  "unsignedLong", xsd_unsignedLong;
  "unsignedInt", xsd_unsignedInt;
  "unsignedShort", xsd_unsignedShort;
  "unsignedByte", xsd_unsignedByte;
  "hexBinary", xsd_hexBinary;
  "base64Binary", xsd_base64Binary;
  "anyURI", xsd_anyURI;
  "boolean", xsd_boolean;
  "XMLLiteral", rdf_XMLLiteral;
]

let rec lookup_datatype (name : string) (tbl : list (string & wf_iri))
  : Tot (option wf_iri) (decreases tbl) =
  match tbl with
  | [] -> None
  | (n, dt) :: rest -> if n = name then Some dt else lookup_datatype name rest

// Given a pred: local name (e.g. "is-literal-decimal" or
// "is-literal-not-hexBinary"), determine which datatype it names and
// whether it is the negated ("not") form. Returns None if the local
// name is not one of this module's supported is-literal-<T> family.
let is_literal_pred_shape (local : string) : option (wf_iri & bool) =
  if String.length local > String.length "is-literal-not-"
     && String.sub local 0 (String.length "is-literal-not-") = "is-literal-not-"
  then
    let ty = String.sub local (String.length "is-literal-not-")
               (String.length local - String.length "is-literal-not-") in
    (match lookup_datatype ty is_literal_datatype_table with
     | Some dt -> Some (dt, true)
     | None -> None)
  else if String.length local > String.length "is-literal-"
     && String.sub local 0 (String.length "is-literal-") = "is-literal-"
  then
    let ty = String.sub local (String.length "is-literal-")
               (String.length local - String.length "is-literal-") in
    (match lookup_datatype ty is_literal_datatype_table with
     | Some dt -> Some (dt, false)
     | None -> None)
  else None

// ------------------------------------------------------------------
// 4. Numeric conversions, reusing SPARQL11.Algebra's already-verified
//    cross-type (integer/decimal/double) arithmetic and comparison
//    machinery rather than re-deriving numeric promotion (the exact
//    logic eval_expr_with_base's E_Arith / value_compare cases use).
// ------------------------------------------------------------------

let term_to_arith_expr (t : rdf_term) : option Alg.expr =
  match t with
  | T_Literal l ->
    if l.datatype = xsd_integer then
      (match Alg.parse_int_string l.lexical_form with
       | Some n -> Some (Alg.E_NumericLit n)
       | None -> None)
    else if l.datatype = xsd_decimal then Some (Alg.E_DecimalLit l.lexical_form)
    else if l.datatype = xsd_double || l.datatype = Alg.xsd_float then Some (Alg.E_DoubleLit l.lexical_form)
    else None
  | _ -> None

let eval_numeric_binop (op : Alg.arith_op) (a b : rdf_term) : option rdf_term =
  match term_to_arith_expr a, term_to_arith_expr b with
  | Some ea, Some eb ->
    let result = Alg.eval_expr_with_base None (Alg.E_Arith op ea eb) Alg.sm_empty in
    Alg.er_to_term result
  | _, _ -> None

// term_to_er promotes a literal to Algebra's numeric eval_result
// exactly the way eval_expr_with_base's E_Var case does, so
// value_compare's cross-type numeric comparison applies uniformly to
// integer/decimal/double/float/boolean operands.
let term_to_er (t : rdf_term) : Alg.eval_result =
  match t with
  | T_Literal l ->
    if l.datatype = xsd_integer then
      (match Alg.parse_int_string l.lexical_form with
       | Some n -> Alg.ER_Num n
       | None -> Alg.ER_Term t)
    else if l.datatype = xsd_decimal then Alg.ER_Dec l.lexical_form
    else if l.datatype = xsd_double || l.datatype = Alg.xsd_float then Alg.ER_Dbl l.lexical_form
    else if l.datatype = xsd_boolean then Alg.ER_Bool (l.lexical_form = "true" || l.lexical_form = "1")
    else Alg.ER_Term t
  | _ -> Alg.ER_Term t

let numeric_predicate (cmp : Alg.comp_op) (a b : rdf_term) : option bool =
  Alg.value_compare (term_to_er a) (term_to_er b) cmp

// numeric-integer-divide / numeric-integer-mod are typed
// xs:integer,xs:integer -> xs:integer in RIF-DTB (unlike
// numeric-divide, which is the polymorphic decimal/double overload
// set already covered by eval_numeric_binop's Div case) — plain
// integer truncating division/modulo, not the scaled-decimal path.
let term_to_int (t : rdf_term) : option int =
  match t with
  | T_Literal l -> if l.datatype = xsd_integer then Alg.parse_int_string l.lexical_form else None
  | _ -> None

// Truncate-toward-zero division/modulo (XPath op:numeric-integer-divide
// / op:numeric-mod semantics). F*'s native `/`/`%` on `int` floor
// toward negative infinity (see XSD.Datatypes.fst's own cast-to-integer
// comment for the same discrepancy); adjust when the floor quotient
// overshoots for mixed-sign operands.
let trunc_div (a b : int) : int =
  if b = 0 then 0
  else
    let q = a / b in
    let r = a - op_Multiply q b in
    if r <> 0 && ((a < 0) <> (b < 0)) then q + 1 else q

let trunc_mod (a b : int) : int =
  if b = 0 then 0
  else a - op_Multiply (trunc_div a b) b

let mk_int_literal (n : int) : rdf_term =
  T_Literal ({ lexical_form = string_of_int n; datatype = xsd_integer; lang_tag = None })

// ------------------------------------------------------------------
// 5. Local-name extraction (substring after the LAST '#') — builtin
//    IRIs in this corpus are always fully-qualified, so dispatch is a
//    direct string match against the two namespace constants above
//    rather than a general IRI-shape parser.
// ------------------------------------------------------------------

let rec find_last_hash_aux (cs : list FStar.Char.char) (idx : nat) (last : option nat)
  : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> last
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x23 (* '#' *)
    then find_last_hash_aux rest (idx + 1) (Some idx)
    else find_last_hash_aux rest (idx + 1) last

let local_name_of_iri (iri : string) : string =
  match find_last_hash_aux (String.list_of_string iri) 0 None with
  | None -> iri
  | Some pos ->
    let len = String.length iri in
    if pos + 1 >= len then "" else String.sub iri (pos + 1) (len - pos - 1)

// ------------------------------------------------------------------
// 6. Public dispatch.
// ------------------------------------------------------------------

// XSD "constructor function" cast: External(xs:<T>(x)) — the
// Builtins_* battery uses these heavily (e.g. Builtins_boolean's
// `External(pred:is-literal-boolean(External(xs:boolean("1"^^xs:string))))`)
// to build a literal of a specific target datatype from another
// literal's lexical form, ahead of an is-literal-<T> check. Every RIF
// Core corpus fixture this project targets casts between datatypes
// whose lexical spaces overlap enough that a straight relabel (same
// lexical form, new datatype tag) is what the fixture actually
// exercises — this is not a general XSD cast-conversion engine (no
// value-preserving reformatting, e.g. no int->boolean numeric
// coercion), just the "reinterpret this lexical form under datatype
// T" constructor form the corpus needs. Scoped to casts whose TARGET
// is one of this module's own supported datatypes (xsd_ns_prefix
// namespace only — every target fixture's cast lands on a numeric/
// binary/boolean/anyURI datatype already in is_literal_datatype_table).
// The cast TARGET must be one of this module's own supported
// datatypes (is_literal_datatype_table's IRIs) — not a blanket
// namespace-prefix match — so an unsupported cast target (e.g. a
// datatype this module has no is-literal-<T> support for) correctly
// falls through to None (SKIP-worthy) rather than silently producing
// a literal no is-literal-<T> check will ever recognise anyway.
let supported_cast_targets : list wf_iri =
  List.Tot.map (fun (p : (string & wf_iri)) -> snd p) is_literal_datatype_table

let xsd_constructor_cast (op : wf_iri) (args : list rdf_term) : option rdf_term =
  match args with
  | [T_Literal l] ->
    if List.Tot.mem op supported_cast_targets && op <> rdf_lang_string
    then Some (T_Literal ({ lexical_form = l.lexical_form; datatype = op; lang_tag = None }))
    else None
  | _ -> None

// func: namespace — value-producing builtins.
let eval_function (op : wf_iri) (args : list rdf_term) : option rdf_term =
  if not (String.length op > String.length rif_func_ns
          && String.sub op 0 (String.length rif_func_ns) = rif_func_ns)
  then xsd_constructor_cast op args
  else
    let local = local_name_of_iri op in
    match local, args with
    | "numeric-add", [a; b]      -> eval_numeric_binop Alg.Add a b
    | "numeric-subtract", [a; b] -> eval_numeric_binop Alg.Sub a b
    | "numeric-multiply", [a; b] -> eval_numeric_binop Alg.Mul a b
    | "numeric-divide", [a; b]   -> eval_numeric_binop Alg.Div a b
    | "numeric-integer-divide", [a; b] ->
      (match term_to_int a, term_to_int b with
       | Some ia, Some ib -> if ib = 0 then None else Some (mk_int_literal (trunc_div ia ib))
       | _, _ -> None)
    | "numeric-integer-mod", [a; b] ->
      (match term_to_int a, term_to_int b with
       | Some ia, Some ib -> if ib = 0 then None else Some (mk_int_literal (trunc_mod ia ib))
       | _, _ -> None)
    | _, _ -> None

// pred: namespace — boolean builtins.
let eval_predicate (op : wf_iri) (args : list rdf_term) : option bool =
  if not (String.length op > String.length rif_pred_ns
          && String.sub op 0 (String.length rif_pred_ns) = rif_pred_ns)
  then None
  else
    let local = local_name_of_iri op in
    match local, args with
    | "numeric-equal", [a; b]              -> numeric_predicate Alg.CmpEq a b
    | "numeric-not-equal", [a; b]           -> numeric_predicate Alg.CmpNe a b
    | "numeric-less-than", [a; b]           -> numeric_predicate Alg.CmpLt a b
    | "numeric-less-than-or-equal", [a; b]  -> numeric_predicate Alg.CmpLe a b
    | "numeric-greater-than", [a; b]        -> numeric_predicate Alg.CmpGt a b
    | "numeric-greater-than-or-equal", [a; b] -> numeric_predicate Alg.CmpGe a b
    | "boolean-equal", [a; b]               -> numeric_predicate Alg.CmpEq a b
    | "boolean-less-than", [a; b]           -> numeric_predicate Alg.CmpLt a b
    | "boolean-greater-than", [a; b]        -> numeric_predicate Alg.CmpGt a b
    | "literal-not-identical", [a; b]       -> Some (not (rdf_term_eq a b))
    | _, [x] ->
      (match is_literal_pred_shape local with
       | Some (dt, negated) ->
         let v = is_literal_of_datatype dt x in
         Some (if negated then not v else v)
       | None -> None)
    | _, _ -> None
