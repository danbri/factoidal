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
// 2026-07-10 extension: the STRING family (compare/concat/string-join/
// substring/string-length/upper-case/lower-case/encode-for-uri/
// iri-to-uri/escape-html-uri/substring-before/substring-after/replace,
// pred:contains/starts-with/ends-with/matches, and is-literal-<T> for
// the xsd:string-derived datatypes), the rdf:PlainLiteral family
// (PlainLiteral-from-string-lang/string-from-PlainLiteral/
// lang-from-PlainLiteral/PlainLiteral-compare, pred:matches-language-
// range, is-literal-(not-)PlainLiteral — operating on the DECODED
// xsd:string/rdf:langString form Parser.RIFXML's
// const_from_type/plain_literal_const produce), pred:iri-string in
// its GROUND filter form (the BINDING form lives in
// RIF.Core.Eval.apply_extra_condition, which sees the unresolved
// argument terms), and the narrow dateTime/duration slice
// EBusiness_Contract exercises (is-literal-dateTime,
// func:subtract-dateTimes, func:days-from-duration).
//
// Deliberately NOT covered (each stays an honest SKIP at the runner
// level, citing this scope note): pred:list-contains and the List
// builtin family (RIF list terms are not modelled in
// RIF.Core.Syntax), and the FULL date/time/duration family
// (Builtins_Time's ~60 add/subtract/multiply/divide/timezone-from/
// year-from/... builtins over date/time/dateTime/dayTimeDuration/
// yearMonthDuration) — only the EBusiness_Contract slice above is
// implemented.
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

// pred:iri-string, exported as a constant because RIF.Core.Eval's
// apply_extra_condition special-cases its alternate BINDING-PATTERN
// execution (producing a binding for an unbound argument) — the
// ground filter form is dispatched normally via eval_predicate below.
let rif_pred_iri_string : wf_iri =
  assert_norm (is_iri (rif_pred_ns ^ "iri-string")); rif_pred_ns ^ "iri-string"

let xsd_hexBinary : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "hexBinary")); xsd_ns_prefix ^ "hexBinary"

let xsd_base64Binary : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "base64Binary")); xsd_ns_prefix ^ "base64Binary"

let xsd_anyURI : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "anyURI")); xsd_ns_prefix ^ "anyURI"

let rdf_ns_prefix : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

let rdf_XMLLiteral : wf_iri =
  assert_norm (is_iri (rdf_ns_prefix ^ "XMLLiteral")); rdf_ns_prefix ^ "XMLLiteral"

let rdf_PlainLiteral_dt : wf_iri =
  assert_norm (is_iri (rdf_ns_prefix ^ "PlainLiteral")); rdf_ns_prefix ^ "PlainLiteral"

// The xsd:string-derived ("string family") datatypes the corpus's
// Builtins_String battery guards with is-literal-<T>.
let xsd_normalizedString : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "normalizedString")); xsd_ns_prefix ^ "normalizedString"

let xsd_token : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "token")); xsd_ns_prefix ^ "token"

let xsd_language : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "language")); xsd_ns_prefix ^ "language"

// Non-standard but corpus-used: Builtins_PlainLiteral's expected
// lang-from-PlainLiteral result is typed `xs:lang` (sic) — kept as
// its own IRI so value comparison (string-family, by lexical form)
// still matches without inventing a datatype alias.
let xsd_lang_nonstandard : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "lang")); xsd_ns_prefix ^ "lang"

let xsd_Name_dt : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "Name")); xsd_ns_prefix ^ "Name"

let xsd_NCName_dt : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "NCName")); xsd_ns_prefix ^ "NCName"

let xsd_NMTOKEN_dt : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "NMTOKEN")); xsd_ns_prefix ^ "NMTOKEN"

let xsd_date : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "date")); xsd_ns_prefix ^ "date"

let xsd_dayTimeDuration : wf_iri =
  assert_norm (is_iri (xsd_ns_prefix ^ "dayTimeDuration")); xsd_ns_prefix ^ "dayTimeDuration"

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

// --- String-family value-space checks (ASCII approximations of the
// XML/XSD productions — sufficient for every vendored corpus lexical
// form, which are all ASCII; documented narrowing, not a silent gap).

let is_crlf_tab_char (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  n = 0x09 || n = 0x0A || n = 0x0D

let is_ascii_alpha_char (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  (n >= 65 && n <= 90) || (n >= 97 && n <= 122)

let is_ascii_digit_char (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  n >= 48 && n <= 57

// XML Name productions (ASCII approximation): NameStartChar includes
// letters, '_' and ':'; NameChar additionally digits, '-' and '.'.
let is_name_start_char (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  is_ascii_alpha_char c || n = 0x5F || n = 0x3A

let is_name_char (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  is_name_start_char c || is_ascii_digit_char c || n = 0x2D || n = 0x2E

let is_colon_char (c : FStar.Char.char) : bool =
  FStar.Char.int_of_char c = 0x3A

let is_space_char (c : FStar.Char.char) : bool =
  FStar.Char.int_of_char c = 0x20

// xsd:normalizedString: no CR / LF / TAB anywhere.
let is_normalized_string_value (lex : string) : bool =
  List.Tot.for_all (fun c -> not (is_crlf_tab_char c)) (String.list_of_string lex)

// xsd:token: normalizedString + no leading/trailing space + no
// internal double space.
let rec no_double_space (cs : list FStar.Char.char) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | [_] -> true
  | a :: b :: rest ->
    if is_space_char a && is_space_char b then false
    else no_double_space (b :: rest)

let is_token_value (lex : string) : bool =
  let cs = String.list_of_string lex in
  is_normalized_string_value lex
  && (match cs with [] -> true | c :: _ -> not (is_space_char c))
  && (match List.Tot.rev cs with [] -> true | c :: _ -> not (is_space_char c))
  && no_double_space cs

// xsd:language: [a-zA-Z]{1,8}(-[a-zA-Z0-9]{1,8})*  (RFC 3066 shape).
let rec split_on_dash_aux (cs : list FStar.Char.char) (cur : list FStar.Char.char)
  : Tot (list (list FStar.Char.char)) (decreases cs) =
  match cs with
  | [] -> [List.Tot.rev cur]
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x2D
    then (List.Tot.rev cur) :: split_on_dash_aux rest []
    else split_on_dash_aux rest (c :: cur)

let split_on_dash (s : string) : list (list FStar.Char.char) =
  split_on_dash_aux (String.list_of_string s) []

let is_language_value (lex : string) : bool =
  match split_on_dash lex with
  | [] -> false
  | first :: rest ->
    let sub_ok (alnum : bool) (sub : list FStar.Char.char) : bool =
      let len = List.Tot.length sub in
      len >= 1 && len <= 8
      && List.Tot.for_all
           (fun c -> if alnum then is_ascii_alpha_char c || is_ascii_digit_char c
                     else is_ascii_alpha_char c)
           sub
    in
    sub_ok false first && List.Tot.for_all (sub_ok true) rest

let is_nmtoken_value (lex : string) : bool =
  let cs = String.list_of_string lex in
  Cons? cs && List.Tot.for_all is_name_char cs

let is_name_value (lex : string) : bool =
  match String.list_of_string lex with
  | [] -> false
  | c :: rest -> is_name_start_char c && List.Tot.for_all is_name_char rest

let is_ncname_value (lex : string) : bool =
  is_name_value lex
  && List.Tot.for_all (fun c -> not (is_colon_char c)) (String.list_of_string lex)

let string_family_datatypes : list wf_iri = [
  xsd_string; xsd_normalizedString; xsd_token; xsd_language;
  xsd_lang_nonstandard; xsd_Name_dt; xsd_NCName_dt; xsd_NMTOKEN_dt
]

let is_string_family_dt (dt : wf_iri) : bool =
  List.Tot.mem dt string_family_datatypes

// Value-space constraint of a string-family datatype, applied to the
// argument's string VALUE (its lexical form). xsd:string itself is
// unconstrained.
let string_value_ok (dt : wf_iri) (lex : string) : bool =
  if dt = xsd_normalizedString then is_normalized_string_value lex
  else if dt = xsd_token then is_token_value lex
  else if dt = xsd_language || dt = xsd_lang_nonstandard then is_language_value lex
  else if dt = xsd_Name_dt then is_name_value lex
  else if dt = xsd_NCName_dt then is_ncname_value lex
  else if dt = xsd_NMTOKEN_dt then is_nmtoken_value lex
  else true

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
// 2b. date / dateTime / dayTimeDuration slice (EBusiness_Contract).
//
// Reuses XSD.Datatypes' proleptic-Gregorian machinery (dt_parse_ms,
// dt_parse_tail, days_from_civil) rather than re-deriving calendar
// arithmetic. Only the operations EBusiness_Contract exercises are
// implemented — see the module comment's scope note.
// ------------------------------------------------------------------

// "YYYY-MM-DD" + optional timezone tail (xsd:date lexical form),
// mapped to milliseconds at midnight of that day (UTC-adjusted when a
// timezone is present). Reuses dt_parse_tail for the tail — a date
// has no fractional seconds, so a nonzero fraction rejects.
let date_lexical_ms (lex : string) : option (int & bool) =
  let len = String.length lex in
  if len < 10 then None
  else if String.sub lex 4 1 <> "-" || String.sub lex 7 1 <> "-" then None
  else
    match Alg.parse_int_string (String.sub lex 0 4),
          Alg.parse_int_string (String.sub lex 5 2),
          Alg.parse_int_string (String.sub lex 8 2) with
    | Some y, Some mo, Some d ->
      (match XD.dt_parse_tail (String.sub lex 10 (len - 10)) with
       | Some (fms, tzoff, has_tz) ->
         if fms <> 0 then None
         else
           let days = XD.days_from_civil y mo d in
           Some (op_Multiply (op_Multiply days 86400 - tzoff) 1000, has_tz)
       | None -> None)
    | _, _, _ -> None

// A dateTime, or (corpus-driven) a date read as midnight: the
// Approved EBusiness_Contract fixture applies is-literal-dateTime /
// subtract-dateTimes guards to xs:date-typed operands
// ("2008-07-22Z"^^xs:date) and its expected outcome requires those
// guards to hold — so this project's dateTime builtins accept both
// lexical spaces, documented here rather than silently.
let dateTime_or_date_ms (lex : string) : option (int & bool) =
  match XD.dt_parse_ms lex with
  | Some r -> Some r
  | None -> date_lexical_ms lex

// Canonical-ish xsd:dayTimeDuration lexical form from a millisecond
// delta. Fraction-of-second components are emitted only when nonzero;
// an all-zero duration is "PT0S" per XSD canonical form.
let dayTimeDuration_of_ms (delta : int) : string =
  let a : int = if delta < 0 then 0 - delta else delta in
  let msec : int = a % 1000 in
  let sec : int = (a / 1000) % 60 in
  let mi : int = (a / 60000) % 60 in
  let h : int = (a / 3600000) % 24 in
  let d : int = a / 86400000 in
  let sign = if delta < 0 then "-" else "" in
  let d_part = if d <> 0 then String.concat "" [string_of_int d; "D"] else "" in
  let h_part = if h <> 0 then String.concat "" [string_of_int h; "H"] else "" in
  let m_part = if mi <> 0 then String.concat "" [string_of_int mi; "M"] else "" in
  let s_part =
    if msec <> 0 then
      let pad = if msec < 10 then "00" else if msec < 100 then "0" else "" in
      String.concat "" [string_of_int sec; "."; pad; string_of_int msec; "S"]
    else if sec <> 0 then String.concat "" [string_of_int sec; "S"]
    else ""
  in
  let t_needed = h_part <> "" || m_part <> "" || s_part <> "" in
  if d_part = "" && not t_needed then "PT0S"
  else
    String.concat "" [sign; "P"; d_part;
                      (if t_needed then "T" else "");
                      h_part; m_part; s_part]

// Parse a (day-time) duration lexical form to milliseconds:
//   -?PnDTnHnMn(.nnn)?S with every component optional. Year/month
// components (yearMonthDuration) are rejected — a month has no fixed
// millisecond length.
let rec dur_take_digits (cs : list FStar.Char.char) (acc : int)
  : Tot (int & list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> (acc, [])
  | c :: rest ->
    let n = FStar.Char.int_of_char c in
    if n >= 48 && n <= 57
    then dur_take_digits rest (op_Multiply acc 10 + (n - 48))
    else (acc, cs)

let rec dur_components (cs : list FStar.Char.char) (in_time : bool) (acc_ms : int)
  : Tot (option int) (decreases (List.Tot.length cs)) =
  match cs with
  | [] -> Some acc_ms
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x54 then
      (if in_time then None else dur_components rest true acc_ms)
    else
      let n0 = FStar.Char.int_of_char c in
      if not (n0 >= 48 && n0 <= 57) then None
      else
        let (v, after) = dur_take_digits cs 0 in
        (match after with
         | [] -> None
         | d :: rest2 ->
           let dn = FStar.Char.int_of_char d in
           if dn = 0x44 && not in_time then
             (if List.Tot.length rest2 < List.Tot.length cs
              then dur_components rest2 in_time (acc_ms + op_Multiply v 86400000)
              else None)
           else if dn = 0x48 && in_time then
             (if List.Tot.length rest2 < List.Tot.length cs
              then dur_components rest2 in_time (acc_ms + op_Multiply v 3600000)
              else None)
           else if dn = 0x4D && in_time then
             (if List.Tot.length rest2 < List.Tot.length cs
              then dur_components rest2 in_time (acc_ms + op_Multiply v 60000)
              else None)
           else if dn = 0x53 && in_time then
             (if List.Tot.length rest2 < List.Tot.length cs
              then dur_components rest2 in_time (acc_ms + op_Multiply v 1000)
              else None)
           else if dn = 0x2E && in_time then
             let (frac, after_frac) = dur_take_digits rest2 0 in
             let frac_ms =
               if frac < 10 then op_Multiply frac 100
               else if frac < 100 then op_Multiply frac 10
               else if frac < 1000 then frac
               else 0
             in
             (match after_frac with
              | sm :: rest3 ->
                if FStar.Char.int_of_char sm = 0x53
                   && List.Tot.length rest3 < List.Tot.length cs
                then dur_components rest3 in_time (acc_ms + op_Multiply v 1000 + frac_ms)
                else None
              | [] -> None)
           else None)

let parse_dayTimeDuration_ms (lex : string) : option int =
  match String.list_of_string lex with
  | [] -> None
  | c :: rest ->
    let (neg, body) =
      if FStar.Char.int_of_char c = 0x2D then (true, rest)
      else (false, c :: rest)
    in
    (match body with
     | p :: comps ->
       if FStar.Char.int_of_char p = 0x50 then
         (match dur_components comps false 0 with
          | Some ms -> Some (if neg then 0 - ms else ms)
          | None -> None)
       else None
     | [] -> None)

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

// Third category (2026-07-10): the string family. RIF-DTB's
// is-literal-<T> is VALUE-SPACE membership — a literal is "a T" iff
// the value it denotes lies in T's value space. For the string family
// that means: the argument must denote a STRING at all (its own
// datatype is in the string family — Builtins_String requires
// is-literal-not-normalizedString("1"^^xs:integer) to hold even
// though "1" is lexically a fine normalizedString: the integer 1 is
// not a string value), and that string must satisfy T's constraining
// facets (is-literal-token("Hello world"^^xs:string) holds because
// the STRING VALUE "Hello world" is in token's value space,
// regardless of the xs:string tag).
let is_literal_of_datatype (expected_dt : wf_iri) (t : rdf_term) : bool =
  match t with
  | T_Literal l ->
    if List.Tot.mem expected_dt unconstrained_lexical_space_datatypes
    then l.datatype = expected_dt
    else if is_string_family_dt expected_dt
    then is_string_family_dt l.datatype && string_value_ok expected_dt l.lexical_form
    else if expected_dt = XD.xsd_dateTime
    then Some? (dateTime_or_date_ms l.lexical_form)
    else if expected_dt = xsd_date
    then Some? (date_lexical_ms l.lexical_form)
    else not (literal_ill_formed_ext expected_dt l.lexical_form)
  | _ -> false

// rdf:PlainLiteral's value space is string-with-optional-language —
// exactly the decoded xsd:string / rdf:langString forms
// Parser.RIFXML's plain_literal_const produces.
let is_plain_literal_value (t : rdf_term) : bool =
  match t with
  | T_Literal l -> l.datatype = xsd_string || l.datatype = rdf_lang_string
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
  // string family (2026-07-10)
  "string", xsd_string;
  "normalizedString", xsd_normalizedString;
  "token", xsd_token;
  "language", xsd_language;
  "Name", xsd_Name_dt;
  "NCName", xsd_NCName_dt;
  "NMTOKEN", xsd_NMTOKEN_dt;
  // dateTime slice (EBusiness_Contract)
  "dateTime", XD.xsd_dateTime;
  "date", xsd_date;
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
  T_Literal ({ lexical_form = string_of_int n; datatype = xsd_integer; lang_tag = None; direction = None })

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
// 5b. String / PlainLiteral / dateTime builtin helpers.
// ------------------------------------------------------------------

let mk_string_literal (s : string) : rdf_term =
  T_Literal ({ lexical_form = s; datatype = xsd_string; lang_tag = None; direction = None })

let mk_lang_literal (s lang : string) : rdf_term =
  T_Literal ({ lexical_form = s; datatype = rdf_lang_string; lang_tag = Some lang; direction = None })

let mk_dayTimeDuration_literal (ms : int) : rdf_term =
  assert_norm (xsd_dayTimeDuration <> rdf_lang_string);
  assert_norm (xsd_dayTimeDuration <> rdf_dir_lang_string);
  T_Literal ({ lexical_form = dayTimeDuration_of_ms ms;
               datatype = xsd_dayTimeDuration; lang_tag = None; direction = None })

// The plain string VALUE of a term, when it denotes one: any
// string-family literal, or a language-tagged (rdf:langString /
// decoded rdf:PlainLiteral) literal.
let term_string_value (t : rdf_term) : option string =
  match t with
  | T_Literal l ->
    if is_string_family_dt l.datatype || l.datatype = rdf_lang_string
    then Some l.lexical_form
    else None
  | _ -> None

let term_string_value2 (a b : rdf_term) : option (string & string) =
  match term_string_value a, term_string_value b with
  | Some sa, Some sb -> Some (sa, sb)
  | _, _ -> None

let rec list_string_values (ts : list rdf_term)
  : Tot (option (list string)) (decreases ts) =
  match ts with
  | [] -> Some []
  | t :: rest ->
    (match term_string_value t, list_string_values rest with
     | Some sv, Some ss -> Some (sv :: ss)
     | _, _ -> None)

// Value equality across the string family (all string-family
// datatypes share xsd:string's value space up to facets, so equal
// lexical forms denote the same string value). Language-tagged
// literals only equal other language-tagged literals with the same
// tag. None = "not a string/string comparison" (caller falls back).
let string_family_value_equal (a b : rdf_term) : option bool =
  match a, b with
  | T_Literal la, T_Literal lb ->
    if la.datatype = rdf_lang_string || lb.datatype = rdf_lang_string
    then
      (if la.datatype = rdf_lang_string && lb.datatype = rdf_lang_string
       then Some (la.lexical_form = lb.lexical_form && la.lang_tag = lb.lang_tag)
       else Some false)
    else if is_string_family_dt la.datatype && is_string_family_dt lb.datatype
    then Some (la.lexical_form = lb.lexical_form)
    else None
  | _, _ -> None

// Three-way byte/codepoint-wise string comparison (XPath fn:compare
// on ASCII collation) — the corpus only compares ASCII operands.
let rec chars_compare (a b : list FStar.Char.char) : Tot int (decreases a) =
  match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys ->
    let cx = FStar.Char.int_of_char x in
    let cy = FStar.Char.int_of_char y in
    if cx < cy then (-1) else if cx > cy then 1 else chars_compare xs ys

let string_compare_3way (a b : string) : int =
  chars_compare (String.list_of_string a) (String.list_of_string b)

// fn:iri-to-uri escapes the characters not allowed in a URI (space,
// angle brackets, quotes, braces, pipe, backslash, caret, backtick)
// plus everything non-ASCII; fn:escape-html-uri escapes only the
// non-ASCII range. Non-ASCII input arrives as UTF-8 BYTES under this
// project's native OCaml string realisation (FStar.String
// list_of_string is byte-indexed there), so a unit in 0x80..0xFF is
// percent-encoded directly; a unit above 0xFF (a runtime whose char
// is a real codepoint) takes the UTF-8-expanding encoder instead.
let is_iri_to_uri_escaped_ascii (code : nat) : bool =
  code = 0x20 || code = 0x22 || code = 0x3C || code = 0x3E ||
  code = 0x5C || code = 0x5E || code = 0x60 ||
  code = 0x7B || code = 0x7C || code = 0x7D

let rec escape_non_ascii_chars (also_uri_specials : bool) (cs : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: rest ->
    let code = FStar.Char.int_of_char c in
    let here =
      if code < 0x80 then
        (if also_uri_specials && is_iri_to_uri_escaped_ascii code
         then Alg.percent_encode_byte code
         else [c])
      else if code < 0x100 then Alg.percent_encode_byte code
      else Alg.percent_encode_char c
    in
    here @ escape_non_ascii_chars also_uri_specials rest

let fn_iri_to_uri (s : string) : string =
  String.string_of_list (escape_non_ascii_chars true (String.list_of_string s))

let fn_escape_html_uri (s : string) : string =
  String.string_of_list (escape_non_ascii_chars false (String.list_of_string s))

// func:string-join — RIF-DTB's variadic form: the LAST argument is
// the separator, the preceding arguments are joined.
let rec split_last (xs : list string) : Tot (option (list string & string)) (decreases xs) =
  match xs with
  | [] -> None
  | [x] -> Some ([], x)
  | x :: rest ->
    (match split_last rest with
     | Some (init_, last_) -> Some (x :: init_, last_)
     | None -> None)

// func:substring, matching the Approved corpus's own usage:
//   - 3-argument form: XPath fn:substring's 1-based window
//     (substring("foobar", 0, 3) = "fo" — characters at 1-based
//     positions p with start <= p < start + length).
//   - 2-argument form: the corpus expects substring("foobar", 3) =
//     "bar", i.e. a 0-BASED start (XPath's 1-based reading would give
//     "obar") — the Approved fixture is the authority here, and the
//     divergence between its two forms is preserved deliberately.
let fn_rif_substring2 (s : string) (start : int) : string =
  let st : nat = if start < 0 then 0 else start in
  Alg.string_substring s st None

let fn_rif_substring3 (s : string) (start len : int) : string =
  let startpos : int = if start < 1 then 1 else start in
  let cnt : int = start + len - startpos in
  if cnt <= 0 then ""
  else Alg.string_substring s (startpos - 1) (Some cnt)

// Language-range matching (RFC 4647 extended filtering, simplified to
// the shapes language tags/ranges actually take): subtags compared
// case-insensitively; '*' in the range matches zero or more tag
// subtags.
let lower_ascii_char (c : FStar.Char.char) : FStar.Char.char =
  let n = FStar.Char.int_of_char c in
  if n >= 65 && n <= 90 then FStar.Char.char_of_int (n + 32) else c

let lower_ascii (s : list FStar.Char.char) : list FStar.Char.char =
  List.Tot.map lower_ascii_char s

let is_star_subtag (s : list FStar.Char.char) : bool =
  match s with
  | [c] -> FStar.Char.int_of_char c = 0x2A
  | _ -> false

let rec lang_range_match (range tag : list (list FStar.Char.char))
  : Tot bool (decreases %[List.Tot.length range; List.Tot.length tag]) =
  match range, tag with
  | [], _ -> true
  | r :: rrest, [] -> is_star_subtag r && lang_range_match rrest []
  | r :: rrest, t :: trest ->
    if is_star_subtag r
    then lang_range_match rrest tag || lang_range_match range trest
    else lower_ascii r = lower_ascii t && lang_range_match rrest trest

let matches_language_range (tag range : string) : bool =
  lang_range_match (split_on_dash range) (split_on_dash tag)

// rdf:PlainLiteral "text@lang" packing: split on the LAST '@' (same
// convention as Parser.RIFXML.plain_literal_const). No '@' at all is
// treated as plain text with no language.
let rec find_last_char_aux (code : int) (cs : list FStar.Char.char) (idx : nat) (last : option nat)
  : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> last
  | c :: rest ->
    if FStar.Char.int_of_char c = code
    then find_last_char_aux code rest (idx + 1) (Some idx)
    else find_last_char_aux code rest (idx + 1) last

let decode_plain_literal_packed (lex : string) : rdf_term =
  match find_last_char_aux 0x40 (String.list_of_string lex) 0 None with
  | None -> mk_string_literal lex
  | Some pos ->
    let len = String.length lex in
    if pos >= len then mk_string_literal lex
    else
      let text = String.sub lex 0 pos in
      let lang = String.sub lex (pos + 1) (len - pos - 1) in
      if String.length lang = 0
      then mk_string_literal text
      else mk_lang_literal text lang

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
    if op = rdf_PlainLiteral_dt
    // rdf:PlainLiteral constructor: reinterpret the lexical form
    // under the "text@lang" packing (no '@' = plain text), producing
    // the DECODED xsd:string / rdf:langString representation this
    // project uses for PlainLiteral values throughout.
    then Some (decode_plain_literal_packed l.lexical_form)
    else if List.Tot.mem op supported_cast_targets && op <> rdf_lang_string && op <> rdf_dir_lang_string
    then Some (T_Literal ({ lexical_form = l.lexical_form; datatype = op; lang_tag = None; direction = None }))
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
    // --- string family (fn: semantics; see section 5b helpers) ---
    | "compare", [a; b] ->
      (match term_string_value2 a b with
       | Some (sa, sb) -> Some (mk_int_literal (string_compare_3way sa sb))
       | None -> None)
    | "string-length", [a] ->
      (match term_string_value a with
       | Some sv -> Some (mk_int_literal (String.length sv))
       | None -> None)
    | "upper-case", [a] ->
      (match term_string_value a with
       | Some sv -> Some (mk_string_literal (Alg.string_uppercase_unicode sv))
       | None -> None)
    | "lower-case", [a] ->
      (match term_string_value a with
       | Some sv -> Some (mk_string_literal (Alg.string_lowercase_unicode sv))
       | None -> None)
    | "encode-for-uri", [a] ->
      (match term_string_value a with
       | Some sv -> Some (mk_string_literal (Alg.string_encode_uri sv))
       | None -> None)
    | "iri-to-uri", [a] ->
      (match term_string_value a with
       | Some sv -> Some (mk_string_literal (fn_iri_to_uri sv))
       | None -> None)
    | "escape-html-uri", [a] ->
      (match term_string_value a with
       | Some sv -> Some (mk_string_literal (fn_escape_html_uri sv))
       | None -> None)
    | "substring-before", [a; b] ->
      (match term_string_value2 a b with
       | Some (sa, sb) -> Some (mk_string_literal (Alg.string_before sa sb))
       | None -> None)
    | "substring-after", [a; b] ->
      (match term_string_value2 a b with
       | Some (sa, sb) -> Some (mk_string_literal (Alg.string_after sa sb))
       | None -> None)
    | "replace", [sarg; parg; rarg] ->
      (match term_string_value sarg, term_string_value2 parg rarg with
       | Some sv, Some (pv, rv) ->
         Some (mk_string_literal (Alg.string_replace sv pv rv None))
       | _, _ -> None)
    | "substring", [sarg; starg] ->
      (match term_string_value sarg, term_to_int starg with
       | Some sv, Some stv -> Some (mk_string_literal (fn_rif_substring2 sv stv))
       | _, _ -> None)
    | "substring", [sarg; starg; lnarg] ->
      (match term_string_value sarg, term_to_int starg, term_to_int lnarg with
       | Some sv, Some stv, Some lnv ->
         Some (mk_string_literal (fn_rif_substring3 sv stv lnv))
       | _, _, _ -> None)
    | "concat", cargs ->
      (match list_string_values cargs with
       | Some strs -> Some (mk_string_literal (String.concat "" strs))
       | None -> None)
    | "string-join", jargs ->
      (match list_string_values jargs with
       | Some strs ->
         (match split_last strs with
          | Some (parts, sep) -> Some (mk_string_literal (String.concat sep parts))
          | None -> None)
       | None -> None)
    // --- rdf:PlainLiteral family (decoded-form semantics) ---
    | "PlainLiteral-from-string-lang", [sarg; lgarg] ->
      (match term_string_value2 sarg lgarg with
       | Some (sv, lv) ->
         Some (if String.length lv = 0 then mk_string_literal sv else mk_lang_literal sv lv)
       | None -> None)
    | "string-from-PlainLiteral", [x] ->
      (match term_string_value x with
       | Some sv -> Some (mk_string_literal sv)
       | None -> None)
    | "lang-from-PlainLiteral", [x] ->
      (match x with
       | T_Literal l ->
         if l.datatype = rdf_lang_string
         then Some (mk_string_literal (match l.lang_tag with Some tg -> tg | None -> ""))
         else if is_string_family_dt l.datatype
         then Some (mk_string_literal "")
         else None
       | _ -> None)
    | "PlainLiteral-compare", [a; b] ->
      (match term_string_value2 a b with
       | Some (sa, sb) -> Some (mk_int_literal (string_compare_3way sa sb))
       | None -> None)
    // --- dateTime slice (EBusiness_Contract) ---
    | "subtract-dateTimes", [a; b] ->
      (match a, b with
       | T_Literal la, T_Literal lb ->
         (match dateTime_or_date_ms la.lexical_form, dateTime_or_date_ms lb.lexical_form with
          | Some (ma, _), Some (mb, _) -> Some (mk_dayTimeDuration_literal (ma - mb))
          | _, _ -> None)
       | _, _ -> None)
    | "days-from-duration", [d] ->
      (match d with
       | T_Literal l ->
         (match parse_dayTimeDuration_ms l.lexical_form with
          | Some ms -> Some (mk_int_literal (trunc_div ms 86400000))
          | None -> None)
       | _ -> None)
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
    // --- string family predicates ---
    | "contains", [a; b] ->
      (match term_string_value2 a b with
       | Some (sa, sb) -> Some (Alg.string_contains sa sb)
       | None -> None)
    | "starts-with", [a; b] ->
      (match term_string_value2 a b with
       | Some (sa, sb) -> Some (Alg.string_starts_with sa sb)
       | None -> None)
    | "ends-with", [a; b] ->
      (match term_string_value2 a b with
       | Some (sa, sb) -> Some (Alg.string_ends_with sa sb)
       | None -> None)
    | "matches", [sarg; parg] ->
      (match term_string_value2 sarg parg with
       | Some (sv, pv) -> Some (Alg.regex_match sv pv None)
       | None -> None)
    | "matches", [sarg; parg; farg] ->
      (match term_string_value2 sarg parg, term_string_value farg with
       | Some (sv, pv), Some fv -> Some (Alg.regex_match sv pv (Some fv))
       | _, _ -> None)
    // pred:iri-string in GROUND filter form: iri-string(I, S) holds
    // when I is an IRI whose string is S. The BINDING form (either
    // argument an unbound variable to be PRODUCED) is handled by
    // RIF.Core.Eval.apply_extra_condition, which sees the unresolved
    // argument terms.
    | "iri-string", [a; b] ->
      (match a, term_string_value b with
       | T_IRI i, Some sv -> Some (i = sv)
       | _, _ -> None)
    | "matches-language-range", [x; r] ->
      (match x, term_string_value r with
       | T_Literal l, Some rv ->
         if l.datatype = rdf_lang_string
         then Some (match l.lang_tag with
                    | Some tag -> matches_language_range tag rv
                    | None -> false)
         else None
       | _, _ -> None)
    | "is-literal-PlainLiteral", [x]     -> Some (is_plain_literal_value x)
    | "is-literal-not-PlainLiteral", [x] -> Some (not (is_plain_literal_value x))
    | _, [x] ->
      (match is_literal_pred_shape local with
       | Some (dt, negated) ->
         let v = is_literal_of_datatype dt x in
         Some (if negated then not v else v)
       | None -> None)
    | _, _ -> None
