module XSD.Datatypes

// Slice 1 of the reusable-foundations stratification — current-state.md
// "Standing priorities" item 4 / issue #235, owner directive 2026-07-04:
// "the split's FIRST-CLASS deliverables are reusable foundation modules
// shared by every parser/serializer/evaluator instead of today's
// scatter" — this module is the XSD.Datatypes leg of that directive
// (RDF.IRI / RDF.Unicode / RDF.LanguageTag are separate, tracked
// follow-ups; see docs/designissues/2026-07-05-xsd-datatypes-module.md).
//
// Today the datatype logic this module is meant to own is scattered
// across three places:
//   - SPARQL11.Algebra.fst  — numeric promotion (ER_Num/ER_Dec/ER_Dbl)
//     and the lexical parsers (parse_int_string, parse_to_scaled,
//     parse_double_to_scaled).
//   - RDF.Graph.Executable.fst — datatype_value_eq (xsd:integer /
//     xsd:decimal value-space equality).
//   - SHACL.Validation.fst — XSD ill-formed literal detection
//     (boolean + integer-family ranges + decimal + dateTime) and
//     xsd:dateTime ordering for sh:minInclusive/maxInclusive/etc.
//
// SLICE 1 SCOPE (this file):
//   - The numeric-lexical parsers (parse_int_string, parse_to_scaled,
//     parse_double_to_scaled, pow10) and the xsd:dateTime IRI constant
//     are RE-EXPORTED from SPARQL11.Algebra rather than re-derived here.
//     SPARQL11.Algebra.fst is UNTOUCHED — this module only adds a new
//     read-only import edge onto it, so Algebra's own verification and
//     its ~40+ internal call sites carry zero migration risk in this
//     slice. A follow-up slice inverts the dependency (canonical
//     definitions move here, Algebra re-exports from XSD.Datatypes)
//     once Algebra's admit-risk is separately assessed — see the design
//     note.
//   - The ONE migrated consumer is SHACL.Validation's XSD ill-formed
//     literal detection + xsd:dateTime ordering + numeric-literal
//     comparison. That logic previously lived directly in
//     SHACL.Validation.fst (section "11g" and "XSD ill-formed literal
//     detection"); it has been MOVED here verbatim (not just
//     duplicated) and SHACL.Validation.fst now calls into this module.
//   - RDF.Graph.Executable's `datatype_value_eq` is NOT migrated in
//     slice 1: RDF.Graph.Executable is the foundational (class F)
//     module that fires every suite on change (OWL closure,
//     Inconsistency detection, every parser/serialiser), and the risk
//     of a slice-1 regression there is disproportionate to the
//     consolidation win. Left in place, documented as the slice-2
//     candidate in the design note.
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries (rule #10).
//   - No "(*" or "*)" inside comments (rule #12); this file uses // only
//     per the 2026-07-04 owner-ratified comment rule.

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
// Alias, not `open` — SPARQL11.Algebra defines SPARQL-expression
// machinery (FILTER/BIND eval_result, ER_Num/ER_Dec/ER_Dbl, etc.) whose
// short names would otherwise collide with this module's own
// datatype-level vocabulary. Only the four pure lexical/numeric helpers
// below are consumed from it.
module Alg = SPARQL11.Algebra

// --- Canonical numeric-lexical parsers ---------------------------------
//
// Re-exported from SPARQL11.Algebra for slice 1 (see file banner).
// Equivalence-preserving: these are literally the same functions Algebra
// already verifies, not reimplementations, so there is no drift risk.
// Anti-pattern #8 reminder for any future caller: try
// parse_double_to_scaled BEFORE parse_to_scaled — E-notation lexical
// forms get mis-parsed by the non-double-aware parser first.

let parse_int_string = Alg.parse_int_string
let parse_to_scaled = Alg.parse_to_scaled
let parse_double_to_scaled = Alg.parse_double_to_scaled
let pow10 = Alg.pow10

// xsd:dateTime is defined in SPARQL11.Algebra (not RDF.Graph.Executable,
// which only carries the string/boolean/numeric-family constants);
// re-exported here so this module's dateTime helpers don't need two
// import paths for "the xsd:* constants."
let xsd_dateTime = Alg.xsd_dateTime

// xsd:float likewise lives in SPARQL11.Algebra (xsd:double is the one
// numeric-family constant RDF.Graph.Executable already carries) —
// re-exported for the same reason as xsd_dateTime above, and needed by
// this file's ill-formed-literal float/double lexical checks below.
let xsd_float = Alg.xsd_float

// --- Numeric comparison for min/maxInclusive/Exclusive -----------------
//
// MOVED from SHACL.Validation.fst (was section "11g"). Reuses the
// parsers above (rule #8: double-aware parsing, not bare int) rather
// than re-deriving one.

let literal_to_scaled (l : literal) : option (int & nat) =
  if l.datatype = xsd_double then parse_double_to_scaled l.lexical_form
  else if l.datatype = xsd_integer || l.datatype = xsd_decimal then parse_to_scaled l.lexical_form
  else None

let scaled_cmp (a b : (int & nat)) : int =
  let (am, asc) = a in
  let (bm, bsc) = b in
  if asc = bsc then (if am < bm then -1 else if am > bm then 1 else 0)
  else if asc < bsc then
    (let am' = op_Multiply am (pow10 (bsc - asc)) in
     if am' < bm then -1 else if am' > bm then 1 else 0)
  else
    (let bm' = op_Multiply bm (pow10 (asc - bsc)) in
     if am < bm' then -1 else if am > bm' then 1 else 0)

// --- xsd:dateTime ordering (moved from SHACL.Validation.fst) -----------
//
// Parses "YYYY-MM-DDTHH:MM:SS(.fraction)?(Z|+HH:MM|-HH:MM)?" into a
// millisecond position on the proleptic Gregorian timeline plus a
// has-timezone flag. Two dateTimes are comparable only when both have
// a timezone or neither does — XML Schema's partial order makes
// mixed tz/naive comparison indeterminate (within +/-14h). `days_from_civil`
// is the standard civil-date day-count algorithm; every intermediate here
// is non-negative for 4-digit years (the only years XSD's lexical form
// admits without an expanded-year sign), so F*'s int division/modulus
// never see negative operands.

let days_from_civil (y m d : int) : int =
  let y' = if m <= 2 then y - 1 else y in
  let era = (if y' >= 0 then y' else y' - 399) / 400 in
  let yoe = y' - op_Multiply era 400 in
  let mp = (m + 9) % 12 in
  let doy = (op_Multiply 153 mp + 2) / 5 + d - 1 in
  let doe = op_Multiply yoe 365 + yoe / 4 - yoe / 100 + doy in
  op_Multiply era 146097 + doe - 719468

// Parse the fraction+timezone tail (everything after the seconds
// field): optional ".<digits>" then one of "", "Z", "+HH:MM",
// "-HH:MM". Returns (fraction_ms, tz_offset_seconds, has_tz).
let dt_parse_tail (tail : string) : option (int & int & bool) =
  let len = String.length tail in
  // Split off the fraction, if any.
  let (frac_ms, tz_start) =
    if len >= 2 && String.sub tail 0 1 = "." then
      // take up to 3 fraction digits for millisecond precision
      let rec frac_end (pos : nat{pos <= len}) : Tot (r:nat{pos <= r /\ r <= len}) (decreases (len - pos)) =
        if pos < len then
          (let c = FStar.Char.int_of_char (String.index tail pos) in
           if c >= 48 && c <= 57 then frac_end (pos + 1) else pos)
        else pos
      in
      let fe = frac_end 1 in
      if fe = 1 then (None, 0)  // "." with no digits: ill-formed
      else
        let dig_len : nat = if fe - 1 > 3 then 3 else fe - 1 in
        (match parse_int_string (String.sub tail 1 dig_len) with
         | Some f ->
           let ms = if dig_len = 1 then op_Multiply f 100
                    else if dig_len = 2 then op_Multiply f 10
                    else f in
           (Some ms, fe)
         | None -> (None, 0))
    else (Some 0, 0)
  in
  match frac_ms with
  | None -> None
  | Some fms ->
    let rest_len = len - tz_start in
    if rest_len = 0 then Some (fms, 0, false)
    else if rest_len = 1 && String.sub tail tz_start 1 = "Z" then Some (fms, 0, true)
    else if rest_len = 6 then
      let sign_s = String.sub tail tz_start 1 in
      if sign_s = "+" || sign_s = "-" then
        (match parse_int_string (String.sub tail (tz_start + 1) 2),
               parse_int_string (String.sub tail (tz_start + 4) 2) with
         | Some th, Some tm ->
           let off = op_Multiply th 3600 + op_Multiply tm 60 in
           Some (fms, (if sign_s = "-" then 0 - off else off), true)
         | _, _ -> None)
      else None
    else None

let dt_parse_ms (s : string) : option (int & bool) =
  let len = String.length s in
  if len < 19 then None
  else
    match parse_int_string (String.sub s 0 4),
          parse_int_string (String.sub s 5 2),
          parse_int_string (String.sub s 8 2),
          parse_int_string (String.sub s 11 2),
          parse_int_string (String.sub s 14 2),
          parse_int_string (String.sub s 17 2) with
    | Some y, Some mo, Some d, Some h, Some mi, Some se ->
      (match dt_parse_tail (String.sub s 19 (len - 19)) with
       | Some (fms, tzoff, has_tz) ->
         let days = days_from_civil y mo d in
         let secs = op_Multiply days 86400 + op_Multiply h 3600 + op_Multiply mi 60 + se - tzoff in
         Some (op_Multiply secs 1000 + fms, has_tz)
       | None -> None)
    | _, _, _, _, _, _ -> None

let dt_cmp (a b : string) : option int =
  match dt_parse_ms a, dt_parse_ms b with
  | Some (ma, tza), Some (mb, tzb) ->
    if tza = tzb then Some (if ma < mb then -1 else if ma > mb then 1 else 0)
    else None
  | _, _ -> None

let both_datetimes (a b : literal) : bool =
  a.datatype = xsd_dateTime && b.datatype = xsd_dateTime

let numeric_cmp_le (a b : literal) : option bool =
  if both_datetimes a b
  then (match dt_cmp a.lexical_form b.lexical_form with Some c -> Some (c <= 0) | None -> None)
  else
    match literal_to_scaled a, literal_to_scaled b with
    | Some sa, Some sb -> Some (scaled_cmp sa sb <= 0)
    | _, _ -> None

let numeric_cmp_lt (a b : literal) : option bool =
  if both_datetimes a b
  then (match dt_cmp a.lexical_form b.lexical_form with Some c -> Some (c < 0) | None -> None)
  else
    match literal_to_scaled a, literal_to_scaled b with
    | Some sa, Some sb -> Some (scaled_cmp sa sb < 0)
    | _, _ -> None

// --- XSD ill-formed literal detection (moved from SHACL.Validation.fst)
//
// SHACL sh:datatype: "A literal matches a datatype if the literal's
// datatype has the same IRI and, for the datatypes supported by
// SPARQL 1.1, is not an ill-typed literal." Exercised by
// core/node/datatype-001 ("aldi"^^xsd:integer),
// core/property/datatype-ill-formed ("300"^^xsd:byte, "c"^^xsd:byte)
// and core/property/or-datatypes-001 ("none"^^xsd:boolean).
// Conservative by construction: datatypes not listed are never
// flagged, so this can only ADD violations the spec requires, not
// invent ones it doesn't.

let is_ascii_digit (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in n >= 48 && n <= 57

// Chars-based cores, factored out so `is_float_lexical` below (which needs
// to check a mantissa substring, not a whole standalone lexical form) can
// reuse the exact same "optional sign then digit body" / "optional sign
// then digit-or-dot body" rules `is_integer_lexical`/`is_decimal_lexical`
// already enforce, rather than re-deriving them.
let is_signed_digits_chars (chars : list FStar.Char.char) : bool =
  match chars with
  | [] -> false
  | c :: rest ->
    let ci = FStar.Char.int_of_char c in
    let digits = if ci = 43 || ci = 45 then rest else c :: rest in
    Cons? digits && List.Tot.for_all is_ascii_digit digits

let is_decimal_lexical_chars (chars : list FStar.Char.char) : bool =
  match chars with
  | [] -> false
  | c :: rest ->
    let ci = FStar.Char.int_of_char c in
    let body = if ci = 43 || ci = 45 then rest else c :: rest in
    Cons? body &&
    List.Tot.for_all (fun ch -> is_ascii_digit ch || FStar.Char.int_of_char ch = 46) body &&
    List.Tot.length (List.Tot.filter (fun ch -> FStar.Char.int_of_char ch = 46) body) <= 1 &&
    List.Tot.existsb is_ascii_digit body

let is_integer_lexical (lex : string) : bool =
  is_signed_digits_chars (String.list_of_string lex)

let is_decimal_lexical (lex : string) : bool =
  is_decimal_lexical_chars (String.list_of_string lex)

// Splits a char list at the FIRST 'e'/'E' (structural recursion — a genuine
// subterm decrease, unlike `strip_trailing_zeros_fuel`'s reverse-based
// walk, so no `fuel` parameter is needed here). Returns
// (chars_before_e, Some chars_after_e) if an 'e'/'E' was found, else
// (original_chars, None).
let rec split_at_e (chars : list FStar.Char.char)
  : Tot (list FStar.Char.char & option (list FStar.Char.char)) (decreases chars) =
  match chars with
  | [] -> ([], None)
  | c :: rest ->
    let n = FStar.Char.int_of_char c in
    if n = 101 (* 'e' *) || n = 69 (* 'E' *) then ([], Some rest)
    else
      let (before, after) = split_at_e rest in
      (c :: before, after)

// xsd:float and xsd:double share one lexical grammar (XML Schema Part 2
// §3.2.4/3.2.5): the three special tokens "NaN"/"INF"/"-INF" (note:
// "+INF" is NOT a valid lexical form — only unsigned "INF" denotes
// positive infinity), OR a decimal-lexical mantissa (reusing
// `is_decimal_lexical_chars` — sign?, digits, at most one '.', at least
// one digit) optionally followed by an ('e'|'E') exponent (sign?,
// digit+, reusing `is_signed_digits_chars`). No other junk is permitted
// anywhere (both helpers reject non-digit/non-dot characters), and a
// second 'e'/'E' in the exponent tail correctly fails `is_signed_digits_chars`
// (a bare digit-scan, no dot allowed) rather than silently truncating.
let is_float_lexical (lex : string) : bool =
  if lex = "NaN" || lex = "INF" || lex = "-INF" then true
  else
    let (mantissa, exp_opt) = split_at_e (String.list_of_string lex) in
    is_decimal_lexical_chars mantissa &&
    (match exp_opt with
     | None -> true
     | Some e -> is_signed_digits_chars e)

// Integer-family range check: well-formed integer lexical whose value
// sits inside [lo, hi] (None = unbounded on that side). parse_int_string
// accepts an optional leading '-' but not '+'; '+'-signed literals are
// flagged conservatively-well-formed by skipping the range check only
// when the parse fails on an is_integer_lexical-accepted string.
let int_lexical_in_range (lex : string) (lo hi : option int) : bool =
  is_integer_lexical lex &&
  (match parse_int_string lex with
   | Some n ->
     (match lo with Some l -> n >= l | None -> true) &&
     (match hi with Some h -> n <= h | None -> true)
   | None -> true)

let literal_ill_formed (dt : wf_iri) (lex : string) : bool =
  if dt = xsd_boolean then not (lex = "true" || lex = "false" || lex = "1" || lex = "0")
  else if dt = xsd_integer then not (is_integer_lexical lex)
  else if dt = xsd_decimal then not (is_decimal_lexical lex)
  else if dt = xsd_long then not (int_lexical_in_range lex (Some (0 - 9223372036854775808)) (Some 9223372036854775807))
  else if dt = xsd_int then not (int_lexical_in_range lex (Some (0 - 2147483648)) (Some 2147483647))
  else if dt = xsd_short then not (int_lexical_in_range lex (Some (0 - 32768)) (Some 32767))
  else if dt = xsd_byte then not (int_lexical_in_range lex (Some (0 - 128)) (Some 127))
  else if dt = xsd_unsignedLong then not (int_lexical_in_range lex (Some 0) (Some 18446744073709551615))
  else if dt = xsd_unsignedInt then not (int_lexical_in_range lex (Some 0) (Some 4294967295))
  else if dt = xsd_unsignedShort then not (int_lexical_in_range lex (Some 0) (Some 65535))
  else if dt = xsd_unsignedByte then not (int_lexical_in_range lex (Some 0) (Some 255))
  else if dt = xsd_nonNegativeInteger then not (int_lexical_in_range lex (Some 0) None)
  else if dt = xsd_positiveInteger then not (int_lexical_in_range lex (Some 1) None)
  else if dt = xsd_nonPositiveInteger then not (int_lexical_in_range lex None (Some 0))
  else if dt = xsd_negativeInteger then not (int_lexical_in_range lex None (Some (0 - 1)))
  else if dt = xsd_dateTime then None? (dt_parse_ms lex)
  else if dt = xsd_float || dt = xsd_double then not (is_float_lexical lex)
  else false

// --- decimal-derived datatype family (for facet applicability) ---------
//
// XML Schema Part 2 §4.3.11/4.3.12 define totalDigits/fractionDigits as
// facets of xsd:decimal specifically ("applicable to decimal and types
// derived from decimal" — i.e. xsd:integer and everything the integer
// branch derives). They are NOT applicable to xsd:float/xsd:double
// (IEEE-754 binary floating point has no digit-count facet in the XSD
// facet table at all) even though those types also have numeric lexical
// forms. A caller applying totalDigits/fractionDigits to a non-decimal-
// derived literal should treat the facet as failing closed (mirrors how
// `numeric_cmp_le`/`numeric_cmp_lt` above already fail closed when a
// literal doesn't parse as numeric) rather than silently counting digits
// in a lexical form the facet was never defined over. This predicate is
// exactly the set of datatypes `literal_ill_formed` already recognises
// via `is_integer_lexical`/`is_decimal_lexical`/`int_lexical_in_range`
// (i.e. every ill-formed-check branch above except boolean, dateTime,
// float, double).
let is_decimal_derived_datatype (dt : wf_iri) : bool =
  dt = xsd_decimal || dt = xsd_integer ||
  dt = xsd_long || dt = xsd_int || dt = xsd_short || dt = xsd_byte ||
  dt = xsd_unsignedLong || dt = xsd_unsignedInt || dt = xsd_unsignedShort || dt = xsd_unsignedByte ||
  dt = xsd_nonNegativeInteger || dt = xsd_positiveInteger ||
  dt = xsd_nonPositiveInteger || dt = xsd_negativeInteger
