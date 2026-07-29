module XSD.Facets

(* Interval-based datatype facet satisfiability — OWL 2 DL completion
   program Wave B
   (docs/designissues/2026-07-10-owl2-dl-completion-program.md).

   Scope: STRICTLY the integer-family facet / oneOf / complement shapes
   third_party/testing/owl/type-inconsistency.rdf's Wave-B target fail
   set actually exercises (min/maxInclusive, min/maxExclusive on
   xsd:integer and its restriction subtypes, DataOneOf finite literal
   sets, DataComplementOf of a DataOneOf, and the numeric/string/
   boolean base-datatype-family disjointness table). No decimal/float/
   dateTime facet arithmetic, no pattern/length facets, no general
   regex intersection — none of those are needed by the target tests;
   extend this module (not hack around it) when a fixture demands one.

   BUILD-ORDER NOTE: this module depends ONLY on RDF.Graph.Executable
   (for wf_iri / rdf_term / literal and the xsd:* IRI constants already
   re-exported through its `include OWL.Closure` chain). It deliberately
   does NOT open XSD.Datatypes / SPARQL11.Algebra for their numeric
   lexical parsers: those two modules sit LATE in build-ocaml.sh's
   OCaml COMMON_MODULES compile order (both listed well after
   Tableau.ml / Tableau.Refute.ml, which is where this module's only
   consumer lives), and pulling them earlier would mean reordering a
   long, working dependency chain — exactly the anti-pattern #27 /
   hazard-#11 blast radius the OWL2 Wave B brief warns against. A
   small, self-contained integer lexical parser is duplicated below
   instead (same "acknowledged duplication wart" pattern already used
   by OWL.QueryRewrite.fst / Parser.OWLFunctional.fst for their own
   file-local IRI constants). This keeps XSD.Facets.fst compilable
   immediately before Tableau.fst/Tableau.Refute.fst with zero
   reordering of the existing module list.

   TERMINATION: every recursive function here is structurally
   recursive over a list argument. No admits, no assumes, no --lax. *)

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable

(* -------------------------------------------------------------------
   1. Integer-family datatype recognition + base-family classification.
   ------------------------------------------------------------------- *)

// Datatype IRIs the OWL 2 datatype map adds on top of the XSD set that
// RDF.Term.fsti already re-exports (xsd:string / xsd:decimal /
// xsd:double / xsd:boolean / the integer family). Defined here because
// neither RDF.Term.fsti nor OWL.Closure.fsti carries them.
//
// OWL 2 Syntax, 2nd edition, section 4.1 "Real Numbers, Decimal Numbers,
// and Integers":
//   "The value space of owl:real is the set of all real numbers."
//   "The value space of owl:rational is the set of all rational numbers.
//    It is a subset of the value space of owl:real, and it contains the
//    value space of xsd:decimal."
// so owl:real contains owl:rational contains xsd:decimal contains
// xsd:integer contains each derived integer type. That single number
// line is what `Fam_Numeric` below names.
let owl_real : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#real");
  "http://www.w3.org/2002/07/owl#real"

let owl_rational : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#rational");
  "http://www.w3.org/2002/07/owl#rational"

let xsd_float : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#float");
  "http://www.w3.org/2001/XMLSchema#float"

let is_float_datatype (dt : wf_iri) : bool = dt = xsd_float

// The three datatypes whose value space is DENSE (between any two
// distinct values lies a third) and unbounded: owl:real, owl:rational
// and xsd:decimal. A min/max facet pair over one of them is empty only
// when its endpoints cross or coincide — never merely by adjacency, the
// way an integer-granularity pair can be.
let is_dense_numeric_datatype (dt : wf_iri) : bool =
  dt = owl_real || dt = owl_rational || dt = xsd_decimal

(* xsd:integer and every restriction subtype the RDF/OWL corpus uses.
   xsd:long/xsd:unsignedLong are recognised for VALUE comparison (their
   lexical forms parse as plain digit runs, same as the others) but
   carry no finite natural interval in `base_interval_for` below (an
   int64 bound is not needed by any target fixture). *)
let is_integer_family_datatype (dt : wf_iri) : bool =
  dt = xsd_integer || dt = xsd_long || dt = xsd_int || dt = xsd_short || dt = xsd_byte ||
  dt = xsd_unsignedLong || dt = xsd_unsignedInt || dt = xsd_unsignedShort || dt = xsd_unsignedByte ||
  dt = xsd_nonNegativeInteger || dt = xsd_positiveInteger ||
  dt = xsd_nonPositiveInteger || dt = xsd_negativeInteger

(* Small closed table over the XSD base-type hierarchy (per the Wave B
   design sketch): just enough families to detect cross-family
   emptiness (e.g. xsd:string vs xsd:integer on one property, the
   "inconsistent_datatypes" fixture). dateTime is deliberately NOT
   classified here (out of this wave's scope) — a dateTime-typed
   filler simply never participates in this family clash, which is
   sound (nothing is falsely flagged; a real dateTime clash is just
   not caught by this rule). *)
(* Fam_Float / Fam_Double were added by the 2026-07-29 value-space wave.
   OWL 2 Syntax section 4.1, on why floating-point values are NOT reals:
     "In accordance with this principle, the value space of owl:real is
      defined as being disjoint with the value spaces of xsd:double and
      xsd:float as well."
     "Although floating-point values are numbers, they are not contained
      in the value space of owl:real."
   and section 4.2 keeps the two floating-point value spaces distinct
   from each other (single vs double precision grids). So the numeric
   part of the OWL 2 datatype map is THREE pairwise-disjoint value
   spaces, not one — modelling them as one would let "1.0"^^xsd:float be
   proved equal to "1.0"^^xsd:decimal, which OWL 2 denies. *)
noeq type xsd_family =
  | Fam_Numeric : xsd_family   // the owl:real number line
  | Fam_String  : xsd_family
  | Fam_Boolean : xsd_family
  | Fam_Float   : xsd_family   // xsd:float  — IEEE single grid + specials
  | Fam_Double  : xsd_family   // xsd:double — IEEE double grid + specials

let xsd_family_eq (a b : xsd_family) : bool =
  match a, b with
  | Fam_Numeric, Fam_Numeric -> true
  | Fam_String, Fam_String -> true
  | Fam_Boolean, Fam_Boolean -> true
  | Fam_Float, Fam_Float -> true
  | Fam_Double, Fam_Double -> true
  | _, _ -> false

let classify_family (dt : wf_iri) : option xsd_family =
  if is_integer_family_datatype dt || is_dense_numeric_datatype dt then Some Fam_Numeric
  else if dt = xsd_string then Some Fam_String
  else if dt = xsd_boolean then Some Fam_Boolean
  else if dt = xsd_float then Some Fam_Float
  else if dt = xsd_double then Some Fam_Double
  else None

(* -------------------------------------------------------------------
   2. Minimal integer lexical parser (see build-order note above).
   ------------------------------------------------------------------- *)

let is_ascii_digit (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in n >= 48 && n <= 57

let digit_val (c : FStar.Char.char) : int = FStar.Char.int_of_char c - 48

let rec digits_to_int (chars : list FStar.Char.char) (acc : int)
  : Tot (option int) (decreases chars) =
  match chars with
  | [] -> Some acc
  | c :: tl -> if is_ascii_digit c then digits_to_int tl (op_Multiply acc 10 + digit_val c) else None

(* Optional leading '-'/'+' then one or more ASCII digits — the XSD
   integer-family lexical grammar restricted to what this corpus's
   facet/literal values use (no leading/trailing whitespace, no
   grouping). Returns None on anything else (sound: an unparseable
   bound is simply DROPPED by the caller, never guessed at). *)
let parse_facet_int (lex : string) : option int =
  let chars = FStar.String.list_of_string lex in
  match chars with
  | [] -> None
  | c :: tl ->
    let code = FStar.Char.int_of_char c in
    if code = 45 (* '-' *) then
      (match tl with [] -> None | _ -> (match digits_to_int tl 0 with Some v -> Some (0 - v) | None -> None))
    else if code = 43 (* '+' *) then
      (match tl with [] -> None | _ -> digits_to_int tl 0)
    else digits_to_int chars 0

let literal_int_value (l : literal) : option int =
  if is_integer_family_datatype l.datatype then parse_facet_int l.lexical_form else None

(* -------------------------------------------------------------------
   2b. Minimal xsd:dateTime lexical parser (Wave B dateTime facets).

   Self-contained for the same build-order reason as parse_facet_int
   (see the module banner): XSD.Datatypes.fst carries the reference
   dt_parse_ms / days_from_civil, but it compiles LATE — after
   Tableau.Refute.ml, this module's only consumer. This port reduces a
   TIMEZONED xsd:dateTime to a single UTC-normalised millisecond count,
   giving a TOTAL order over timezoned instants (XSD Part 2 §3.2.7 order
   relation: two dateTimes that both carry a timezone are compared by
   their UTC instants). A dateTime WITHOUT an explicit timezone, an
   expanded/negative year, or any lexical form this restricted parser
   does not accept yields None and is DROPPED by every caller — sound:
   a value we cannot totally place is never used to manufacture an empty
   intersection (a clash). Timezone-less dateTimes sit in a partial
   order (±14h indeterminacy) with the timezoned ones, so refusing to
   place them withholds every uncertain clash. Withholding is sound;
   manufacturing emptiness is not. *)

let xsd_dateTime : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#dateTime");
  "http://www.w3.org/2001/XMLSchema#dateTime"

let is_datetime_datatype (dt : wf_iri) : bool = dt = xsd_dateTime

// xsd:float / owl:rational / owl:real and `is_float_datatype` moved to
// section 1 (they are needed by `classify_family` now that the two
// floating-point value spaces are first-class families).

// Parse the fixed-width substring [pos, pos+n) as an unsigned decimal
// integer (every char must be an ASCII digit). Out-of-range or any
// non-digit -> None (sound: an unparseable field drops the whole value).
let parse_digits_sub (s : string) (pos n : nat) : option int =
  if pos + n > String.length s then None
  else digits_to_int (FStar.String.list_of_string (String.sub s pos n)) 0

// Days from the civil date to 1970-01-01 (Howard Hinnant's algorithm,
// same port as XSD.Datatypes.days_from_civil). Total integer arithmetic.
let days_from_civil (y m d : int) : int =
  let y' = if m <= 2 then y - 1 else y in
  let era = (if y' >= 0 then y' else y' - 399) / 400 in
  let yoe = y' - op_Multiply era 400 in
  let mp = (m + 9) % 12 in
  let doy = (op_Multiply 153 mp + 2) / 5 + d - 1 in
  let doe = op_Multiply yoe 365 + yoe / 4 - yoe / 100 + doy in
  op_Multiply era 146097 + doe - 719468

// Parse the fraction+timezone tail (everything after the seconds field):
// optional ".<digits>" then one of "", "Z", "+HH:MM", "-HH:MM". Returns
// (fraction_ms, tz_offset_seconds, has_tz). Faithful port of
// XSD.Datatypes.dt_parse_tail with parse_digits_sub in place of the
// SPARQL11.Algebra parser (build-order-local duplication, per banner).
let dt_parse_tail (tail : string) : option (int & int & bool) =
  let len = String.length tail in
  let (frac_ms, tz_start) =
    if len >= 2 && String.sub tail 0 1 = "." then
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
        (match parse_digits_sub tail 1 dig_len with
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
        (match parse_digits_sub tail (tz_start + 1) 2,
               parse_digits_sub tail (tz_start + 4) 2 with
         | Some th, Some tm ->
           let off = op_Multiply th 3600 + op_Multiply tm 60 in
           Some (fms, (if sign_s = "-" then 0 - off else off), true)
         | _, _ -> None)
      else None
    else None

// Reduce a timezoned xsd:dateTime lexical form to its UTC-normalised
// millisecond count. Returns None (dropped) unless the value carries an
// explicit timezone — see the section banner for why.
let dt_parse_utc_ms (s : string) : option int =
  let len = String.length s in
  if len < 19 then None
  else if String.sub s 0 1 = "-" then None  // expanded/negative year: out of scope
  else
    match parse_digits_sub s 0 4, parse_digits_sub s 5 2, parse_digits_sub s 8 2,
          parse_digits_sub s 11 2, parse_digits_sub s 14 2, parse_digits_sub s 17 2 with
    | Some y, Some mo, Some d, Some h, Some mi, Some se ->
      (match dt_parse_tail (String.sub s 19 (len - 19)) with
       | Some (fms, tzoff, has_tz) ->
         if has_tz then
           let days = days_from_civil y mo d in
           let secs = op_Multiply days 86400 + op_Multiply h 3600 + op_Multiply mi 60 + se - tzoff in
           Some (op_Multiply secs 1000 + fms)
         else None
       | None -> None)
    | _ -> None

let literal_datetime_key (l : literal) : option int =
  if l.datatype = xsd_dateTime then dt_parse_utc_ms l.lexical_form else None

let term_datetime_key (t : rdf_term) : option int =
  match t with T_Literal l -> literal_datetime_key l | _ -> None

(* -------------------------------------------------------------------
   3. Interval representation over integers.
   ------------------------------------------------------------------- *)

noeq type bound =
  | B_Unbounded : bound
  | B_Incl : int -> bound
  | B_Excl : int -> bound

noeq type interval = { iv_lo : bound; iv_hi : bound }

let full_interval : interval = { iv_lo = B_Unbounded; iv_hi = B_Unbounded }

(* PROVABLY empty (contains no integer)? Unbounded-on-either-side
   intervals are never reported empty here (sound: absence of a proof
   is not a proof of absence). *)
let interval_empty (iv : interval) : bool =
  match iv.iv_lo, iv.iv_hi with
  | B_Incl lo, B_Incl hi -> lo > hi
  | B_Incl lo, B_Excl hi -> lo >= hi
  | B_Excl lo, B_Incl hi -> lo >= hi
  | B_Excl lo, B_Excl hi -> lo >= hi - 1
  | _, _ -> false

(* PROVABLY empty over a DENSE value space (xsd:dateTime, whose value
   space has unbounded fractional-second precision — between any two
   distinct instants lies another). The discrete `B_Excl,B_Excl ->
   lo >= hi - 1` rule of `interval_empty` above is UNSOUND for a dense
   order: minExclusive T / maxExclusive T+1ms is NON-empty (T+0.5ms
   exists), so an open interval is empty only when its endpoints cross
   or coincide, never merely by being adjacent. Used for VS_DateInterval
   intersections; keeping it separate leaves the integer discrete rule
   untouched. *)
let interval_empty_dense (iv : interval) : bool =
  match iv.iv_lo, iv.iv_hi with
  | B_Incl lo, B_Incl hi -> lo > hi
  | B_Incl lo, B_Excl hi -> lo >= hi
  | B_Excl lo, B_Incl hi -> lo >= hi
  | B_Excl lo, B_Excl hi -> lo >= hi
  | _, _ -> false

let tighter_lo (a b : bound) : bound =
  match a, b with
  | B_Unbounded, _ -> b
  | _, B_Unbounded -> a
  | B_Incl x, B_Incl y -> if x >= y then a else b
  | B_Excl x, B_Excl y -> if x >= y then a else b
  | B_Incl x, B_Excl y -> if x > y then a else b
  | B_Excl x, B_Incl y -> if x >= y then a else b

let tighter_hi (a b : bound) : bound =
  match a, b with
  | B_Unbounded, _ -> b
  | _, B_Unbounded -> a
  | B_Incl x, B_Incl y -> if x <= y then a else b
  | B_Excl x, B_Excl y -> if x <= y then a else b
  | B_Incl x, B_Excl y -> if x < y then a else b
  | B_Excl x, B_Incl y -> if x <= y then a else b

let interval_intersect (a b : interval) : interval =
  { iv_lo = tighter_lo a.iv_lo b.iv_lo; iv_hi = tighter_hi a.iv_hi b.iv_hi }

let value_in_interval (v : int) (iv : interval) : bool =
  (match iv.iv_lo with B_Unbounded -> true | B_Incl lo -> v >= lo | B_Excl lo -> v > lo) &&
  (match iv.iv_hi with B_Unbounded -> true | B_Incl hi -> v <= hi | B_Excl hi -> v < hi)

(* Natural bounds for the finite integer subtypes the corpus needs
   (xsd:byte / xsd:unsignedInt / etc, WebOnt-I5.8-style "only N values"
   reasoning). xsd:integer/xsd:long/xsd:unsignedLong: no finite bound
   is asserted here (`full_interval`) — none of the Wave-B target
   fixtures need one, and inventing one would be unsound narrowing. *)
let base_interval_for (dt : wf_iri) : interval =
  if dt = xsd_byte then { iv_lo = B_Incl (0 - 128); iv_hi = B_Incl 127 }
  else if dt = xsd_unsignedByte then { iv_lo = B_Incl 0; iv_hi = B_Incl 255 }
  else if dt = xsd_short then { iv_lo = B_Incl (0 - 32768); iv_hi = B_Incl 32767 }
  else if dt = xsd_unsignedShort then { iv_lo = B_Incl 0; iv_hi = B_Incl 65535 }
  else if dt = xsd_int then { iv_lo = B_Incl (0 - 2147483648); iv_hi = B_Incl 2147483647 }
  else if dt = xsd_unsignedInt then { iv_lo = B_Incl 0; iv_hi = B_Incl 4294967295 }
  else if dt = xsd_nonNegativeInteger then { iv_lo = B_Incl 0; iv_hi = B_Unbounded }
  else if dt = xsd_positiveInteger then { iv_lo = B_Incl 1; iv_hi = B_Unbounded }
  else if dt = xsd_nonPositiveInteger then { iv_lo = B_Unbounded; iv_hi = B_Incl 0 }
  else if dt = xsd_negativeInteger then { iv_lo = B_Unbounded; iv_hi = B_Incl (0 - 1) }
  else full_interval

(* -------------------------------------------------------------------
   4. Facet-pair IRIs + facets -> interval.
   ------------------------------------------------------------------- *)

let facet_min_incl_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#minInclusive");
  "http://www.w3.org/2001/XMLSchema#minInclusive"

let facet_max_incl_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#maxInclusive");
  "http://www.w3.org/2001/XMLSchema#maxInclusive"

let facet_min_excl_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#minExclusive");
  "http://www.w3.org/2001/XMLSchema#minExclusive"

let facet_max_excl_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#maxExclusive");
  "http://www.w3.org/2001/XMLSchema#maxExclusive"

(* facets -> interval, restricted to min/maxInclusive/Exclusive on an
   integer-family base datatype. Any other facet (pattern, length, ...)
   or non-integer base type is DROPPED — sound narrowing: fewer
   constraints can only make refutation harder, never wrong. *)
let rec facets_to_interval (base_dt : wf_iri) (facets : list (wf_iri & rdf_term)) (acc : interval)
  : Tot interval (decreases facets) =
  match facets with
  | [] -> acc
  | (firi, fval) :: tl ->
    let acc' =
      if not (is_integer_family_datatype base_dt) then acc
      else
        match fval with
        | T_Literal l ->
          (match parse_facet_int l.lexical_form with
           | None -> acc
           | Some v ->
             if firi = facet_min_incl_iri then interval_intersect acc { iv_lo = B_Incl v; iv_hi = B_Unbounded }
             else if firi = facet_max_incl_iri then interval_intersect acc { iv_lo = B_Unbounded; iv_hi = B_Incl v }
             else if firi = facet_min_excl_iri then interval_intersect acc { iv_lo = B_Excl v; iv_hi = B_Unbounded }
             else if firi = facet_max_excl_iri then interval_intersect acc { iv_lo = B_Unbounded; iv_hi = B_Excl v }
             else acc)
        | _ -> acc
    in
    facets_to_interval base_dt tl acc'

(* dateTime facets -> interval over UTC-normalised millisecond keys,
   restricted to min/maxInclusive/Exclusive. A facet value that is not a
   TIMEZONED xsd:dateTime literal (`term_datetime_key` = None) is DROPPED
   — sound narrowing: fewer constraints only make refutation harder. The
   resulting interval lives in the dateTime dimension and is only ever
   intersected against other dateTime keys / dateTime intervals (see
   value_set_intersect's VS_DateInterval cases), never against the
   integer intervals `facets_to_interval` builds. *)
let rec datetime_facets_to_interval (facets : list (wf_iri & rdf_term)) (acc : interval)
  : Tot interval (decreases facets) =
  match facets with
  | [] -> acc
  | (firi, fval) :: tl ->
    let acc' =
      match term_datetime_key fval with
      | None -> acc
      | Some v ->
        if firi = facet_min_incl_iri then interval_intersect acc { iv_lo = B_Incl v; iv_hi = B_Unbounded }
        else if firi = facet_max_incl_iri then interval_intersect acc { iv_lo = B_Unbounded; iv_hi = B_Incl v }
        else if firi = facet_min_excl_iri then interval_intersect acc { iv_lo = B_Excl v; iv_hi = B_Unbounded }
        else if firi = facet_max_excl_iri then interval_intersect acc { iv_lo = B_Unbounded; iv_hi = B_Excl v }
        else acc
    in
    datetime_facets_to_interval tl acc'

(* -------------------------------------------------------------------
   4b. Exact rationals (numerator/denominator), the shared concrete-
       domain endpoint model for the owl:real number line.

   OWL 2's numeric value space (owl:real ⊃ owl:rational ⊃ xsd:decimal ⊃
   xsd:integer ⊃ ...) is a single dense line; xsd:decimal and owl:rational
   literals both denote EXACT points on it. "0.5"^^xsd:decimal and
   "1/2"^^owl:rational are the SAME real, and this module must be able to
   prove it (New-Feature-Rational-002). We carry the value as an exact
   fraction num/den (den > 0). No rounding, no float here — see 4c for the
   IEEE-754 float grid, which is a DIFFERENT, discrete value space.
   ------------------------------------------------------------------- *)

type rational = { rn_num : int; rn_den : pos }

let rec pow10 (n : nat) : Tot pos (decreases n) =
  if n = 0 then 1 else op_Multiply 10 (pow10 (n - 1))

let rec pow2i (n : nat) : Tot pos (decreases n) =
  if n = 0 then 1 else op_Multiply 2 (pow2i (n - 1))

// Two exact rationals are equal iff a.num*b.den = b.num*a.den (dens > 0).
let rational_eq (a b : rational) : bool =
  op_Multiply a.rn_num b.rn_den = op_Multiply b.rn_num a.rn_den

// Consume a maximal run of ASCII digits, returning (value, count, rest).
let rec span_digits (cs : list FStar.Char.char) (accv : int) (accn : nat)
  : Tot (int & nat & list FStar.Char.char) (decreases cs) =
  match cs with
  | c :: tl ->
    if is_ascii_digit c then span_digits tl (op_Multiply accv 10 + digit_val c) (accn + 1)
    else (accv, accn, cs)
  | [] -> (accv, accn, cs)

// Parse an optional-sign decimal or scientific lexical form into an EXACT
// rational. Grammar accepted: [+-]? d* ('.' d*)? ([eE] [+-]? d+)? with at
// least one mantissa digit and full consumption. Returns None otherwise
// (sound: an unparseable value is DROPPED by every caller, never guessed).
let parse_decimal_rational (lex : string) : option rational =
  let cs0 = FStar.String.list_of_string lex in
  let (neg, cs1) =
    match cs0 with
    | c :: tl ->
      let n = FStar.Char.int_of_char c in
      if n = 45 then (true, tl) else if n = 43 then (false, tl) else (false, cs0)
    | [] -> (false, cs0) in
  let (ipart, ilen, cs2) = span_digits cs1 0 0 in
  let (fpart, flen, cs3) =
    match cs2 with
    | c :: tl -> if FStar.Char.int_of_char c = 46 then span_digits tl 0 0 else (0, 0, cs2)
    | [] -> (0, 0, cs2) in
  let (ok_exp, expv, cs4) =
    match cs3 with
    | c :: tl ->
      let ec = FStar.Char.int_of_char c in
      if ec = 101 || ec = 69 then
        (match tl with
         | s :: tl2 ->
           let sn = FStar.Char.int_of_char s in
           let (eneg, ed) =
             if sn = 45 then (true, tl2) else if sn = 43 then (false, tl2) else (false, tl) in
           let (ev, elen, r) = span_digits ed 0 0 in
           if elen = 0 then (false, 0, r) else (true, (if eneg then 0 - ev else ev), r)
         | [] -> (false, 0, cs3))
      else (true, 0, cs3)
    | [] -> (true, 0, cs3) in
  if (not ok_exp) || Cons? cs4 || ilen + flen = 0 then None
  else
    let mantissa = op_Multiply ipart (pow10 flen) + fpart in
    let net = expv - flen in
    let signed = if neg then 0 - mantissa else mantissa in
    if net >= 0 then Some ({ rn_num = op_Multiply signed (pow10 net); rn_den = 1 })
    else Some ({ rn_num = signed; rn_den = pow10 (0 - net) })

// Split a char list on the first '/', returning (before, after).
let rec split_slash (cs : list FStar.Char.char) (acc : list FStar.Char.char)
  : Tot (option (list FStar.Char.char & list FStar.Char.char)) (decreases cs) =
  match cs with
  | [] -> None
  | c :: tl ->
    if FStar.Char.int_of_char c = 47 then Some (List.Tot.rev acc, tl)
    else split_slash tl (c :: acc)

// Parse an owl:rational lexical form "num/den" (den a positive integer).
let parse_rational_lex (lex : string) : option rational =
  match split_slash (FStar.String.list_of_string lex) [] with
  | None -> None
  | Some (ns, ds) ->
    (match parse_facet_int (FStar.String.string_of_list ns),
           parse_facet_int (FStar.String.string_of_list ds) with
     | Some n, Some d -> if d > 0 then Some ({ rn_num = n; rn_den = d }) else None
     | _, _ -> None)

// The EXACT rational value of a literal whose datatype places it on the
// owl:real line with an exact lexical-to-value map: integer family
// (v/1), xsd:decimal, owl:rational. Everything else -> None (xsd:float /
// xsd:double are NOT here — their value is the ROUNDED grid point, a
// different value space handled in 4c; conflating them would be unsound).
let term_exact_rational (t : rdf_term) : option rational =
  match t with
  | T_Literal l ->
    if is_integer_family_datatype l.datatype then
      (match parse_facet_int l.lexical_form with
       | Some v -> Some ({ rn_num = v; rn_den = 1 })
       | None -> None)
    else if l.datatype = xsd_decimal then parse_decimal_rational l.lexical_form
    else if l.datatype = owl_rational then parse_rational_lex l.lexical_form
    else None
  | _ -> None

(* -------------------------------------------------------------------
   4c. IEEE-754 single-precision float grid (DISCRETE value space).

   xsd:float's value space is the finite IEEE-754 single grid, NOT the
   real line: between two ADJACENT floats lies no representable value.
   So an OPEN interval (minExclusive a, maxExclusive b) whose endpoints
   are adjacent floats is EMPTY, though the same open interval over the
   reals is not (Datatype-Float-Discrete-001: (0, 2^-149) is empty in
   float — 2^-149 is the smallest positive subnormal, ordinal 1, and 0.0
   is ordinal 0).

   We coordinatise the grid by ORDINAL (the value's rank in the sorted
   grid): 0.0 = 0, the k-th positive subnormal = k for 1 <= k <= 2^23-1
   (subnormals are spaced exactly 2^-149 apart). Two floats are adjacent
   iff their ordinals differ by 1, so emptiness reduces to the EXISTING
   discrete `interval_empty` rule applied to an ordinal-valued interval.

   `float_ordinal_of_lexical` is sound-partial: it returns the ordinal
   ONLY for 0.0 and the subnormal band [1, 2^23-1], and ONLY when the
   parsed exact rational lies STRICTLY inside that ordinal's round-to-
   nearest interval ((2k-1)/2^150, (2k+1)/2^150). Ties, negatives,
   normals, and anything it cannot place -> None, and the caller DROPS
   the bound (widening the interval -> withholding the emptiness verdict).
   Withholding is always sound; manufacturing emptiness is not.
   ------------------------------------------------------------------- *)

// Subnormal-grid ordinal of a single-precision float lexical form. See
// the section banner for the soundness contract (partial by design).
let float_ordinal_of_lexical (lex : string) : option int =
  match parse_decimal_rational lex with
  | None -> None
  | Some r ->
    if r.rn_num = 0 then Some 0
    else if r.rn_num < 0 then None
    else
      // r = num/den, both > 0. k = round(num*2^149 / den); accept only
      // when (2k-1)*den < num*2^150 < (2k+1)*den and 1 <= k <= 2^23-1.
      let n150 = op_Multiply r.rn_num (pow2i 150) in
      let den : pos = r.rn_den in
      let twoden : pos = op_Multiply 2 den in
      let k = (n150 + den) / twoden in
      if k >= 1 && k <= (pow2i 23) - 1
         && op_Multiply (op_Multiply 2 k - 1) den < n150
         && n150 < op_Multiply (op_Multiply 2 k + 1) den
      then Some k else None

// Fold min/max Inclusive/Exclusive facets into an ORDINAL interval, the
// float analogue of facets_to_interval. A facet value whose ordinal is
// unknown (None) is DROPPED (sound narrowing — see banner).
let rec float_facets_to_ordinal_interval (facets : list (wf_iri & rdf_term)) (acc : interval)
  : Tot interval (decreases facets) =
  match facets with
  | [] -> acc
  | (firi, fval) :: tl ->
    let acc' =
      match fval with
      | T_Literal l ->
        (match float_ordinal_of_lexical l.lexical_form with
         | None -> acc
         | Some v ->
           if firi = facet_min_incl_iri then interval_intersect acc { iv_lo = B_Incl v; iv_hi = B_Unbounded }
           else if firi = facet_max_incl_iri then interval_intersect acc { iv_lo = B_Unbounded; iv_hi = B_Incl v }
           else if firi = facet_min_excl_iri then interval_intersect acc { iv_lo = B_Excl v; iv_hi = B_Unbounded }
           else if firi = facet_max_excl_iri then interval_intersect acc { iv_lo = B_Unbounded; iv_hi = B_Excl v }
           else acc)
      | _ -> acc
    in float_facets_to_ordinal_interval tl acc'

// Is a DatatypeRestriction over xsd:float PROVABLY empty on the float
// grid? True only when the ordinal interval is empty by the DISCRETE rule
// (interval_empty) — i.e. the representable endpoints are adjacent or
// crossed, so no float satisfies. Sound: unknown ordinals widen the
// interval, so `interval_empty` never fires on a doubt.
let float_restriction_provably_empty (dt : wf_iri) (facets : list (wf_iri & rdf_term)) : bool =
  is_float_datatype dt
  && interval_empty (float_facets_to_ordinal_interval facets full_interval)

(* -------------------------------------------------------------------
   4d. The three IEEE SPECIAL values, modelled explicitly.

   XSD 1.1 Datatypes, section 3.3.5 (xsd:float) / 3.3.6 (xsd:double):
   each value space is "the set of values ... together with the three
   special values positive infinity, negative infinity and not-a-number",
   with the canonical lexical forms "INF", "-INF" and "NaN". They are the
   only members of those value spaces that no decimal lexical form
   denotes, so `parse_decimal_rational` returns None on them and the
   float-grid ordinal map of section 4c refuses them — CORRECT but
   silent. Naming them here makes the reason explicit and gives the
   owl:real membership test below something to point at: an infinity is
   not a real number, so no owl:real constraint can ever admit one.

   This is what the W3C DL InconsistencyTest "Minus Infinity is not in
   owl:real" turns on:
     SubClassOf(:A DataAllValuesFrom(:dp owl:real))
     SubClassOf(:A DataSomeValuesFrom(:dp
                     DataOneOf("-INF"^^xsd:float "-0"^^xsd:integer)))
   The forced :dp-filler must lie in {-INF, 0} INTERSECT owl:real = {0}.
   ------------------------------------------------------------------- *)

noeq type float_special =
  | FSpec_PosInf : float_special
  | FSpec_NegInf : float_special
  | FSpec_NaN    : float_special

// The canonical XSD lexical forms of the three specials, plus the
// "+INF" variant XSD 1.1 admits in the lexical space of xsd:float and
// xsd:double (it maps to positive infinity, canonical form "INF").
let float_special_of_lexical (lex : string) : option float_special =
  if lex = "INF" || lex = "+INF" then Some FSpec_PosInf
  else if lex = "-INF" then Some FSpec_NegInf
  else if lex = "NaN" then Some FSpec_NaN
  else None

let is_floating_point_datatype (dt : wf_iri) : bool =
  dt = xsd_float || dt = xsd_double

let term_float_special (t : rdf_term) : option float_special =
  match t with
  | T_Literal l ->
    if is_floating_point_datatype l.datatype
    then float_special_of_lexical l.lexical_form else None
  | _ -> None

(* THREE-VALUED membership of a term in the owl:real value space — the
   "membership of a parsed literal" primitive of this decision procedure.
     Some true  : PROVABLY a real number. The integer family, xsd:decimal,
                  owl:rational, owl:real: OWL 2 Syntax section 4.1 nests
                  their value spaces inside the reals, and each lexical
                  map here is exact (`term_exact_rational`).
     Some false : PROVABLY NOT a real number. Every xsd:float / xsd:double
                  value (finite grid point OR special — section 4.1: "the
                  value space of owl:real is defined as being disjoint
                  with the value spaces of xsd:double and xsd:float"), and
                  every string / boolean value (disjoint value spaces,
                  XSD 1.1 section 3).
     None       : unknown datatype — WITHHELD. Sound in both directions:
                  no caller may turn "not proved in" into "proved out". *)
let term_in_owl_real (t : rdf_term) : option bool =
  match t with
  | T_Literal l ->
    (match classify_family l.datatype with
     | Some Fam_Numeric -> Some true
     | Some _ -> Some false
     | None -> None)
  | _ -> None

(* -------------------------------------------------------------------
   4e. DENSE numeric intervals with EXACT RATIONAL endpoints.

   Section 3's `interval` carries `int` endpoints and INTEGER
   granularity: `interval_empty` treats `(lo, hi)` as empty once the two
   are adjacent, and `interval_count` counts its members. Both are wrong
   for xsd:decimal / owl:rational / owl:real, whose value spaces are
   dense: (0, 1) holds no integer but infinitely many decimals.

   So the dense spaces get their own normalised representation — same
   bound algebra, endpoints drawn from the exact `rational` type of
   section 4b (so "0.1"^^xsd:decimal is an endpoint with no rounding),
   and a dense emptiness rule. The bridge to the integer representation
   is `qinterval_to_int_interval`, which ceils the lower bound and floors
   the upper: exactly the integers a dense interval contains.
   ------------------------------------------------------------------- *)

// a <= b and a < b for exact rationals. Both denominators are `pos`, so
// cross-multiplication is order-preserving and needs no case split.
let rational_le (a b : rational) : bool =
  op_Multiply a.rn_num b.rn_den <= op_Multiply b.rn_num a.rn_den

let rational_lt (a b : rational) : bool =
  op_Multiply a.rn_num b.rn_den < op_Multiply b.rn_num a.rn_den

noeq type qbound =
  | QB_Unbounded : qbound
  | QB_Incl : rational -> qbound
  | QB_Excl : rational -> qbound

noeq type qinterval = { qv_lo : qbound; qv_hi : qbound }

let full_qinterval : qinterval = { qv_lo = QB_Unbounded; qv_hi = QB_Unbounded }

let rational_in_qinterval (v : rational) (iv : qinterval) : bool =
  (match iv.qv_lo with
   | QB_Unbounded -> true | QB_Incl lo -> rational_le lo v | QB_Excl lo -> rational_lt lo v) &&
  (match iv.qv_hi with
   | QB_Unbounded -> true | QB_Incl hi -> rational_le v hi | QB_Excl hi -> rational_lt v hi)

let qtighter_lo (a b : qbound) : qbound =
  match a, b with
  | QB_Unbounded, _ -> b
  | _, QB_Unbounded -> a
  | QB_Incl x, QB_Incl y -> if rational_le y x then a else b
  | QB_Excl x, QB_Excl y -> if rational_le y x then a else b
  | QB_Incl x, QB_Excl y -> if rational_lt y x then a else b
  | QB_Excl x, QB_Incl y -> if rational_le y x then a else b

let qtighter_hi (a b : qbound) : qbound =
  match a, b with
  | QB_Unbounded, _ -> b
  | _, QB_Unbounded -> a
  | QB_Incl x, QB_Incl y -> if rational_le x y then a else b
  | QB_Excl x, QB_Excl y -> if rational_le x y then a else b
  | QB_Incl x, QB_Excl y -> if rational_lt x y then a else b
  | QB_Excl x, QB_Incl y -> if rational_le x y then a else b

let qinterval_intersect (a b : qinterval) : qinterval =
  { qv_lo = qtighter_lo a.qv_lo b.qv_lo; qv_hi = qtighter_hi a.qv_hi b.qv_hi }

// PROVABLY empty over a DENSE order: the endpoints cross, or coincide
// with at least one end open. Adjacency is meaningless here — between
// any two distinct reals lies a third.
let qinterval_empty (iv : qinterval) : bool =
  match iv.qv_lo, iv.qv_hi with
  | QB_Incl lo, QB_Incl hi -> rational_lt hi lo
  | QB_Incl lo, QB_Excl hi -> rational_le hi lo
  | QB_Excl lo, QB_Incl hi -> rational_le hi lo
  | QB_Excl lo, QB_Excl hi -> rational_le hi lo
  | _, _ -> false

// floor / ceil of an exact rational. Written so the answer does not
// depend on whether integer division truncates toward zero or toward
// minus infinity: take the quotient, then correct by one step if the
// product misses on the wrong side.
let rational_floor (r : rational) : int =
  let q = r.rn_num / r.rn_den in
  if op_Multiply q r.rn_den > r.rn_num then q - 1 else q

let rational_ceil (r : rational) : int =
  let q = r.rn_num / r.rn_den in
  if op_Multiply q r.rn_den < r.rn_num then q + 1 else q

let rational_is_integer (r : rational) : bool =
  op_Multiply (rational_floor r) r.rn_den = r.rn_num

// The INTEGERS a dense interval contains, as an integer-granularity
// interval: ceil the lower bound, floor the upper, and step one past an
// integral endpoint that is EXCLUDED.
let qbound_to_int_lo (b : qbound) : bound =
  match b with
  | QB_Unbounded -> B_Unbounded
  | QB_Incl r -> B_Incl (rational_ceil r)
  | QB_Excl r -> B_Incl (if rational_is_integer r then rational_floor r + 1 else rational_ceil r)

let qbound_to_int_hi (b : qbound) : bound =
  match b with
  | QB_Unbounded -> B_Unbounded
  | QB_Incl r -> B_Incl (rational_floor r)
  | QB_Excl r -> B_Incl (if rational_is_integer r then rational_ceil r - 1 else rational_floor r)

let qinterval_to_int_interval (iv : qinterval) : interval =
  { iv_lo = qbound_to_int_lo iv.qv_lo; iv_hi = qbound_to_int_hi iv.qv_hi }

(* min/max Inclusive/Exclusive facets over a DENSE numeric base datatype,
   folded into a rational-endpoint interval. A facet value that is not an
   EXACT point on the owl:real line (`term_exact_rational` = None — a
   float, a string, an unparseable lexical form) is DROPPED, which widens
   the interval: sound narrowing, exactly as `facets_to_interval` does. *)
let rec dense_facets_to_qinterval (facets : list (wf_iri & rdf_term)) (acc : qinterval)
  : Tot qinterval (decreases facets) =
  match facets with
  | [] -> acc
  | (firi, fval) :: tl ->
    let acc' =
      match term_exact_rational fval with
      | None -> acc
      | Some v ->
        if firi = facet_min_incl_iri then qinterval_intersect acc { qv_lo = QB_Incl v; qv_hi = QB_Unbounded }
        else if firi = facet_max_incl_iri then qinterval_intersect acc { qv_lo = QB_Unbounded; qv_hi = QB_Incl v }
        else if firi = facet_min_excl_iri then qinterval_intersect acc { qv_lo = QB_Excl v; qv_hi = QB_Unbounded }
        else if firi = facet_max_excl_iri then qinterval_intersect acc { qv_lo = QB_Unbounded; qv_hi = QB_Excl v }
        else acc
    in
    dense_facets_to_qinterval tl acc'

(* -------------------------------------------------------------------
   5. Value sets: the combined shape a facet checker needs — an
      interval, a finite literal enumeration (DataOneOf), a bare
      base-datatype family, unconstrained (top), or empty (bottom).
   ------------------------------------------------------------------- *)

noeq type value_set =
  | VS_Unconstrained : value_set
  | VS_Interval : interval -> value_set
  (* VS_Dense: a DENSE stretch of the owl:real number line (owl:real /
     owl:rational / xsd:decimal). Distinct from VS_Interval because the
     granularity changes both rules that matter — emptiness (adjacency
     empties an integer open interval, never a dense one) and counting
     (an integer interval with finite ends has an exact finite size; a
     non-empty dense one is infinite). *)
  | VS_Dense : qinterval -> value_set
  | VS_DateInterval : interval -> value_set
  | VS_Enum : list rdf_term -> value_set
  | VS_Family : xsd_family -> value_set
  | VS_Empty : value_set

let term_int_opt (t : rdf_term) : option int =
  match t with T_Literal l -> literal_int_value l | _ -> None

let term_family (t : rdf_term) : option xsd_family =
  match t with T_Literal l -> classify_family l.datatype | _ -> None

let term_bool_opt (t : rdf_term) : option bool =
  match t with
  | T_Literal l ->
    if l.datatype = xsd_boolean then
      (if l.lexical_form = "true" || l.lexical_form = "1" then Some true
       else if l.lexical_form = "false" || l.lexical_form = "0" then Some false
       else None)
    else None
  | _ -> None

(* THREE-VALUED value comparison — the load-bearing soundness choice of
   this module. The empty-intersection verdict feeds a CLASH (refutes
   the whole ontology), so an enum element may be DISCARDED from an
   intersection only when it is PROVABLY not in the other operand, and
   removed by a complement only when it PROVABLY equals a removed
   value. "Failed to prove equal" is NOT "provably distinct": a decimal
   "3.0" and an integer "3" denote the SAME value in OWL 2's unified
   numeric value space even though no rule below can prove it — such
   pairs must answer false to BOTH predicates (unknown), keeping the
   element and thereby withholding the clash. Withholding is always
   sound; manufacturing emptiness is not.

   provably EQUAL when:
     - identical term (same lexical form + datatype denotes one value
       for every datatype, plus IRI/bnode identity); or
     - both parse as integer-family values and the values agree
       (promotes across integer subtypes — "2"^^xsd:short =
       "2"^^xsd:integer, the anti-pattern-#6 promoted-type gap); or
     - both are boolean and their normalised values agree ("1" = "true").
   provably DISTINCT when:
     - both parse as integer-family values and the values differ; or
     - both classify into DIFFERENT base families (numeric / string /
       boolean value spaces are pairwise disjoint, XSD Part 2 §3 + the
       OWL 2 datatype map); or
     - both are xsd:string with different lexical forms (a string's
       value IS its lexical form); or
     - both are boolean with different normalised values.
   Everything else (decimal-vs-integer, rational, float, unrecognised
   datatypes): both predicates false — unknown. *)
let term_provably_equal (a b : rdf_term) : bool =
  rdf_term_eq a b
  || (match term_int_opt a, term_int_opt b with
      | Some x, Some y -> x = y
      | _, _ ->
        (match term_bool_opt a, term_bool_opt b with
         | Some x, Some y -> x = y
         | _, _ -> false))
  (* Exact-rational equality across the owl:real line: "0.5"^^xsd:decimal
     and "1/2"^^owl:rational denote the SAME real (owl:decimal ⊂
     owl:rational ⊂ owl:real, both maps exact) — provably equal, so a
     DataOneOf enumerating them holds ONE value, not two (New-Feature-
     Rational-002). Sound: rational_eq is true only for genuinely equal
     reals, so no distinct pair is ever falsely merged. *)
  || (match term_exact_rational a, term_exact_rational b with
      | Some x, Some y -> rational_eq x y
      | _, _ -> false)

let both_string (a b : rdf_term) : bool =
  match a, b with
  | T_Literal la, T_Literal lb -> la.datatype = xsd_string && lb.datatype = xsd_string
  | _, _ -> false

let string_lex_neq (a b : rdf_term) : bool =
  match a, b with
  | T_Literal la, T_Literal lb -> la.lexical_form <> lb.lexical_form
  | _, _ -> false

let term_provably_distinct (a b : rdf_term) : bool =
  (match term_int_opt a, term_int_opt b with
   | Some x, Some y -> x <> y
   | _, _ -> false)
  || (match term_family a, term_family b with
      | Some fa, Some fb -> not (xsd_family_eq fa fb)
      | _, _ -> false)
  || (both_string a b && string_lex_neq a b)
  || (match term_bool_opt a, term_bool_opt b with
      | Some x, Some y -> x <> y
      | _, _ -> false)

let rec all_literal_terms (ts : list rdf_term) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | T_Literal _ :: tl -> all_literal_terms tl
  | _ -> false

let rec filter_enum_by (f : rdf_term -> bool) (xs : list rdf_term)
  : Tot (list rdf_term) (decreases xs) =
  match xs with
  | [] -> []
  | h :: tl -> if f h then h :: filter_enum_by f tl else filter_enum_by f tl

(* Keep h ∈ xs unless h is provably distinct from EVERY y ∈ ys — i.e.
   drop only on a PROOF of absence from the other operand. *)
let rec enum_intersect (xs ys : list rdf_term) : Tot (list rdf_term) (decreases xs) =
  match xs with
  | [] -> []
  | h :: tl ->
    if List.Tot.for_all (term_provably_distinct h) ys
    then enum_intersect tl ys
    else h :: enum_intersect tl ys

(* Drop h from an integer-interval intersection only when PROVABLY
   outside: either h parses as an integer-family value that misses the
   interval, or h's base family is provably non-numeric (string/boolean
   value spaces are disjoint from every numeric interval). A decimal or
   unrecognised-datatype literal is KEPT (its value might lie in the
   interval — e.g. "5.0"^^xsd:decimal in [4,10]). *)
let provably_outside_interval (iv : interval) (t : rdf_term) : bool =
  (match term_int_opt t with
   | Some v -> not (value_in_interval v iv)
   | None -> false)
  || (match term_family t with
      | Some f -> not (xsd_family_eq f Fam_Numeric)
      | None -> false)

(* Drop h from a family intersection only when h PROVABLY classifies
   into a different family; unclassifiable datatypes are kept. *)
let provably_outside_family (f : xsd_family) (t : rdf_term) : bool =
  match term_family t with
  | Some g -> not (xsd_family_eq f g)
  | None -> false

(* Drop h from a dateTime-interval intersection only when PROVABLY
   outside: either h is a timezoned dateTime whose UTC instant misses
   the interval, or h is a literal of a recognised NON-dateTime base
   family (numeric / string / boolean — `term_family` = Some, and the
   xsd:dateTime value space is disjoint from all three, XSD Part 2 §3).
   A timezone-less dateTime (`term_datetime_key` = None yet dateTime-
   typed, so `term_family` = None) is KEPT — its instant is only
   partially ordered w.r.t. the timezoned bounds, so it might lie
   inside; withholding the clash is sound. *)
let provably_outside_date_interval (iv : interval) (t : rdf_term) : bool =
  (match term_datetime_key t with
   | Some v -> not (value_in_interval v iv)
   | None -> false)
  || Some? (term_family t)

(* Drop h from a DENSE numeric intersection only when PROVABLY outside:
   either h is an exact point on the owl:real line that misses the
   interval, or h's value space is PROVABLY not the real line at all
   (string / boolean / float / double — OWL 2 Syntax section 4.1). A
   literal of an unrecognised datatype is KEPT. *)
let provably_outside_dense (iv : qinterval) (t : rdf_term) : bool =
  (match term_exact_rational t with
   | Some q -> not (rational_in_qinterval q iv)
   | None -> false)
  || (match term_family t with
      | Some f -> not (xsd_family_eq f Fam_Numeric)
      | None -> false)

let value_set_intersect (a b : value_set) : value_set =
  match a, b with
  | VS_Empty, _ -> VS_Empty
  | _, VS_Empty -> VS_Empty
  | VS_Unconstrained, x -> x
  | x, VS_Unconstrained -> x
  | VS_Dense qa, VS_Dense qb ->
    let qi = qinterval_intersect qa qb in
    if qinterval_empty qi then VS_Empty else VS_Dense qi
  (* Integers are reals: a dense stretch meeting an integer-granularity
     interval leaves exactly the integers inside both, which is again an
     integer-granularity interval (discrete emptiness applies). *)
  | VS_Dense qa, VS_Interval ib ->
    let ii = interval_intersect (qinterval_to_int_interval qa) ib in
    if interval_empty ii then VS_Empty else VS_Interval ii
  | VS_Interval ia, VS_Dense qb ->
    let ii = interval_intersect ia (qinterval_to_int_interval qb) in
    if interval_empty ii then VS_Empty else VS_Interval ii
  | VS_Dense qa, VS_Enum xs ->
    let e = filter_enum_by (fun t -> not (provably_outside_dense qa t)) xs in
    if Nil? e then VS_Empty else VS_Enum e
  | VS_Enum xs, VS_Dense qb ->
    let e = filter_enum_by (fun t -> not (provably_outside_dense qb t)) xs in
    if Nil? e then VS_Empty else VS_Enum e
  (* The owl:real line is disjoint from the string / boolean / float /
     double value spaces, and from xsd:dateTime. *)
  | VS_Dense qa, VS_Family f -> if xsd_family_eq f Fam_Numeric then VS_Dense qa else VS_Empty
  | VS_Family f, VS_Dense qb -> if xsd_family_eq f Fam_Numeric then VS_Dense qb else VS_Empty
  | VS_Dense _, VS_DateInterval _ -> VS_Empty
  | VS_DateInterval _, VS_Dense _ -> VS_Empty
  | VS_Interval ia, VS_Interval ib ->
    let ii = interval_intersect ia ib in
    if interval_empty ii then VS_Empty else VS_Interval ii
  | VS_DateInterval ia, VS_DateInterval ib ->
    let ii = interval_intersect ia ib in
    if interval_empty_dense ii then VS_Empty else VS_DateInterval ii
  (* dateTime value space is disjoint from every integer/decimal (numeric
     family) value space, so a dateTime interval meeting an integer
     interval or any base family is EMPTY (a value cannot be both). *)
  | VS_DateInterval _, VS_Interval _ -> VS_Empty
  | VS_Interval _, VS_DateInterval _ -> VS_Empty
  | VS_DateInterval _, VS_Family _ -> VS_Empty
  | VS_Family _, VS_DateInterval _ -> VS_Empty
  | VS_DateInterval iv, VS_Enum xs ->
    let e = filter_enum_by (fun t -> not (provably_outside_date_interval iv t)) xs in
    if Nil? e then VS_Empty else VS_Enum e
  | VS_Enum xs, VS_DateInterval iv ->
    let e = filter_enum_by (fun t -> not (provably_outside_date_interval iv t)) xs in
    if Nil? e then VS_Empty else VS_Enum e
  | VS_Enum xs, VS_Enum ys ->
    let e = enum_intersect xs ys in
    if Nil? e then VS_Empty else VS_Enum e
  | VS_Enum xs, VS_Interval iv ->
    let e = filter_enum_by (fun t -> not (provably_outside_interval iv t)) xs in
    if Nil? e then VS_Empty else VS_Enum e
  | VS_Interval iv, VS_Enum xs ->
    let e = filter_enum_by (fun t -> not (provably_outside_interval iv t)) xs in
    if Nil? e then VS_Empty else VS_Enum e
  | VS_Enum xs, VS_Family f ->
    let e = filter_enum_by (fun t -> not (provably_outside_family f t)) xs in
    if Nil? e then VS_Empty else VS_Enum e
  | VS_Family f, VS_Enum xs ->
    let e = filter_enum_by (fun t -> not (provably_outside_family f t)) xs in
    if Nil? e then VS_Empty else VS_Enum e
  | VS_Interval iv, VS_Family f ->
    (* Every interval this module builds is over an integer-family base
       datatype (facets_to_interval / base_interval_for guard on it),
       so its value space is numeric: disjoint from string/boolean. *)
    if xsd_family_eq f Fam_Numeric then VS_Interval iv else VS_Empty
  | VS_Family f, VS_Interval iv ->
    if xsd_family_eq f Fam_Numeric then VS_Interval iv else VS_Empty
  | VS_Family fa, VS_Family fb ->
    if xsd_family_eq fa fb then VS_Family fa else VS_Empty

let value_set_is_empty (v : value_set) : bool =
  match v with
  | VS_Empty -> true
  | VS_Enum [] -> true
  (* A bare dateTime restriction whose own facets already cross (e.g. a
     single DataSomeValuesFrom with contradictory min/max on dateTime —
     case (b) of the Wave B clash rules) is empty before any second
     restriction intersects it. Dense emptiness, per interval_empty_dense. *)
  | VS_DateInterval iv -> interval_empty_dense iv
  (* Same reason on the owl:real line: a DatatypeRestriction whose own
     min/max facets already cross is empty before anything intersects
     it. Dense rule — adjacency does not empty a real interval. *)
  | VS_Dense qi -> qinterval_empty qi
  | _ -> false

(* -------------------------------------------------------------------
   5b. Value-space cardinality: a SOUND UPPER BOUND on the number of
       distinct values a value_set admits.

   Feeds the datatype cardinality clash (Tableau.Refute): a min/exact
   cardinality k on a datatype property whose fillers are all confined to
   a value space of provable size < k is UNSATISFIABLE (k distinct data
   values cannot be drawn from fewer than k). Soundness DIRECTION: the
   returned M must be >= the true number of distinct values, so that
   `k > M` implies `k > |value space|` (never the reverse) — an
   over-count only WITHHOLDS a clash, an under-count would MANUFACTURE
   one. Every branch below returns a sound over-approximation:
     - integer interval: EXACT count (discrete, both ends finite);
     - enum: distinct count after collapsing ONLY provably-equal members
       (unproven-equal pairs stay separate -> count can only be too high);
     - dense/unbounded/unknown (decimal, dateTime, family, ⊤): None (no
       finite bound — a min-cardinality on a dense domain is satisfiable,
       the Wave B dense-domain lesson).
   ------------------------------------------------------------------- *)

let bound_lo_incl (b : bound) : option int =
  match b with B_Unbounded -> None | B_Incl x -> Some x | B_Excl x -> Some (x + 1)

let bound_hi_incl (b : bound) : option int =
  match b with B_Unbounded -> None | B_Incl x -> Some x | B_Excl x -> Some (x - 1)

// Number of integers in a discrete interval, when both ends are finite;
// None when either end is unbounded (an infinite integer value space).
let interval_count (iv : interval) : option nat =
  match bound_lo_incl iv.iv_lo, bound_hi_incl iv.iv_hi with
  | Some lo, Some hi -> if hi >= lo then Some (hi - lo + 1) else Some 0
  | _, _ -> None

// Drop every member provably equal to h (length-bounded for termination).
let rec drop_provably_equal (h : rdf_term) (xs : list rdf_term)
  : Tot (r : list rdf_term { List.Tot.length r <= List.Tot.length xs }) (decreases xs) =
  match xs with
  | [] -> []
  | x :: tl ->
    let rest = drop_provably_equal h tl in
    if term_provably_equal h x then rest else x :: rest

// Distinct-value count of a literal enum, collapsing ONLY provably-equal
// members: a sound UPPER bound on the true number of distinct values.
let rec enum_distinct_count (xs : list rdf_term) : Tot nat (decreases (List.Tot.length xs)) =
  match xs with
  | [] -> 0
  | h :: tl -> 1 + enum_distinct_count (drop_provably_equal h tl)

let value_set_max_size (v : value_set) : option nat =
  match v with
  | VS_Empty -> Some 0
  | VS_Enum [] -> Some 0
  | VS_Enum xs -> Some (enum_distinct_count xs)
  | VS_Interval iv -> interval_count iv
  | VS_DateInterval iv -> if interval_empty_dense iv then Some 0 else None
  (* A non-empty stretch of the owl:real line holds infinitely many
     values, so no finite bound — the dense-domain lesson again. *)
  | VS_Dense qi -> if qinterval_empty qi then Some 0 else None
  | VS_Unconstrained -> None
  | VS_Family _ -> None

(* Subtract `remove` from `acc` — used for DataComplementOf. Only the
   Enum/Enum shape is representable exactly (removing a finite literal
   set from a finite literal set); every other combination is a sound
   no-op (an interval minus a set is not representable as one interval
   in general, and none of the Wave-B target fixtures need it — every
   DataComplementOf in the corpus wraps a DataOneOf). An element is
   removed only when PROVABLY equal to a removed value — over-removal
   would manufacture emptiness (see the term_provably_equal banner). *)
let value_set_subtract (acc : value_set) (remove : value_set) : value_set =
  match acc, remove with
  | VS_Enum xs, VS_Enum ys ->
    let e = filter_enum_by (fun t -> not (List.Tot.existsb (term_provably_equal t) ys)) xs in
    if Nil? e then VS_Empty else VS_Enum e
  | _, _ -> acc

(* -------------------------------------------------------------------
   5c. EXACT ENUMERATION of a finite value space.

   `value_set_max_size` above answers "how many values AT MOST?" — the
   number only. This answers "WHICH values?", and it is what turns a
   value-space computation into an ENTAILMENT rather than a refutation:
   when an ontology forces k pairwise-distinct fillers into a value space
   with exactly k members, every one of those members IS a filler.

   CONTRACT of the returned list L, for a value_set standing for the true
   admissible set A:
     (1) COVER   — A subset-of set(L). L never misses an admissible value.
     (2) DISTINCT — L's members are pairwise distinct BY VALUE, so
                    |set(L)| = length L exactly (no double count).
   Consumers get two sound readings from (1) + (2):
     (a) if every member of L is excluded, then A is empty (refutation);
     (b) if some axiom forces >= length L pairwise-distinct members of A,
         then A = set(L) and every member of L is realised (entailment) —
         |A| >= length L = |set(L)| >= |A| forces equality. Note this
         holds even when L OVER-approximates A, which is why (1) is a
         one-sided cover and not an equality.

   Shapes that qualify:
     - VS_Empty            : the empty list.
     - VS_Interval iv      : both ends finite -> the integers in [lo, hi],
                             written in the canonical xsd:integer lexical
                             form. Exact and pairwise distinct.
     - VS_Enum xs          : only when the members are PAIRWISE PROVABLY
                             DISTINCT, so (2) holds. An enum with an
                             unproven-equal pair (a decimal and a rational
                             that might denote one value) answers None.
   Everything else answers None: dense, dateTime, bare family and
   unconstrained spaces are infinite, and withholding is always sound.
   ------------------------------------------------------------------- *)

(* Materialisation cap. Above it the answer is None and every consumer
   withholds — sound, and it bounds the work a pathological facet range
   (say xsd:int with no facets, 2^32 values) can ask for. 4096 covers
   every finite XSD integer subtype the corpus enumerates (the largest is
   xsd:unsignedByte / xsd:byte at 256, and the byte-INTERSECT-unsignedInt
   window of WebOnt-I5.8-004 at 128). *)
let exact_enum_cap : nat = 4096

// An integer as a canonical xsd:integer literal term. Well-formed by
// construction: no language tag and no direction, and xsd:integer is
// neither rdf:langString nor rdf:dirLangString.
let int_literal_term (n : int) : rdf_term =
  let l : literal = { lexical_form = string_of_int n; datatype = xsd_integer;
                      lang_tag = None; direction = None } in
  assert_norm (xsd_integer <> rdf_lang_string);
  assert_norm (xsd_integer <> rdf_dir_lang_string);
  assert (literal_wf l);
  T_Literal l

// The integers lo, lo+1, ..., lo+n-1 as canonical xsd:integer literals.
let rec int_range_literals (lo : int) (n : nat) : Tot (list rdf_term) (decreases n) =
  if n = 0 then []
  else int_literal_term lo :: int_range_literals (lo + 1) (n - 1)

let rec pairwise_provably_distinct (xs : list rdf_term) : Tot bool (decreases xs) =
  match xs with
  | [] -> true
  | h :: tl -> List.Tot.for_all (term_provably_distinct h) tl && pairwise_provably_distinct tl

(* The xsd:boolean value space, in canonical lexical form. XSD 1.1
   Datatypes section 3.3.2 gives it as the two-element set {true, false}
   — the only FINITE value space in the OWL 2 datatype map that is not a
   numeric interval. Naming it lets `value_set_exact_values` treat a bare
   `xsd:boolean` filler the way it already treats `xsd:byte`: a finite
   space whose members can be listed. `term_provably_equal` / `_distinct`
   already fold the "1"/"0" lexical variants onto these two values, so
   the pair is pairwise distinct and covers the space, as the COVER +
   DISTINCT contract requires. *)
let bool_literal_term (b : bool) : rdf_term =
  let l : literal = { lexical_form = (if b then "true" else "false"); datatype = xsd_boolean;
                      lang_tag = None; direction = None } in
  assert_norm (xsd_boolean <> rdf_lang_string);
  assert_norm (xsd_boolean <> rdf_dir_lang_string);
  assert (literal_wf l);
  T_Literal l

let xsd_boolean_value_space : list rdf_term =
  [bool_literal_term false; bool_literal_term true]

let value_set_exact_values (v : value_set) : option (list rdf_term) =
  match v with
  | VS_Empty -> Some []
  | VS_Enum xs -> if pairwise_provably_distinct xs then Some xs else None
  // A bare xsd:boolean constraint IS a finite value space, not an
  // unbounded family: exactly two values. Every other family
  // (numeric / string / float / double) is infinite -> None below.
  | VS_Family Fam_Boolean -> Some xsd_boolean_value_space
  | VS_Interval iv ->
    (match interval_count iv with
     | None -> None
     | Some n ->
       if n > exact_enum_cap then None
       else
         (match bound_lo_incl iv.iv_lo with
          | Some lo -> Some (int_range_literals lo n)
          | None -> if n = 0 then Some [] else None))
  | _ -> None

(* -------------------------------------------------------------------
   5d. Removing values an axiom FORBIDS.

   `negs` is the list of data values some axiom asserts are NOT fillers
   of the property this value_set constrains — the targets of the
   NegativeDataPropertyAssertions on that property (OWL 2 Syntax
   section 9.6.6: NegativeDataPropertyAssertion(DP a lt) is satisfied iff
   the pair is NOT in the property's extension). Removing them turns a
   forced-witness obligation into a clash whenever nothing survives.

   A value is removed only when PROVABLY equal to a forbidden one — the
   same one-sided discipline as `value_set_subtract`; over-removal would
   manufacture emptiness. Only the two shapes with a COVER (section 5c)
   can shrink to empty:
     - VS_Enum: its members cover the admissible set, so if every one is
       forbidden the admissible set is empty.
     - VS_Interval: same, via its exact enumeration; guarded on
       `count <= length negs` so a 4096-value interval is not enumerated
       against a two-element negation list that cannot possibly cover it.
   Dense, dateTime, family and unconstrained spaces are infinite: minus a
   finite set of points they stay non-empty, so they are left alone. *)
let remove_negated_values (negs : list rdf_term) (v : value_set) : value_set =
  if Nil? negs then v
  else
    match v with
    | VS_Enum xs ->
      let e = filter_enum_by (fun t -> not (List.Tot.existsb (term_provably_equal t) negs)) xs in
      if Nil? e then VS_Empty else VS_Enum e
    | VS_Interval iv ->
      (match interval_count iv with
       | Some n ->
         if n <= List.Tot.length negs then
           (match value_set_exact_values v with
            | Some vs ->
              if List.Tot.for_all
                   (fun (t : rdf_term) -> List.Tot.existsb (term_provably_equal t) negs) vs
              then VS_Empty else v
            | None -> v)
         else v
       | None -> v)
    | _ -> v
