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
noeq type xsd_family =
  | Fam_Numeric : xsd_family
  | Fam_String  : xsd_family
  | Fam_Boolean : xsd_family

let xsd_family_eq (a b : xsd_family) : bool =
  match a, b with
  | Fam_Numeric, Fam_Numeric -> true
  | Fam_String, Fam_String -> true
  | Fam_Boolean, Fam_Boolean -> true
  | _, _ -> false

let classify_family (dt : wf_iri) : option xsd_family =
  if is_integer_family_datatype dt || dt = xsd_decimal then Some Fam_Numeric
  else if dt = xsd_string then Some Fam_String
  else if dt = xsd_boolean then Some Fam_Boolean
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
   5. Value sets: the combined shape a facet checker needs — an
      interval, a finite literal enumeration (DataOneOf), a bare
      base-datatype family, unconstrained (top), or empty (bottom).
   ------------------------------------------------------------------- *)

noeq type value_set =
  | VS_Unconstrained : value_set
  | VS_Interval : interval -> value_set
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

let value_set_intersect (a b : value_set) : value_set =
  match a, b with
  | VS_Empty, _ -> VS_Empty
  | _, VS_Empty -> VS_Empty
  | VS_Unconstrained, x -> x
  | x, VS_Unconstrained -> x
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
  | _ -> false

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
