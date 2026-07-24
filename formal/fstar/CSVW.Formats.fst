module CSVW.Formats

// ================================================================
// CSVW UAX-35 format engines (csv2rdf §"Parsing cells",
// tabular-metadata §6.4 "Datatypes" and its "Formats for numeric
// types" / "Formats for dates and times" / "Formats for booleans"
// subsections).
//
// The CSVW spec restricts UAX-35 to a defined SUBSET. This module
// implements exactly that subset, driven by the W3C csv2rdf test
// corpus (test157-171, test183-192, test246-247, test282-304):
//
//   - NUMBER patterns: the symbols `0`, `#`, the (overridable)
//     decimalChar and groupChar, `E` (exponent), `+`/`-` sign,
//     `%` (per-cent) and U+2030 per-mille. Primary + secondary
//     grouping sizes (Indian-style `#,##,##0`), fractional grouping,
//     min integer digits, min/max fraction digits.
//   - DATE/TIME patterns: field symbols yyyy / MM / dd / HH / mm / ss
//     (+ single-letter M/d/H/m/s variable-width forms), fractional
//     seconds `S...`, timezone X / XX / XXX / x / xx / xxx, and
//     literal separators. Day/month NAMES are NOT in the subset;
//     a two-digit `yy` year is NOT supported (test191 expects a
//     `yy-MM-dd` pattern to leave the value un-parsed).
//   - BOOLEAN format: `trueValue|falseValue`, defaulting to
//     true/false/1/0 when no format is given.
//
// The three engines return a `fmt_outcome`:
//   FO_NoFormat  — this datatype has no applicable format facet;
//                  the caller keeps its existing (plain xsd-lexical)
//                  path.
//   FO_Valid lex — the cell matched the format; `lex` is the
//                  canonical xsd lexical (grouping removed, decimalChar
//                  normalised to '.', percent/permille applied, date
//                  fields reordered + zero-padded, boolean canonicalised
//                  to true/false).
//   FO_Invalid   — a format facet is present but the cell does NOT
//                  match it; per tabular-data-model §6.4.2 the cell
//                  keeps its RAW lexical as a plain string literal
//                  (test185/191/269/286-304).
//
// IRON RULES:
//   - F* is the source of truth (rule #1); extracted, never hand-
//     written OCaml (rule #2).
//   - No --lax, no --admit_smt_queries (rule #10).
//   - No "(" star or star ")" inside block comments (rule #12); use //.
// ================================================================

open FStar.List.Tot

module S = FStar.String
module C = FStar.Char

// Verified regex engine (issue #304): a duration `format` facet is a
// REGULAR EXPRESSION per tabular-metadata, not a UAX-35 field pattern.
// `Regex.XSDPattern.parse_xsd_pattern` reads the XSD-flavor pattern to
// the `Regex.Syntax` AST and `Regex.Exec.matches_norm` tests the whole
// cell against it (matches_norm is proven language-equal to the
// `Regex.Derivative` reference — matches_norm_correct).
module RXP = Regex.XSDPattern
module RXE = Regex.Exec

// ----------------------------------------------------------------
// Character helpers (all parsing is over `list C.char`).
// ----------------------------------------------------------------

let chars_of (s : string) : list C.char = S.list_of_string s
let string_of (l : list C.char) : string = S.string_of_list l

let code (c : C.char) : int = C.int_of_char c

let is_digit (c : C.char) : bool =
  let i = code c in i >= 48 && i <= 57  // '0'..'9'

let char_zero : C.char = C.char_of_int 48
let dot_char : C.char  = C.char_of_int 46  // '.'
let plus_char : C.char = C.char_of_int 43  // '+'
let minus_char : C.char = C.char_of_int 45 // '-'
let percent_char : C.char = C.char_of_int 37 // '%'
let permille_char : C.char = C.char_of_int 8240 // U+2030
let big_e_char : C.char = C.char_of_int 69 // 'E'
let cap_z_char : C.char = C.char_of_int 90 // 'Z'
let colon_char : C.char = C.char_of_int 58 // ':'
let quote_char : C.char = C.char_of_int 39 // single quote

// First char of a (possibly empty) string, as a char option.
let first_char (s : string) : option C.char =
  match chars_of s with [] -> None | c :: _ -> Some c

let rec all_digits (l : list C.char) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | c :: tl -> is_digit c && all_digits tl

let rec count_char (target : C.char) (l : list C.char) : Tot nat (decreases l) =
  match l with
  | [] -> 0
  | c :: tl -> (if code c = code target then 1 else 0) + count_char target tl

// Split a char list at the FIRST occurrence of `sep` into (before, after)
// with `sep` dropped; None if `sep` is absent.
let rec split_first (sep : C.char) (l : list C.char)
  : Tot (option (list C.char & list C.char)) (decreases l) =
  match l with
  | [] -> None
  | c :: tl ->
    if code c = code sep then Some ([], tl)
    else (match split_first sep tl with
          | None -> None
          | Some (a, b) -> Some (c :: a, b))

// Split on EVERY occurrence of `sep` into a list of segments (always
// returns at least one segment). Structural recursion on `l`.
let rec split_all (sep : C.char) (l : list C.char)
  : Tot (list (list C.char)) (decreases l) =
  match l with
  | [] -> [[]]
  | c :: tl ->
    if code c = code sep then [] :: split_all sep tl
    else (match split_all sep tl with
          | seg :: rest -> (c :: seg) :: rest
          | [] -> [[c]])

// Drop leading '0's, keeping at least one char.
let rec drop_leading_zeros (l : list C.char) : Tot (list C.char) (decreases l) =
  match l with
  | [] -> [char_zero]
  | [c] -> [c]
  | c :: tl -> if code c = 48 then drop_leading_zeros tl else c :: tl

let rec repeat_char (c : C.char) (n : nat) : Tot (list C.char) (decreases n) =
  if n = 0 then [] else c :: repeat_char c (n - 1)

// ----------------------------------------------------------------
// Outcome type + numeric base classification.
// ----------------------------------------------------------------

type fmt_outcome =
  | FO_NoFormat : fmt_outcome
  | FO_Valid    : string -> fmt_outcome
  | FO_Invalid  : fmt_outcome

let is_integer_base (n : string) : bool =
  n = "integer" || n = "long" || n = "int" || n = "short" || n = "byte" ||
  n = "nonNegativeInteger" || n = "positiveInteger" || n = "nonPositiveInteger" ||
  n = "negativeInteger" || n = "unsignedLong" || n = "unsignedInt" ||
  n = "unsignedShort" || n = "unsignedByte"

let is_double_base (n : string) : bool =
  n = "double" || n = "float" || n = "number"

let is_decimal_base (n : string) : bool =
  n = "decimal"

let is_numeric_base (n : string) : bool =
  is_integer_base n || is_double_base n || is_decimal_base n

let is_date_base (n : string) : bool =
  n = "date" || n = "time" || n = "dateTime" || n = "dateTimeStamp" ||
  n = "datetime"

// ----------------------------------------------------------------
// NUMBER format engine.
// ----------------------------------------------------------------

noeq type num_fmt = {
  nf_min_int  : nat;
  nf_prim_grp : nat;    // 0 == no grouping-position checking
  nf_sec_grp  : nat;    // secondary grouping size (== prim when only one group)
  // Grouping REQUIRED: true only when the pattern EXPLICITLY contains a
  // group char, in which case an ungrouped value longer than the primary
  // group is rejected (test289 "#,#00" rejects "1234"). When a datatype
  // gives only groupChar/decimalChar (no pattern), grouping in the value
  // is optional (test170 "123456.789%" is valid) — nf_grp_required=false.
  nf_grp_req  : bool;
  nf_min_frac : nat;
  nf_max_frac : nat;
  nf_has_exp  : bool;
  nf_group    : C.char;
  nf_decimal  : C.char;
}

let count_zeros (l : list C.char) : nat = count_char char_zero l

// Count digit placeholders ('0' or '#') in a segment.
let rec count_places (l : list C.char) : Tot nat (decreases l) =
  match l with
  | [] -> 0
  | c :: tl -> (if code c = 48 || code c = 35 then 1 else 0) + count_places tl

// Grouping sizes from the integer-part pattern chars (which may contain
// the group char). Returns (prim, sec); prim = 0 means "no grouping".
let grouping_of (grp : C.char) (int_pat : list C.char) : (nat & nat) =
  let segs = split_all grp int_pat in
  match segs with
  | [] -> (0, 0)
  | [_] -> (0, 0)
  | _ ->
    let n = length segs in
    let prim = count_places (index segs (n - 1)) in
    let sec = if n >= 3 then count_places (index segs (n - 2)) else prim in
    (prim, sec)

// Parse a number pattern (already stripped of prefix/suffix literals —
// we only look at 0 / # / group / decimal / E chars) into a num_fmt.
let parse_num_fmt (pat : list C.char) (grp : C.char) (dec : C.char) : num_fmt =
  let has_exp = count_char big_e_char pat > 0 in
  // The pattern body up to the exponent 'E' (if any).
  let body = (match split_first big_e_char pat with
              | Some (a, _) -> a
              | None -> pat) in
  let int_pat, frac_pat =
    (match split_first dec body with
     | Some (a, b) -> a, b
     | None -> body, []) in
  let prim, sec = grouping_of grp int_pat in
  // Fraction '0'/'#' after removing any grouping char.
  let frac_digits_pat = filter (fun (c : C.char) -> code c <> code grp) frac_pat in
  {
    nf_min_int  = count_zeros int_pat;
    nf_prim_grp = prim;
    nf_sec_grp  = sec;
    nf_grp_req  = prim > 0;   // explicit group char in the pattern
    nf_min_frac = count_zeros frac_digits_pat;
    nf_max_frac = count_places frac_digits_pat;
    nf_has_exp  = has_exp;
    nf_group    = grp;
    nf_decimal  = dec;
  }

// Default pattern for a "groupChar/decimalChar only" datatype: standard
// 3-digit grouping for validating grouped values, but grouping is NOT
// required (an ungrouped value of any length is accepted).
let default_num_fmt (grp : C.char) (dec : C.char) : num_fmt =
  { nf_min_int = 0; nf_prim_grp = 3; nf_sec_grp = 3; nf_grp_req = false;
    nf_min_frac = 0; nf_max_frac = 1000000; nf_has_exp = false;
    nf_group = grp; nf_decimal = dec }

// Validate + strip grouping from the integer part. Returns the raw
// digit list (no group chars) or None if grouping / digits are invalid.
let validate_int_group (prim sec : nat) (grp_req : bool) (grp : C.char) (int_chars : list C.char)
  : option (list C.char) =
  let segs = split_all grp int_chars in
  match segs with
  | [] -> Some []
  | [only] ->
    // No group separator present in the value.
    if not (all_digits only) then None
    else if prim = 0 then Some only              // pattern has no grouping: fine
    else if not grp_req then Some only           // grouping optional (no pattern): fine
    else if length only <= prim then Some only   // fits in one group: fine
    else None                                    // too many digits, grouping required
  | _ ->
    if prim = 0 then None  // value is grouped but the pattern has no grouping
    else
      let n = length segs in
      let rec ok (i : nat) : Tot bool (decreases (n - i)) =
        if i >= n then true
        else
          let seg = index segs i in
          if not (all_digits seg) || length seg = 0 then false
          else
            let want =
              if i = n - 1 then prim                 // rightmost group
              else if i = 0 then sec                 // leftmost: 1..sec, checked below
              else sec in                            // middle groups
            let seg_ok =
              if i = 0 then (length seg <= want)
              else (length seg = want) in
            if seg_ok then ok (i + 1) else false
      in
      if ok 0 then Some (concatMap (fun s -> s) segs) else None

// Assemble the canonical lexical from sign / integer digits / fraction
// digits, applying a percent (shift=2) or per-mille (shift=3) left
// decimal-point shift.
let assemble_number (neg : bool) (int_digits frac_digits : list C.char) (shift : nat)
  : list C.char =
  let sign = if neg then [minus_char] else [] in
  if shift = 0 then
    let ip = drop_leading_zeros int_digits in
    (match frac_digits with
     | [] -> sign @ ip
     | _  -> sign @ ip @ (dot_char :: frac_digits))
  else
    // Combine all digits, then place the point `len frac + shift` from
    // the right.
    let alldigits = int_digits @ frac_digits in
    let newfrac = length frac_digits + shift in
    let alllen = length alldigits in
    let padded = if newfrac >= alllen then repeat_char char_zero (newfrac - alllen + 1) @ alldigits else alldigits in
    let padlen = length padded in
    let intlen : nat = if padlen >= newfrac then padlen - newfrac else 0 in
    let ipart = fst (splitAt intlen padded) in
    let fpart = snd (splitAt intlen padded) in
    let ip = drop_leading_zeros ipart in
    sign @ ip @ (dot_char :: fpart)

// Parse a single numeric value against `nf` for the given base kind.
// Returns the canonical lexical or None.
let parse_number (nf : num_fmt) (base_name : string) (v0 : list C.char)
  : option (list C.char) =
  // 1. percent / per-mille (anywhere; removes the marker).
  let has_pct = count_char percent_char v0 > 0 in
  let has_pm  = count_char permille_char v0 > 0 in
  let shift = if has_pct then 2 else if has_pm then 3 else 0 in
  let v1 = filter (fun (c : C.char) ->
                     code c <> code percent_char && code c <> code permille_char) v0 in
  // 2. leading sign.
  let neg, v2 =
    (match v1 with
     | c :: rest ->
       if code c = code minus_char then true, rest
       else if code c = code plus_char then false, rest
       else false, v1
     | _ -> false, v1) in
  // 3. exponent split (only when the pattern declares one).
  let mant, exp_opt =
    if nf.nf_has_exp then
      (match split_first big_e_char v2 with
       | Some (a, b) -> a, Some b
       | None -> v2, None)   // pattern wants exponent but value has none
    else v2, None in
  // integer base rejects any exponent or fraction; require the exponent
  // when the pattern declares one.
  if nf.nf_has_exp && exp_opt = None then None
  else
    // 4. split mantissa on the decimal char.
    let int_chars, frac_chars_raw, has_dec =
      (match split_first nf.nf_decimal mant with
       | Some (a, b) -> a, b, true
       | None -> mant, [], false) in
    // 5. integer grouping.
    (match validate_int_group nf.nf_prim_grp nf.nf_sec_grp nf.nf_grp_req nf.nf_group int_chars with
     | None -> None
     | Some int_digits ->
       // 6. fraction: strip grouping, must be all digits.
       let frac_digits = filter (fun (c : C.char) -> code c <> code nf.nf_group) frac_chars_raw in
       if not (all_digits frac_digits) then None
       else if has_dec && length frac_digits = 0 then None   // trailing decimal char
       else if length int_digits = 0 then None
       else
         let flen = length frac_digits in
         // integer bases: no fraction allowed.
         if is_integer_base base_name && (has_dec || flen > 0) then None
         // min integer digits.
         else if length int_digits < nf.nf_min_int then None
         // min / max fraction digits (only meaningful for the mantissa).
         else if flen < nf.nf_min_frac then None
         else if flen > nf.nf_max_frac then None
         else
           // Un-scaled values keep the ORIGINAL lexical (sign included:
           // pattern "+0" on "+1" emits "+1"^^xsd:decimal, test283) with
           // only group chars stripped and decimalChar normalised to
           // '.'; xsd lexical space admits a leading '+'. Only the
           // percent / per-mille SCALED path recomputes digits.
           let sign_txt =
             (match v1 with
              | c :: _ ->
                if code c = code plus_char then [plus_char]
                else if code c = code minus_char then [minus_char]
                else []
              | _ -> []) in
           let mant_norm =
             sign_txt @ int_digits @
             (if has_dec then dot_char :: frac_digits else []) in
           (match exp_opt with
            | Some exp ->
              // exponent digits (optional leading sign), non-empty;
              // 'E' normalises to 'e' (test158 "0.0E0" -> "0.0e0").
              let esign, edig =
                (match exp with
                 | c :: rest ->
                   if code c = code minus_char then [minus_char], rest
                   else if code c = code plus_char then [], rest
                   else [], exp
                 | _ -> [], exp) in
              if length edig = 0 || not (all_digits edig) then None
              else
                Some (mant_norm @ (C.char_of_int 101 :: (esign @ edig)))  // 'e'
            | None ->
              if shift = 0 then Some mant_norm
              else Some (assemble_number neg int_digits frac_digits shift)))

// ----------------------------------------------------------------
// DATE / TIME format engine.
// ----------------------------------------------------------------

noeq type dt_acc = {
  d_year : option (list C.char);
  d_mon  : option (list C.char);
  d_day  : option (list C.char);
  d_hour : option (list C.char);
  d_min  : option (list C.char);
  d_sec  : option (list C.char);
  d_frac : option (list C.char);
  d_tz   : option (list C.char);
}

let dt_empty : dt_acc =
  { d_year = None; d_mon = None; d_day = None; d_hour = None;
    d_min = None; d_sec = None; d_frac = None; d_tz = None }

// Take up to `maxn` (>=1) leading digits from `v`; returns (digits, rest)
// with at least one digit, or None.
let rec take_digits (maxn : nat) (v : list C.char)
  : Tot (option (list C.char & list C.char)) (decreases v) =
  match v with
  | [] -> None
  | c :: tl ->
    if not (is_digit c) then None
    else if maxn <= 1 then Some ([c], tl)
    else (match tl with
          | c2 :: _ ->
            if is_digit c2 then
              (match take_digits (maxn - 1) tl with
               | Some (ds, rest) -> Some (c :: ds, rest)
               | None -> Some ([c], tl))
            else Some ([c], tl)
          | _ -> Some ([c], tl))

// Take exactly `n` digits.
let rec take_exact (n : nat) (v : list C.char)
  : Tot (option (list C.char & list C.char)) (decreases n) =
  if n = 0 then Some ([], v)
  else match v with
       | c :: tl ->
         if is_digit c then
           (match take_exact (n - 1) tl with
            | Some (ds, rest) -> Some (c :: ds, rest)
            | None -> None)
         else None
       | _ -> None

// Take one-or-more leading digits (for fractional seconds).
let rec take_digits_greedy (v : list C.char)
  : Tot (option (list C.char & list C.char)) (decreases v) =
  match v with
  | c :: tl ->
    if is_digit c then
      (match take_digits_greedy tl with
       | Some (ds, rest) -> Some (c :: ds, rest)
       | None -> Some ([c], tl))
    else None
  | _ -> None

// Parse and canonicalise a timezone token at the head of `v`.
// `allow_z` is true for X/XX/XXX (numeric-with-Z), false for x/xx/xxx.
let parse_tz (allow_z : bool) (v : list C.char) : option (list C.char & list C.char) =
  match v with
  | c :: tl ->
    if allow_z && code c = code cap_z_char then Some ([cap_z_char], tl)
    else if code c = code plus_char || code c = code minus_char then begin
      let sgn = c in
      (match take_exact 2 tl with
       | None -> None
       | Some (hh, r1) ->
         // optional ':' then MM, or bare MM, else MM = "00".
         let after_colon =
           (match r1 with
            | c2 :: r -> if code c2 = code colon_char then Some r else None
            | _ -> None) in
         let mm, r2 =
           (match after_colon with
            | Some r ->
              (match take_exact 2 r with
               | Some (m, rr) -> m, rr
               | None -> [char_zero; char_zero], r1)
            | None ->
              (match take_exact 2 r1 with
               | Some (m, rr) -> m, rr
               | None -> [char_zero; char_zero], r1)) in
         Some (sgn :: (hh @ (colon_char :: mm)), r2))
    end
    else None
  | _ -> None

// Zero-pad a digit list to width 2 (left).
let pad2 (l : list C.char) : list C.char =
  if length l >= 2 then l else repeat_char char_zero (2 - length l) @ l

let is_field_letter (c : C.char) : bool =
  let i = code c in
  i = 121 (* y *) || i = 77 (* M *) || i = 100 (* d *) ||
  i = 72 (* H *) || i = 109 (* m *) || i = 115 (* s *) ||
  i = 83 (* S *) || i = 88 (* X *) || i = 120 (* x *)

// A pattern token: a field (letter + run count) or a literal char.
noeq type dt_token =
  | TkField : C.char -> nat -> dt_token
  | TkLit   : C.char -> dt_token

// Tokenise the pattern (structural fold): consecutive identical field
// letters merge into one TkField with a count; everything else is a
// literal (bare 'T', '-', '/', '.', ':', space). Day/month NAMES and
// quoted literals are outside the CSVW subset — no corpus fixture uses
// them and 'T' appears un-quoted in the dateTime patterns.
let rec tokenize (pat : list C.char) : Tot (list dt_token) (decreases pat) =
  match pat with
  | [] -> []
  | c :: tl ->
    let rest = tokenize tl in
    if is_field_letter c then
      (match rest with
       | TkField f k :: more -> if code f = code c then TkField f (k + 1) :: more
                                else TkField c 1 :: rest
       | _ -> TkField c 1 :: rest)
    else TkLit c :: rest

// Walk the token list against the value chars, accumulating fields.
let rec dt_walk (toks : list dt_token) (v : list C.char) (acc : dt_acc)
  : Tot (option dt_acc) (decreases toks) =
  match toks with
  | [] -> if v = [] then Some acc else None
  | TkLit lc :: more ->
    (match v with
     | vc :: vr -> if code vc = code lc then dt_walk more vr acc else None
     | _ -> None)
  | TkField f n :: more ->
    let i = code f in
    if i = 121 then begin              // y
      if n <> 4 then None              // only yyyy is supported (test191)
      else (match take_exact 4 v with
            | Some (ds, vr) -> dt_walk more vr ({ acc with d_year = Some ds })
            | None -> None)
    end
    else if i = 88 || i = 120 then begin  // X / x  (timezone)
      match parse_tz (i = 88) v with
      | Some (tz, vr) -> dt_walk more vr ({ acc with d_tz = Some tz })
      | None -> None
    end
    else if i = 83 then begin          // S... (fractional seconds, EXACTLY n digits)
      // The run length is the exact fraction width (test246 .S/.SS);
      // a value with MORE digits than the pattern allows leaves the
      // surplus digit to fail against the next token / end-of-pattern
      // (test247 "HH:mm:ss.S" must REJECT "15:02:37.143").
      match take_exact n v with
      | Some (ds, vr) -> dt_walk more vr ({ acc with d_frac = Some ds })
      | None -> None
    end
    else begin
      // M / d / H / m / s : fixed 2-wide when n>=2, else 1..2 digits.
      let taken = if n >= 2 then take_exact 2 v else take_digits 2 v in
      match taken with
      | None -> None
      | Some (ds, vr) ->
        let acc2 =
          if i = 77 then { acc with d_mon = Some ds }
          else if i = 100 then { acc with d_day = Some ds }
          else if i = 72 then { acc with d_hour = Some ds }
          else if i = 109 then { acc with d_min = Some ds }
          else { acc with d_sec = Some ds } in
        dt_walk more vr acc2
    end

// Build the canonical xsd lexical from the accumulated fields for the
// given base. Returns None if a required field is missing.
let build_dt (base_name : string) (acc : dt_acc) : option (list C.char) =
  let tzc = (match acc.d_tz with Some t -> t | None -> []) in
  let fracc = (match acc.d_frac with Some f -> dot_char :: f | None -> []) in
  let time_core () : option (list C.char) =
    match acc.d_hour, acc.d_min with
    | Some h, Some m ->
      let s = (match acc.d_sec with Some s -> s | None -> [char_zero; char_zero]) in
      Some (pad2 h @ (colon_char :: pad2 m) @ (colon_char :: pad2 s) @ fracc)
    | _ -> None in
  let date_core () : option (list C.char) =
    match acc.d_year, acc.d_mon, acc.d_day with
    | Some y, Some mo, Some d ->
      Some (y @ (minus_char :: pad2 mo) @ (minus_char :: pad2 d))
    | _ -> None in
  if base_name = "date" then
    (match date_core () with Some d -> Some (d @ tzc) | None -> None)
  else if base_name = "time" then
    (match time_core () with Some t -> Some (t @ tzc) | None -> None)
  else
    // dateTime / dateTimeStamp / datetime
    (match date_core (), time_core () with
     | Some d, Some t -> Some (d @ (C.char_of_int 84 :: t) @ tzc)  // 'T'
     | _ -> None)

let parse_date_time (base_name : string) (fmt : list C.char) (v : list C.char)
  : option (list C.char) =
  match dt_walk (tokenize fmt) v dt_empty with
  | None -> None
  | Some acc -> build_dt base_name acc

// ----------------------------------------------------------------
// BOOLEAN format engine.
// ----------------------------------------------------------------

let lit_true : list C.char = chars_of "true"
let lit_false : list C.char = chars_of "false"

let parse_bool (fmt : option string) (v : list C.char) : fmt_outcome =
  match fmt with
  | None ->
    let s = string_of v in
    if s = "true" || s = "1" then FO_Valid "true"
    else if s = "false" || s = "0" then FO_Valid "false"
    else FO_Invalid
  | Some f ->
    (match split_first (C.char_of_int 124) (chars_of f) with  // '|'
     | None -> FO_Invalid   // malformed boolean format (test269 "YN")
     | Some (tv, fv) ->
       if v = tv then FO_Valid "true"
       else if v = fv then FO_Valid "false"
       else FO_Invalid)

// ----------------------------------------------------------------
// DURATION lexical validation (xsd:duration / xsd:dayTimeDuration /
// xsd:yearMonthDuration; test279-281). XSD.Datatypes.literal_ill_formed
// does not recognise the duration family, so a nonsense value like
// "Foo" would silently keep its duration datatype without this check.
// A duration `format` facet is a REGULAR EXPRESSION per tabular-
// metadata — no regex engine here, so a format-carrying duration is
// left untouched (FO_NoFormat; test194 stays enumerated).
// ----------------------------------------------------------------

// Optionally consume `<digits>[.<digits> when allow_frac]<designator>`
// from the head of `v`. Returns (consumed?, rest) — backtracks to the
// original list when the designator does not follow the digits.
let dur_opt_field (designator : C.char) (allow_frac : bool) (v : list C.char)
  : (bool & list C.char) =
  match take_digits_greedy v with
  | None -> (false, v)
  | Some (_, r1) ->
    let r2 =
      if allow_frac then
        (match r1 with
         | c :: rr ->
           if code c = code dot_char then
             (match take_digits_greedy rr with
              | Some (_, r3) -> r3
              | None -> r1)   // "1.S" — leave the dot to fail below
           else r1
         | _ -> r1)
      else r1 in
    (match r2 with
     | c :: rest -> if code c = code designator then (true, rest) else (false, v)
     | _ -> (false, v))

let dur_char_Y : C.char = C.char_of_int 89
let dur_char_M : C.char = C.char_of_int 77
let dur_char_D : C.char = C.char_of_int 68
let dur_char_H : C.char = C.char_of_int 72
let dur_char_S : C.char = C.char_of_int 83
let dur_char_T : C.char = C.char_of_int 84
let dur_char_P : C.char = C.char_of_int 80

// The T-part: 'T' (nH)? (nM)? (n(.n)?S)? — at least one time field.
let dur_time_part (v : list C.char) : option (list C.char) =
  match v with
  | c :: rest ->
    if code c <> code dur_char_T then None
    else
      let (h_ok, r1) = dur_opt_field dur_char_H false rest in
      let (m_ok, r2) = dur_opt_field dur_char_M false r1 in
      let (s_ok, r3) = dur_opt_field dur_char_S true r2 in
      if h_ok || m_ok || s_ok then Some r3 else None
  | _ -> None

// Full lexical check for the three duration bases.
let duration_lexical_valid (base_name : string) (v0 : list C.char) : bool =
  // optional leading '-'
  let v1 = (match v0 with
            | c :: rest -> if code c = code minus_char then rest else v0
            | _ -> v0) in
  match v1 with
  | p :: rest ->
    if code p <> code dur_char_P then false
    else if base_name = "yearMonthDuration" then
      // P (nY)? (nM)? — at least one, no T-part.
      let (y_ok, r1) = dur_opt_field dur_char_Y false rest in
      let (m_ok, r2) = dur_opt_field dur_char_M false r1 in
      (y_ok || m_ok) && r2 = []
    else if base_name = "dayTimeDuration" then
      // P (nD)? (T ...)? — at least one field somewhere.
      let (d_ok, r1) = dur_opt_field dur_char_D false rest in
      (match r1 with
       | [] -> d_ok
       | _ -> (match dur_time_part r1 with
               | Some [] -> true
               | _ -> false))
    else
      // xsd:duration: P (nY)? (nM)? (nD)? (T ...)?
      let (y_ok, r1) = dur_opt_field dur_char_Y false rest in
      let (m_ok, r2) = dur_opt_field dur_char_M false r1 in
      let (d_ok, r3) = dur_opt_field dur_char_D false r2 in
      (match r3 with
       | [] -> y_ok || m_ok || d_ok
       | _ -> (match dur_time_part r3 with
               | Some [] -> true
               | _ -> false))
  | _ -> false

let is_duration_base (n : string) : bool =
  n = "duration" || n = "dayTimeDuration" || n = "yearMonthDuration"

// ----------------------------------------------------------------
// Top-level dispatch.
// ----------------------------------------------------------------

// `format_str` is the string-form `format` (date pattern, boolean
// trueVal|falseVal, or a number pattern given as a bare string).
// `pattern` is the object-form number `format.pattern`. `group_char` /
// `decimal_char` are the object-form overrides.
let csvw_format_convert
    (base_name : string)
    (format_str : option string)
    (pattern : option string)
    (group_char : option string)
    (decimal_char : option string)
    (txt : string)
  : fmt_outcome =
  if base_name = "boolean" then
    parse_bool format_str (chars_of txt)
  else if is_numeric_base base_name then begin
    // number pattern may arrive as object `pattern` or bare `format` string.
    let pat_opt = (match pattern with Some p -> Some p | None -> format_str) in
    if pat_opt = None && group_char = None && decimal_char = None then FO_NoFormat
    else begin
      let grp = (match group_char with Some g -> (match first_char g with Some c -> c | None -> C.char_of_int 44) | None -> C.char_of_int 44) in
      let dec = (match decimal_char with Some d -> (match first_char d with Some c -> c | None -> dot_char) | None -> dot_char) in
      let nf = (match pat_opt with
                | Some p -> parse_num_fmt (chars_of p) grp dec
                | None -> default_num_fmt grp dec) in
      match parse_number nf base_name (chars_of txt) with
      | Some lex -> FO_Valid (string_of lex)
      | None -> FO_Invalid
    end
  end
  else if is_date_base base_name then begin
    // A date/time pattern arrives as the bare `format` string OR as the
    // object form's `pattern` member (test191 `{"pattern": "yy-MM-dd"}`).
    let fmt_opt = (match format_str with Some f -> Some f | None -> pattern) in
    match fmt_opt with
    | None -> FO_NoFormat
    | Some f ->
      let bn = if base_name = "datetime" then "dateTime" else base_name in
      (match parse_date_time bn (chars_of f) (chars_of txt) with
       | Some lex -> FO_Valid (string_of lex)
       | None -> FO_Invalid)
  end
  else if is_duration_base base_name then begin
    match format_str with
    | Some fmt ->
      // A duration `format` facet is a REGULAR EXPRESSION (tabular-
      // metadata). Parse it with the verified XSD-flavor engine and test
      // the WHOLE cell against it: XSD pattern facets are implicitly
      // anchored to the entire lexical value, which is exactly
      // matches_norm's whole-word semantics. A match keeps the value on
      // its duration datatype (the caller re-checks the duration lexical
      // space); a non-match drops it to a plain string (test194's `^.$`
      // rejects the multi-char durations). An unparseable pattern (outside
      // the engine's measured fragment) yields None and we FALL BACK to the
      // pre-engine behaviour (FO_NoFormat) — conservative: a format we
      // cannot read never rejects a value it might have accepted.
      (match RXP.parse_xsd_pattern fmt with
       | Some r ->
         if RXE.matches_norm r (RXP.cps_of_string txt) then FO_Valid txt
         else FO_Invalid
       | None -> FO_NoFormat)
    | None ->
      if duration_lexical_valid base_name (chars_of txt) then FO_Valid txt
      else FO_Invalid
  end
  else FO_NoFormat

// tabular-metadata: "If the datatype base is not numeric, boolean, a
// date/time type, or a duration type, the datatype format annotation
// provides a regular expression for the string values" (test154). The
// value MUST match the whole pattern. Kept separate from
// csvw_format_convert (whose else-branch returns FO_NoFormat) so the
// csv2rdf/csv2json conversion behaviour is unchanged; only the VALIDATION
// path consults this. An unparseable pattern never rejects.
let csvw_string_format_ok (base_name : string) (format_str : option string) (txt : string) : bool =
  if base_name = "boolean" || is_numeric_base base_name
     || is_date_base base_name || is_duration_base base_name
  then true
  else
    match format_str with
    | Some fmt ->
      (match RXP.parse_xsd_pattern fmt with
       | Some r -> RXE.matches_norm r (RXP.cps_of_string txt)
       | None -> true)
    | None -> true
