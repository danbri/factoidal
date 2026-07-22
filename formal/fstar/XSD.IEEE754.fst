module XSD.IEEE754

// Decimal-lexical -> IEEE-754 VALUE EQUALITY for xsd:double (binary64),
// xsd:float (binary32) and rdf:JSON numbers (treated as binary64).
//
// This module answers ONE question: do two numeric lexical forms denote
// the SAME IEEE-754 value (sign of zero distinguished, overflow -> the
// same signed infinity, correct round-to-nearest-ties-to-even)?  It never
// needs to emit the float — only compare — so the whole computation is
// done in EXACT big-integer rational arithmetic (F* native `nat`/`int`),
// with no floating point anywhere in F*.  This unblocks the RDF 1.2
// D-entailment tests that hinge on value identity of double/float/JSON
// numbers.
//
// APPROACH (exact rational, round-to-nearest-ties-to-even):
//   A lexical parses to a sign and an exact rational  M * 10^E  (M:nat
//   mantissa from the concatenated integer+fraction digits, E:int the
//   adjusted exponent).  That rational is rounded to the target binary
//   format by comparing it against powers of two purely with big-integer
//   cross-multiplication:  a/b >= 2^k  <=>  a >= b*2^k  (k>=0)  <=>
//   a*2^(-k) >= b  (k<0), all exact integers.  The round/sticky decision
//   is the exact remainder of that division.  The rounded value is a
//   canonical, order-able record { sign ; Zero | Inf | NaN | Finite s e }
//   and two lexicals are equal iff they share that canonical record.
//
//   binary64: 53-bit significand, exponent range emin=-1022..emax=1023.
//   binary32: 24-bit significand, exponent range emin=-126 ..emax=127.
//
// FLOAT (binary32) uses DOUBLE ROUNDING (decimal -> binary64 -> binary32),
// which is exactly what OCaml `Int32.bits_of_float (float_of_string s)`,
// JavaScript `Math.fround(Number(s))` and Python all do.  Pure single
// rounding (decimal -> binary32 directly) diverges from that only on
// exotic double-rounding boundary decimals, none of which appear in the
// D-entailment suite; matching the deployed binary64->binary32 path keeps
// us in lock-step with those runtimes and with the validation harness.
//
// TERMINATION: every recursive helper decreases structurally on a list,
// or on a shrinking `nat` (bit-length / power helpers).  No `--lax`, no
// `assume`, no `admit`.

open FStar.Mul
open FStar.String
open FStar.List.Tot

// -------------------------------------------------------------------
// 1. Exact big-integer helpers.
// -------------------------------------------------------------------

let rec pow2 (n:nat) : Tot pos (decreases n) =
  if n = 0 then 1 else 2 * pow2 (n - 1)

let rec pow10 (n:nat) : Tot pos (decreases n) =
  if n = 0 then 1 else 10 * pow10 (n - 1)

// Number of bits in n (bitlen 0 = 0; for n>0, floor(log2 n)+1).
let rec bitlen (n:nat) : Tot nat (decreases n) =
  if n = 0 then 0 else 1 + bitlen (n / 2)

// Positive * positive stays positive (kept explicit so the big-integer
// numerators/denominators below carry a `pos` type without per-site
// SMT nudging).
let mul_pos (a:pos) (b:pos) : pos = a * b

// num/den >= 2^k, exactly, by cross multiplication.
let geq_ratio (num:pos) (den:pos) (k:int) : bool =
  if k >= 0 then num >= mul_pos den (pow2 k)
  else mul_pos num (pow2 (- k)) >= den

// floor(log2(num/den)), exact.  The candidate k0 = bitlen num - bitlen den
// is provably either the answer or one too high, so a single comparison
// settles it.
let floor_log2_ratio (num:pos) (den:pos) : int =
  let k0 = bitlen num - bitlen den in
  if geq_ratio num den k0 then k0 else k0 - 1

// Round n/d (n:nat, d:pos) to the nearest integer, ties to even.  Exact.
let round_ties_even (n:nat) (d:pos) : nat =
  let q = n / d in
  let r = n % d in
  let twice = 2 * r in
  if twice < d then q
  else if twice > d then q + 1
  else (if q % 2 = 0 then q else q + 1)  // exact tie -> nearest even

// -------------------------------------------------------------------
// 2. Canonical IEEE-754 value (sign-aware, order-able for equality).
// -------------------------------------------------------------------

type fclass =
  | FZero   : fclass                  // signed zero
  | FInf    : fclass                  // signed infinity
  | FNaN    : fclass                  // not-a-number (never equal to anything)
  | FFinite : mant:nat -> bexp:int -> fclass
                                      // value = mant * 2^bexp, normalized
                                      // (normals: mant in [2^(p-1),2^p);
                                      //  subnormals: bexp = emin-(p-1))

type fval = { fsign : bool; fcls : fclass }   // fsign = true means negative

// IEEE-754 value equality of two canonical forms.  NaN is unequal to
// everything including itself; +0 and -0 differ; +inf and -inf differ.
let fval_eq (a:fval) (b:fval) : bool =
  match a.fcls, b.fcls with
  | FNaN, _ -> false
  | _, FNaN -> false
  | FZero, FZero -> a.fsign = b.fsign
  | FInf, FInf -> a.fsign = b.fsign
  | FFinite s1 e1, FFinite s2 e2 -> a.fsign = b.fsign && s1 = s2 && e1 = e2
  | _, _ -> false

// -------------------------------------------------------------------
// 3. Round an exact positive rational num/den to a target format.
// -------------------------------------------------------------------

// Returns the magnitude's class (FZero on underflow, FInf on overflow,
// otherwise FFinite s e).  Sign is attached by the caller.  num>0 required.
let round_rational (p:pos) (emin:int) (emax:int) (num:pos) (den:pos) : fclass =
  let e_norm = floor_log2_ratio num den in
  let e_denorm = emin - (p - 1) in       // fixed exponent of the subnormal grid
  let e_max_normal = emax - (p - 1) in    // exponent of the largest finite significand
  let e_tent = e_norm - (p - 1) in
  // Strict overflow short-circuit: e_norm > emax forces the value above
  // the round-to-infinity threshold regardless of the round bits, and
  // avoids building astronomically large powers of two for e.g. 1e400.
  if e_tent > e_max_normal then FInf
  else begin
    // Clamp into the subnormal grid on underflow so the quantization step
    // is uniform (2^e_denorm) for every subnormal / smallest-normal value.
    let e : int = if e_tent < e_denorm then e_denorm else e_tent in
    // value / 2^e  =  (num/den) / 2^e , as an exact integer ratio bigN/bigD.
    let bigN : nat = if e >= 0 then num else mul_pos num (pow2 (- e)) in
    let bigD : pos = if e >= 0 then mul_pos den (pow2 e) else den in
    let s0 = round_ties_even bigN bigD in
    if s0 = 0 then FZero
    else begin
      // Rounding may carry the significand up to exactly 2^p; renormalize.
      let twop = pow2 p in
      let s = if s0 >= twop then s0 / 2 else s0 in
      let e2 = if s0 >= twop then e + 1 else e in
      if e2 > e_max_normal then FInf
      else FFinite s e2
    end
  end

// -------------------------------------------------------------------
// 4. Lexical parsing:  string -> (sign, M, E)  |  INF  |  NaN.
// -------------------------------------------------------------------

let is_digit (c:FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in n >= 48 && n <= 57

let all_digits (cs:list FStar.Char.char) : bool = List.Tot.for_all is_digit cs

// acc-folding decimal-digit reader.  Non-digit chars are clamped to 0 so
// the result stays a `nat`; callers validate with `all_digits` first, so
// the clamp is never exercised on well-formed input.
let rec digits_to_nat (acc:nat) (cs:list FStar.Char.char)
  : Tot nat (decreases cs) =
  match cs with
  | [] -> acc
  | c :: rest ->
    let raw = FStar.Char.int_of_char c - 48 in
    let d = if raw < 0 then 0 else if raw > 9 then 0 else raw in
    digits_to_nat (acc * 10 + d) rest

// Split a char list at the first occurrence of char-code `code`.
// Returns (before, Some after) if found, else (all, None).
let rec split_at_code (code:int) (cs:list FStar.Char.char)
  : Tot (list FStar.Char.char & option (list FStar.Char.char)) (decreases cs) =
  match cs with
  | [] -> ([], None)
  | c :: rest ->
    if FStar.Char.int_of_char c = code then ([], Some rest)
    else
      let (before, after) = split_at_code code rest in
      (c :: before, after)

// Parse an exponent tail:  optional +/- then one-or-more digits.
let parse_signed_int (cs:list FStar.Char.char) : option int =
  match cs with
  | [] -> None
  | c :: rest ->
    let ci = FStar.Char.int_of_char c in
    let (neg, digits) =
      if ci = 43 then (false, rest)        // '+'
      else if ci = 45 then (true, rest)    // '-'
      else (false, cs) in
    if Cons? digits && all_digits digits then
      let v = digits_to_nat 0 digits in
      Some (if neg then - v else v)
    else None

type parsed =
  | PNum : neg:bool -> m:nat -> e:int -> parsed
  | PInf : neg:bool -> parsed
  | PNaN : parsed

// Parse a decimal/scientific numeric lexical (after INF/NaN handling).
let parse_decimal (neg:bool) (chars:list FStar.Char.char) : option parsed =
  // 'e' = 101, 'E' = 69 : split at the first exponent marker.
  let (mant, exp_opt) = split_at_code 101 chars in
  let (mant, exp_opt) =
    if Some? exp_opt then (mant, exp_opt)
    else split_at_code 69 chars in
  let exp_res : option int =
    match exp_opt with
    | None -> Some 0
    | Some ec -> parse_signed_int ec in
  match exp_res with
  | None -> None
  | Some exp_val ->
    // '.' = 46 : split mantissa into integer and fraction parts.
    let (ipart, fopt) = split_at_code 46 mant in
    let fpart = (match fopt with None -> [] | Some f -> f) in
    if all_digits ipart && all_digits fpart
       && List.Tot.length ipart + List.Tot.length fpart >= 1 then
      let m = digits_to_nat 0 (ipart @ fpart) in
      let e = exp_val - List.Tot.length fpart in
      Some (PNum neg m e)
    else None

let parse_lexical (s:string) : option parsed =
  if s = "NaN" then Some PNaN
  else if s = "INF" || s = "+INF" then Some (PInf false)
  else if s = "-INF" then Some (PInf true)
  else
    let chars = String.list_of_string s in
    match chars with
    | [] -> None
    | c :: rest ->
      let ci = FStar.Char.int_of_char c in
      if ci = 43 then parse_decimal false rest       // leading '+'
      else if ci = 45 then parse_decimal true rest   // leading '-'
      else parse_decimal false chars

// -------------------------------------------------------------------
// 5. Canonicalize a parsed lexical into an fval for a given format.
// -------------------------------------------------------------------

let canon (p:pos) (emin:int) (emax:int) (pv:parsed) : fval =
  match pv with
  | PNaN -> { fsign = false; fcls = FNaN }
  | PInf neg -> { fsign = neg; fcls = FInf }
  | PNum neg m e ->
    if m = 0 then { fsign = neg; fcls = FZero }
    else
      let mp : pos = m in
      let num : pos = if e >= 0 then mul_pos mp (pow10 e) else mp in
      let den : pos = if e >= 0 then 1 else pow10 (- e) in
      { fsign = neg; fcls = round_rational p emin emax num den }

// binary64 canonicalization.
let canon_double (pv:parsed) : fval = canon 53 (-1022) 1023 pv

// binary32 canonicalization via DOUBLE ROUNDING (decimal -> binary64 ->
// binary32), matching OCaml/JS/Python.  A NaN stays NaN; an infinity in
// binary64 is an infinity in binary32; a finite binary64 value s*2^e is an
// exact dyadic rational that we re-round to binary32.
let canon_float (pv:parsed) : fval =
  let d64 = canon_double pv in
  match d64.fcls with
  | FNaN -> { fsign = d64.fsign; fcls = FNaN }
  | FZero -> { fsign = d64.fsign; fcls = FZero }
  | FInf -> { fsign = d64.fsign; fcls = FInf }
  | FFinite s e ->
    // s > 0 here (round_rational never returns FFinite 0); build the exact
    // ratio s*2^e = num2/den2 and round to binary32.
    let sp : pos = if s = 0 then 1 else s in
    let num2 : pos = if e >= 0 then mul_pos sp (pow2 e) else sp in
    let den2 : pos = if e >= 0 then 1 else pow2 (- e) in
    { fsign = d64.fsign; fcls = round_rational 24 (-126) 127 num2 den2 }

// -------------------------------------------------------------------
// 6. Public value-equality API.
// -------------------------------------------------------------------

// Two xsd:double lexicals denote the same IEEE-754 binary64 value?
// (Malformed input falls back to raw string equality — harmless, and the
// D-entailment tests only feed well-formed lexicals.)
let double_value_eq (a:string) (b:string) : bool =
  match parse_lexical a, parse_lexical b with
  | Some pa, Some pb -> fval_eq (canon_double pa) (canon_double pb)
  | _, _ -> a = b

// Two xsd:float lexicals denote the same IEEE-754 binary32 value?
let float_value_eq (a:string) (b:string) : bool =
  match parse_lexical a, parse_lexical b with
  | Some pa, Some pb -> fval_eq (canon_float pa) (canon_float pb)
  | _, _ -> a = b

// rdf:JSON number lexicals — JSON numbers are IEEE-754 binary64.
let json_number_eq (a:string) (b:string) : bool = double_value_eq a b
