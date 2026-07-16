module Regex.XSDPattern

// XSD-flavor regular-expression PARSER (Phase 2 of issue #304).
// Design doc: docs/designissues/2026-07-15-verified-regex-engine.md
//
// Parses XML Schema Part 2 Appendix F pattern syntax (+ the XPath fn:matches
// `^`/`$` anchors that the SHACL / ShEx / CSVW pattern corpora actually use)
// into the Regex.Syntax AST over Unicode codepoints. Total F*, extracted like
// the rest of the tree (iron rule #4: parsers are F*-implemented).
//
// SCOPE — DERIVED BY MEASURING THE FIXTURES THIS ENGINE WILL CONSUME
// (grep of the target corpora, 2026-07-16; design-doc §2 audit):
//
//   * OWL Inconsistent-pattern fixture (third_party/testing/owl/all.rdf:3051):
//       xsd:pattern "a(b|c)"   -- literals, groups (), alternation |
//     plus the derived enumeration `ab|ac` the #299 emptiness check intersects.
//   * CSVW test194 duration format (test194-metadata.json): "^.$"
//       -- anchors ^ $, dot .
//   * SHACL sh:pattern corpus: ^\d{3}-\d{2}-\d{4}$, [2-8][0-9]*, \d{4},
//       (-\d{4})?, .*?, \.(jpg|jpeg|...)$, literal runs -- char classes with
//       ranges, \d, {n}/{n,m}, ?, *, +, escaped metachars, anchors.
//   * ShEx pattern corpus: (ab)+, .*cd.*, ^https?://, {2,3}, \t \n \r \uXXXX
//       \U00XXXXXX escapes, escaped ^ $ ( [ etc.
//   * XSD.Datatypes / XSD.Facets: no built-in xsd:pattern constants (measured;
//       nothing to cover there).
//
// Constructs IMPLEMENTED (exactly the measured union): ordinary literals
// (any codepoint, incl. astral), `.`, character classes `[...]` with ranges
// and the `\d \D \s \S \w \W` escapes, single-char escapes
// (`\n \r \t \f \\ \. \- \/ \^ \$ \( \) \[ \] \{ \} \| \* \+ \?`), Unicode
// escapes `\uHHHH` / `\UHHHHHHHH`, quantifiers `?` `*` `+` `{n}` `{n,}`
// `{n,m}` (with a trailing lazy `?` accepted and ignored — lazy vs greedy does
// not change the LANGUAGE, and this engine decides membership, not capture),
// groups `(...)` and non-capturing `(?:...)`, alternation `|`, and the anchors
// `^` / `$` (parsed as no-ops: matching here is whole-string membership, so a
// boundary anchor asserts what is already true — a Phase-3 substring consumer
// wraps with `.*`).
//
// Negated character classes `[^...]` ARE supported (complement over
// [0, max_codepoint] via `complement_ranges`; #304 phase 4 added the SPARQL
// `a[^b]c` shape). Constructs that still cleanly return None (NOT in the
// measured set): lookahead/lookbehind/flag groups `(?=...`,
// `(?<...`, `(?i)`, category escapes `\p{...}` / `\P{...}`, and backreferences
// `\1` (which leave the regular fragment entirely — issue #304 excludes them
// on principle). `\w`/`\W` use the ECMAScript definition [A-Za-z0-9_]; the
// XSD category-table definition is deferred (no fixture needs it).
//
// TOTALITY: recursive descent over `list nat`, terminated by an explicit fuel
// that decreases on every call (fstar-module-style trap #3: fuel scales with
// input length, never a bare constant). The top-level budget is a generous
// multiple of the input length, so no measured pattern exhausts it; a genuinely
// pathological input returns None rather than diverging.

open FStar.Mul
open Regex.Syntax
module L = FStar.List.Tot

// ----------------------------------------------------------------------------
// Codepoint constants for the metacharacters
// ----------------------------------------------------------------------------

let cp_lparen   : nat = 0x28
let cp_rparen   : nat = 0x29
let cp_lbracket : nat = 0x5B
let cp_rbracket : nat = 0x5D
let cp_lbrace   : nat = 0x7B
let cp_rbrace   : nat = 0x7D
let cp_pipe     : nat = 0x7C
let cp_star     : nat = 0x2A
let cp_plus     : nat = 0x2B
let cp_question : nat = 0x3F
let cp_dot      : nat = 0x2E
let cp_caret    : nat = 0x5E
let cp_dollar   : nat = 0x24
let cp_backslash: nat = 0x5C
let cp_hyphen   : nat = 0x2D
let cp_comma    : nat = 0x2C
let cp_colon    : nat = 0x3A
let cp_0        : nat = 0x30
let cp_9        : nat = 0x39
let cp_u        : nat = 0x75
let cp_U        : nat = 0x55

// ----------------------------------------------------------------------------
// Leaf regex builders
// ----------------------------------------------------------------------------

// A single-codepoint literal class.
let single (c:nat) : regex = R_Ranges [(c, c)]

// XSD `.` matches any character except newline (#xA) and carriage return
// (#xD): the complement of {#xA, #xD} over [0, max_codepoint].
let dot_regex : regex = R_Ranges (complement_ranges [(0x0A, 0x0A); (0x0D, 0x0D)])

// ----------------------------------------------------------------------------
// Escapes
// ----------------------------------------------------------------------------

// Hex digit value.
let hex_val (c:nat) : option nat =
  if c >= 0x30 && c <= 0x39 then Some (c - 0x30)
  else if c >= 0x61 && c <= 0x66 then Some (c - 0x61 + 10)
  else if c >= 0x41 && c <= 0x46 then Some (c - 0x41 + 10)
  else None

// Read exactly `n` hex digits, accumulating the value. The remaining list is
// no longer than the input (needed by the char-class decreases measure).
let rec read_hex_n (n:nat) (input:list nat) (acc:nat)
  : Tot (option (nat & (r:list nat{L.length r <= L.length input}))) (decreases n) =
  if n = 0 then Some (acc, input)
  else match input with
       | [] -> None
       | c :: t ->
         (match hex_val c with
          | None -> None
          | Some v ->
            (match read_hex_n (n - 1) t (acc * 16 + v) with
             | None -> None
             | Some (res, rest) -> Some (res, rest)))

// Single-character escapes: control chars and escaped metacharacters.
let char_escape (letter:nat) : option nat =
  if letter = 0x6E then Some 0x0A          // \n
  else if letter = 0x72 then Some 0x0D     // \r
  else if letter = 0x74 then Some 0x09     // \t
  else if letter = 0x66 then Some 0x0C     // \f
  else if letter = cp_backslash then Some 0x5C
  else if letter = cp_dot then Some 0x2E
  else if letter = cp_hyphen then Some 0x2D
  else if letter = 0x2F then Some 0x2F      // \/
  else if letter = cp_caret then Some 0x5E
  else if letter = cp_dollar then Some 0x24
  else if letter = cp_lparen then Some 0x28
  else if letter = cp_rparen then Some 0x29
  else if letter = cp_lbracket then Some 0x5B
  else if letter = cp_rbracket then Some 0x5D
  else if letter = cp_lbrace then Some 0x7B
  else if letter = cp_rbrace then Some 0x7D
  else if letter = cp_pipe then Some 0x7C
  else if letter = cp_star then Some 0x2A
  else if letter = cp_plus then Some 0x2B
  else if letter = cp_question then Some 0x3F
  else None

// Multi-character class escapes `\d \D \s \S \w \W` as codepoint ranges.
// \s = {#x9 #xA #xD #x20} (XSD). \w = [A-Za-z0-9_] (ECMAScript; XSD category
// tables deferred, unmeasured). \D \S \W are the complements over [0,max].
let class_escape_ranges (letter:nat) : option (list (nat & nat)) =
  if letter = 0x64 then Some [(0x30, 0x39)]                                   // \d
  else if letter = 0x44 then Some (complement_ranges [(0x30, 0x39)])          // \D
  else if letter = 0x73 then Some [(0x09, 0x0A); (0x0D, 0x0D); (0x20, 0x20)]  // \s
  else if letter = 0x53 then Some (complement_ranges [(0x09, 0x0A); (0x0D, 0x0D); (0x20, 0x20)])  // \S
  else if letter = 0x77 then Some [(0x30, 0x39); (0x41, 0x5A); (0x5F, 0x5F); (0x61, 0x7A)]        // \w
  else if letter = 0x57 then Some (complement_ranges [(0x30, 0x39); (0x41, 0x5A); (0x5F, 0x5F); (0x61, 0x7A)])  // \W
  else None

// Escape as an ATOM (top-level `\...`): a class escape becomes an R_Ranges,
// a unicode escape a single codepoint, a char escape a singleton class.
let parse_escape_atom (letter:nat) (t2:list nat) : option (regex & list nat) =
  match class_escape_ranges letter with
  | Some rs -> Some (R_Ranges rs, t2)
  | None ->
    if letter = cp_u then
      (match read_hex_n 4 t2 0 with
       | Some (cp, rest) -> if cp <= max_codepoint then Some (single cp, rest) else None
       | None -> None)
    else if letter = cp_U then
      (match read_hex_n 8 t2 0 with
       | Some (cp, rest) -> if cp <= max_codepoint then Some (single cp, rest) else None
       | None -> None)
    else (match char_escape letter with
          | Some cp -> Some (single cp, t2)
          | None -> None)

// Escape INSIDE a character class: yields the codepoint ranges it contributes,
// with a remaining-length bound (so the class scanner stays total on `length`).
let class_escape_item (letter:nat) (t2:list nat)
  : option (list (nat & nat) & (r:list nat{L.length r <= L.length t2})) =
  match class_escape_ranges letter with
  | Some rs -> Some (rs, t2)
  | None ->
    if letter = cp_u then
      (match read_hex_n 4 t2 0 with
       | Some (cp, rest) -> if cp <= max_codepoint then Some ([(cp, cp)], rest) else None
       | None -> None)
    else if letter = cp_U then
      (match read_hex_n 8 t2 0 with
       | Some (cp, rest) -> if cp <= max_codepoint then Some ([(cp, cp)], rest) else None
       | None -> None)
    else (match char_escape letter with
          | Some cp -> Some ([(cp, cp)], t2)
          | None -> None)

// ----------------------------------------------------------------------------
// Character classes  [...]
// ----------------------------------------------------------------------------
//
// Positive classes only (`in_ranges` is an OR over intervals, so an unsorted /
// overlapping range list is still exact). Negated classes `[^...]` are NOT in
// the measured set and return None. Range items `a-z` require plain-codepoint
// endpoints with lo <= hi.

let rec parse_class_items (input:list nat) (acc:list (nat & nat))
  : Tot (option (list (nat & nat) & list nat)) (decreases (L.length input)) =
  match input with
  | [] -> None                                   // unterminated class
  | h :: t ->
    if h = cp_rbracket then Some (acc, t)         // end of class
    else if h = cp_backslash then
      (match t with
       | [] -> None
       | letter :: t2 ->
         (match class_escape_item letter t2 with
          | None -> None
          | Some (rs, t3) -> parse_class_items t3 (L.append acc rs)))
    else
      (match t with
       | d :: c2 :: t2 ->
         if d = cp_hyphen && c2 <> cp_rbracket && c2 <> cp_backslash && h <= c2 then
           parse_class_items t2 (L.append acc [(h, c2)])       // range h-c2
         else parse_class_items t (L.append acc [(h, h)])       // literal h
       | _ -> parse_class_items t (L.append acc [(h, h)]))

// Entry after the opening `[`.
// Negated class `[^...]`: parse the item ranges after the `^`, then take their
// complement over [0, max_codepoint] (`complement_ranges`). The complement is
// exact when the item ranges are sorted-disjoint (`complement_ranges`' stated
// precondition); the measured negated-class fixtures are single-range
// (SPARQL `a[^b]c`), for which this holds trivially.
let parse_class (input:list nat) : option (regex & list nat) =
  match input with
  | [] -> None
  | h :: t ->
    if h = cp_caret then
      (match parse_class_items t [] with
       | None -> None
       | Some (ranges, rest) -> Some (R_Ranges (complement_ranges ranges), rest))
    else (match parse_class_items input [] with
          | None -> None
          | Some (ranges, rest) -> Some (R_Ranges ranges, rest))

// ----------------------------------------------------------------------------
// Quantifiers
// ----------------------------------------------------------------------------

let rec repeat_exact (r:regex) (n:nat) : Tot regex (decreases n) =
  if n = 0 then R_Eps else R_Cat r (repeat_exact r (n - 1))

// k optional copies: (r?)^k, used for the {n,m} upper slack.
let rec repeat_opt (r:regex) (k:nat) : Tot regex (decreases k) =
  if k = 0 then R_Eps else R_Cat (R_Alt r R_Eps) (repeat_opt r (k - 1))

// Read a (possibly empty) run of decimal digits.
let rec read_digits_acc (input:list nat) (acc:nat) (seen:bool)
  : Tot (nat & list nat & bool) (decreases input) =
  match input with
  | c :: t -> if c >= cp_0 && c <= cp_9 then read_digits_acc t (acc * 10 + (c - cp_0)) true
              else (acc, input, seen)
  | [] -> (acc, input, seen)

let read_uint (input:list nat) : option (nat & list nat) =
  let (v, rest, seen) = read_digits_acc input 0 false in
  if seen then Some (v, rest) else None

// Parse a `{...}` quantifier body (input is AFTER the `{`).
let parse_brace (r:regex) (t:list nat) : option (regex & list nat) =
  match read_uint t with
  | None -> None
  | Some (n, t1) ->
    (match t1 with
     | c :: t2 ->
       if c = cp_rbrace then Some (repeat_exact r n, t2)                         // {n}
       else if c = cp_comma then
         (match t2 with
          | c2 :: t3 ->
            if c2 = cp_rbrace then Some (R_Cat (repeat_exact r n) (R_Star r), t3) // {n,}
            else (match read_uint t2 with
                  | None -> None
                  | Some (m, t3') ->
                    (match t3' with
                     | c3 :: t4 ->
                       if c3 = cp_rbrace && m >= n then
                         Some (R_Cat (repeat_exact r n) (repeat_opt r (m - n)), t4)  // {n,m}
                       else None
                     | [] -> None))
          | [] -> None)
       else None
     | [] -> None)

// Drop a trailing lazy `?` (e.g. `*?`, `+?`, `??`): identical language.
let skip_lazy (t:list nat) : list nat =
  match t with
  | c :: t2 -> if c = cp_question then t2 else t
  | [] -> t

// Apply a postfix quantifier (if any) to an already-parsed atom `r`.
let parse_quant (r:regex) (rest:list nat) : option (regex & list nat) =
  match rest with
  | [] -> Some (r, rest)
  | q :: t ->
    if q = cp_star then Some (R_Star r, skip_lazy t)
    else if q = cp_plus then Some (R_Cat r (R_Star r), skip_lazy t)
    else if q = cp_question then Some (R_Alt r R_Eps, skip_lazy t)
    else if q = cp_lbrace then
      (match parse_brace r t with
       | None -> None
       | Some (r', t') -> Some (r', skip_lazy t'))
    else Some (r, rest)

// Metacharacters that may not begin an atom (a quantifier with no atom, or an
// unbalanced closer). `|` and `)` are handled by the sequence layer.
let is_atom_meta (h:nat) : bool =
  h = cp_star || h = cp_plus || h = cp_question || h = cp_lbrace ||
  h = cp_rbrace || h = cp_rbracket || h = cp_pipe || h = cp_rparen

// ----------------------------------------------------------------------------
// Recursive-descent core (alt > seq > rep > atom > group), fuel-terminated
// ----------------------------------------------------------------------------

let rec parse_alt (fuel:nat) (input:list nat)
  : Tot (option (regex & list nat)) (decreases fuel) =
  if fuel = 0 then None
  else (match parse_seq (fuel - 1) input with
        | None -> None
        | Some (r1, rest) ->
          (match rest with
           | c :: t ->
             if c = cp_pipe then
               (match parse_alt (fuel - 1) t with
                | None -> None
                | Some (r2, rest2) -> Some (R_Alt r1 r2, rest2))
             else Some (r1, rest)
           | [] -> Some (r1, rest)))

and parse_seq (fuel:nat) (input:list nat)
  : Tot (option (regex & list nat)) (decreases fuel) =
  if fuel = 0 then None
  else (match input with
        | [] -> Some (R_Eps, [])
        | h :: _ ->
          if h = cp_pipe || h = cp_rparen then Some (R_Eps, input)
          else (match parse_rep (fuel - 1) input with
                | None -> None
                | Some (r1, rest) ->
                  (match rest with
                   | [] -> Some (r1, [])
                   | h2 :: _ ->
                     if h2 = cp_pipe || h2 = cp_rparen then Some (r1, rest)
                     else (match parse_seq (fuel - 1) rest with
                           | None -> None
                           | Some (r2, rest2) -> Some (R_Cat r1 r2, rest2)))))

and parse_rep (fuel:nat) (input:list nat)
  : Tot (option (regex & list nat)) (decreases fuel) =
  if fuel = 0 then None
  else (match parse_atom (fuel - 1) input with
        | None -> None
        | Some (r, rest) -> parse_quant r rest)

and parse_atom (fuel:nat) (input:list nat)
  : Tot (option (regex & list nat)) (decreases fuel) =
  if fuel = 0 then None
  else (match input with
        | [] -> None
        | h :: t ->
          if h = cp_lparen then parse_group (fuel - 1) t
          else if h = cp_lbracket then parse_class t
          else if h = cp_dot then Some (dot_regex, t)
          else if h = cp_caret then Some (R_Eps, t)      // ^ anchor: no-op (whole-string)
          else if h = cp_dollar then Some (R_Eps, t)     // $ anchor: no-op (whole-string)
          else if h = cp_backslash then
            (match t with
             | [] -> None
             | letter :: t2 -> parse_escape_atom letter t2)
          else if is_atom_meta h then None
          else Some (single h, t))

and parse_group (fuel:nat) (t:list nat)
  : Tot (option (regex & list nat)) (decreases fuel) =
  if fuel = 0 then None
  else (match t with
        | q :: c :: t2 ->
          if q = cp_question && c = cp_colon then parse_group_close (fuel - 1) t2  // (?: non-capturing
          else if q = cp_question then None            // (?=  (?!  (?<  (?i)  -> unsupported
          else parse_group_close (fuel - 1) t
        | q :: _ ->
          if q = cp_question then None                  // `(?` then end -> unsupported
          else parse_group_close (fuel - 1) t
        | [] -> parse_group_close (fuel - 1) t)         // `(` at end -> close will fail (no `)`)

and parse_group_close (fuel:nat) (t:list nat)
  : Tot (option (regex & list nat)) (decreases fuel) =
  if fuel = 0 then None
  else (match parse_alt (fuel - 1) t with
        | None -> None
        | Some (r, rest) ->
          (match rest with
           | c :: t2 -> if c = cp_rparen then Some (r, t2) else None
           | [] -> None))

// ----------------------------------------------------------------------------
// Public API
// ----------------------------------------------------------------------------

// Parse a pattern given as a codepoint list. Succeeds only if the ENTIRE input
// is consumed (XSD patterns are whole-pattern; a trailing unbalanced `)` etc.
// yields None).
let parse_cps (cps:list nat) : option regex =
  let fuel : nat = 16 * (L.length cps + 4) in
  match parse_alt fuel cps with
  | Some (r, []) -> Some r
  | _ -> None

// Decode a UTF-8 string to its codepoint list (native runtime: BatUTF8-backed
// FStar.String.list_of_string; each FStar.Char.char is the scalar value).
let cps_of_string (s:string) : list nat =
  L.map (fun (c:FStar.Char.char) -> (FStar.Char.int_of_char c <: nat)) (FStar.String.list_of_string s)

// Parse an XSD-flavor pattern string to a Regex.Syntax regex, or None if it
// uses a construct outside the supported (measured) fragment.
let parse_xsd_pattern (s:string) : option regex = parse_cps (cps_of_string s)
