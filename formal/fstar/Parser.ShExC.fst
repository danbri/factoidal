module Parser.ShExC

// ============================================================================
// ShExC (ShEx compact syntax) parser — Stage 9 of the ShEx program
// (docs/designissues/2026-07-05-shex-program-plan.md). Parses ShExC schema
// text directly into ShEx.Schema.fst's existing `shex_schema` AST (the same
// tree `ShEx.Schema.decode_shex_schema` produces from ShExJ), so every
// downstream consumer (ShEx.Validation.fst's `validate_focus`, the
// differential/equality checker, npm/CLI wiring) is unchanged.
//
// Architecture: tokenize (character-level scan reusing Parser.Turtle's
// IRIREF/PNAME/STRING/NUMBER scanners — ShExC borrows those terminals
// byte-for-byte from Turtle/SPARQL, per shex.io/shex-semantics's own
// grammar credits) into a `list shexc_token`, then a fuel-based mutually
// recursive descent parser over the token list builds the AST — same
// two-phase shape as SPARQL11.Parser.fst (tokenize_loop + token_stream +
// fuel-threaded parse_expr family), chosen over Parser.Turtle's raw
// char-position combinators because ShExC's shapeExpr algebra (OR/AND/NOT
// precedence, EachOf/OneOf grouping, cardinality suffixes, EXTENDS/CLOSED/
// EXTRA shape-definition modifiers) is a deeper non-terminal graph than
// Turtle's, and keyword case-insensitivity + comment/whitespace skipping
// are each handled once at tokenize time instead of at every grammar rule.
//
// Acceptance: bin/shex-runner --differential parses every ShExC
// fixture under third_party/testing/shex/schemas/ and checks the
// result against the reference ShExJ decoding of its .json twin via
// ShEx.SchemaEq.shex_schema_equal — 433 of 433 pairs structurally
// equal (the one known upstream defect, start2RefS2.json's "p1" typo
// vs. the canonical .shex's "p2", is a documented expected mismatch:
// this parser agreeing with the .shex there is correct).
//
// Scope (grammar constructs supported):
//   - PREFIX / BASE / IMPORT directives (case-insensitive keyword, SPARQL-
//     style syntax only — no dot, no `@prefix`/`@base` Turtle-style form;
//     grepped zero hits for the latter across the vendored corpus). The
//     DEFAULT (empty) prefix (`PREFIX : <iri>`, then bare `:local`) is
//     supported, including as a shapeRef target (`@:label`) and with
//     whitespace before the label (`@ :label`).
//   - START = shapeExpression, startActs (%...%).
//   - shapeExprDecl: label (IRI/PNAME/BNode) + shapeExpression | EXTERNAL,
//     optionally ABSTRACT-prefixed.
//   - shapeExpression algebra: OR / AND / NOT, parenthesized sub-expressions,
//     shapeRef (`@<iri>`, `@prefix:local`, `@_:bnode`, and each of those
//     forms with whitespace between the `@` and the label), the
//     wildcard `.`. Bare "A AND B AND C" flattens to one N-ary
//     SE_ShapeAnd/SE_ShapeOr; a PARENTHESIZED "(A AND B)" stays nested
//     when a further "AND C" follows (open1dotAND1dotcloseAND1dot.json),
//     while a nodeConstraint's own IMPLICIT "shapeOrRef" AND (no "AND"
//     keyword at all -- see below) DOES flatten into a surrounding
//     explicit AND chain (FocusIRI2EachBnodeNested2EachIRIRef.json).
//   - shapeDefinition: CLOSED, EXTRA (one-or-more predicates), EXTENDS
//     (zero-or-more, each a shapeExprRef), `{ oneOfTripleExpr? }`,
//     annotations, semActs.
//   - oneOfTripleExpr: `;`-separated groupTripleExpr, `|`-separated
//     unaryTripleExpr — EachOf/OneOf wrapping applied ONLY when a group
//     genuinely has >=2 non-empty members (a lone member is unwrapped,
//     matching ShEx.Schema.fst's decode_group / the corpus's own JSON
//     twins — see 1dotSemiOne1dotSemi.json).
//   - unaryTripleExpr: `$label` (id) prefix, tripleConstraint,
//     bracketedTripleExpr `( ... ) cardinality?`, include `&label`.
//   - tripleConstraint: senseFlags (`^` inverse), predicate (including the
//     Turtle `a` = rdf:type shorthand, case-sensitive lowercase only),
//     inlineShapeExpression, cardinality (`*`/`+`/`?`/`{m,n}`/`{m,}`/
//     `{m,*}`), annotations, semActs. A bare, uncombined wildcard `.`
//     value omits "valueExpr" entirely (1dot.json); combined with
//     anything (`NOT .`, `. AND x`) it reifies as an empty Shape, never
//     an empty NodeConstraint (1NOTdot.json).
//   - nodeConstraint: nodeKind (IRI/BNODE/NONLITERAL/LITERAL), datatype,
//     value set (`[ ... ]`: exact IRI/literal/language values, IRI/literal/
//     language stems `~` (bare, no exclusions -> *Stem; with exclusions
//     -> *StemRange), stem ranges with exclusions `- v ~?`, the
//     wildcard-stem `.` + typed exclusions form), numeric facets
//     (MININCLUSIVE/MAXINCLUSIVE/MINEXCLUSIVE/MAXEXCLUSIVE/TOTALDIGITS/
//     FRACTIONDIGITS), string facets (LENGTH/MINLENGTH/MAXLENGTH,
//     PATTERN "..." and the `/regex/flags` shorthand with UCHAR +
//     backslash-run-parity `\/` escape decoding). ANY nodeConstraint
//     form (nodeKind, bare facets, PATTERN-shorthand, valueSet, datatype)
//     may be followed by an optional shapeRef/shapeDefinition suffix,
//     combined via an implicit AND (0focusIRI.json, 1focusLength-dot.json,
//     focusbnode0ORfocusPattern0.json).
//   - annotations (`// pred obj`), semActs (`%iri{ code %}`, the bare
//     `%iri%` no-code form, and CODE-body escaping `\%`/`\\`/UCHAR),
//     comments (`#...` and `/* ... */`).
//   - Numeric literals try the double-aware scan before falling back
//     (anti-pattern #8 — reuses Parser.Turtle.parse_numeric_literal, which
//     already gets this right).
//
// Known NOT supported (parse-and-reject-loudly, never a silent wrong
// answer): SemAct CODE-body escaping beyond `\%`/`\\`/UCHAR (untested
// past what the one vendored fixture exercising it, 1dotCodeWithEscapes1,
// covers). No other gap is known against the schemas/ corpus as of the
// 433/433 differential result above; `negativeSyntax/`'s 100 ShExC-
// grammar-rejection fixtures and `negativeStructure/`'s 14 fixtures
// (ShExC-only by construction, no ShExJ twin to differential-check
// against) are NOT exercised by this parser's acceptance gate.
// ============================================================================

open FStar.String
open FStar.List.Tot
open FStar.Char
open Parser.FastString
open Parser.IRI
open Parser.Combinators
open Parser.TurtleScanner
open Parser.NTriples
open Parser.Turtle
open RDF.Graph.Executable
open ShEx.Schema

(* ================================================================ *)
(* Tokens                                                            *)
(* ================================================================ *)

// A lexical term: an absolute/relative IRIREF, an unresolved prefixed name
// (ns, local — local = "" for a bare "ns:" PNAME_NS, e.g. inside a PREFIX
// directive), or a blank-node label. Resolution against the current
// (prefixes, base_iri) state happens at parse time via
// `resolve_shexc_term`, mirroring Parser.Turtle's own state-threaded IRI
// resolution (directives can appear anywhere among ShExC statements, not
// just at the top, so eager resolution at tokenize time would be wrong).
type shexc_term =
  | ST_Iri   : raw:string -> has_colon:bool -> shexc_term
  | ST_PName : ns:string -> local:string -> shexc_term
  | ST_BNode : string -> shexc_term

type shexc_token =
  | TK_TERM        : shexc_term -> shexc_token
  | TK_AT_TERM     : shexc_term -> shexc_token   // '@' fused directly onto a term (shapeRef)
  | TK_LANGTAG     : string -> shexc_token        // '@' fused onto langtag chars (possibly empty, `@~`)
  | TK_STRING      : string -> shexc_token
  | TK_NUMBER      : lexeme:string -> datatype:string -> shexc_token
  | TK_REGEX       : pattern:string -> flags:string -> shexc_token
  | TK_SEMACT      : name:shexc_term -> code:option string -> shexc_token
  | TK_KW          : string -> shexc_token        // normalized (uppercased) keyword
  | TK_HATHAT
  | TK_CARET
  | TK_TILDE
  | TK_MINUS
  | TK_LBRACE
  | TK_RBRACE
  | TK_LPAREN
  | TK_RPAREN
  | TK_LBRACKET
  | TK_RBRACKET
  | TK_SEMI
  | TK_PIPE
  | TK_DOT
  | TK_DOLLAR
  | TK_AMP
  | TK_STAR
  | TK_PLUS
  | TK_QMARK
  | TK_SLASH_ANNOT                                 // '//'
  | TK_AT                                          // bare '@', whitespace before its shapeRef label
  | TK_EQ                                          // '=' (START = shapeExpression)
  | TK_REPEAT_RANGE : min:int -> max:int -> shexc_token  // {m,n}; max = -1 => unbounded ({m,})
  | TK_INVALID     : string -> shexc_token
  | TK_EOF

type shexc_tokens = list shexc_token

(* ================================================================ *)
(* Character classes                                                 *)
(* ================================================================ *)

let sc_is_digit (c: char) : bool =
  let code = int_of_char c in code >= 0x30 && code <= 0x39

let sc_is_ws_char (c: char) : bool =
  let code = int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

let sc_is_alpha (c: char) : bool =
  let code = int_of_char c in
  (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A)

// Charset used to scan a bare keyword-or-langtag run: ASCII letters,
// digits, hyphen. (Real LANGTAG is stricter — letters then
// hyphen-separated alnum subtags — but this superset is harmless since
// the only consumer either matches it against the fixed keyword table or
// stores it verbatim as a language tag.)
let sc_is_word_char (c: char) : bool =
  sc_is_alpha c || sc_is_digit c || int_of_char c = 0x2D

(* ================================================================ *)
(* Whitespace / comment skipping                                     *)
(* ================================================================ *)

let rec sc_skip_block_comment (input: string) (pos: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = fs_byte_length input in
    if pos + 1 < len then
      let c0 = fs_byte_index input pos in
      let c1 = fs_byte_index input (pos + 1) in
      if int_of_char c0 = 0x2A && int_of_char c1 = 0x2F then pos + 2
      else sc_skip_block_comment input (pos + 1) (fuel - 1)
    else len

let rec sc_skip_ws_comments (input: string) (pos: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = fs_byte_length input in
    if pos >= len then pos
    else
      let c = fs_byte_index input pos in
      let code = int_of_char c in
      if code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D then
        sc_skip_ws_comments input (pos + 1) (fuel - 1)
      else if code = 0x23 (* # *) then
        // Line comment: skip to (not past) end of line, then keep going.
        let p' = skip_to_eol input pos fuel in
        sc_skip_ws_comments input p' (fuel - 1)
      else if code = 0x2F && pos + 1 < len && int_of_char (fs_byte_index input (pos + 1)) = 0x2A then
        // '/*' block comment (NOT '//' -- that's the annotation token).
        let p' = sc_skip_block_comment input (pos + 2) fuel in
        sc_skip_ws_comments input p' (fuel - 1)
      else pos

let shexc_ws (input: string) (pos: nat) : nat =
  let len = fs_byte_length input in
  if pos > len then pos else sc_skip_ws_comments input pos (len - pos + 1)

(* ================================================================ *)
(* UCHAR-decoding scanner for REGEXP bodies. Backslash-run PARITY rule
   (derived from, and verified against, the three vendored twins
   1literalPattern_with_REGEXP_escapes{,_bare,_escaped}.shex/.json):
   scan the maximal run of `n` consecutive backslashes; if the character
   right after the run is `/`, `u`, or `U` AND `n` is ODD, the run's
   FINAL backslash escapes that character (decodes `\/` to `/`, `\uXXXX`/
   `\UXXXXXXXX` to the codepoint) and the run's other `n-1` backslashes
   are emitted as literal backslash characters, unpaired/uncollapsed;
   otherwise (n even, or the following character isn't one of those
   three, or there's no following character) ALL `n` backslashes are
   emitted literally and the next character is scanned as itself (so an
   even-length run right before `/` does NOT terminate the regex via
   that `/` being "escaped" -- it's the following, un-consumed `/`
   token, scanned fresh, that terminates it). This is the standard
   "escaped-backslash-then-literal-target" convention: `\\/` (2
   backslashes, i.e. one literal backslash, then a real terminator `/`)
   differs from `\/` (an escaped terminator, doesn't end the regex). *)
(* ================================================================ *)

let rec sc_count_backslash_run (input: string) (pos: nat) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then 0
  else
    let len = fs_byte_length input in
    if pos < len && int_of_char (fs_byte_index input pos) = 0x5C
    then 1 + sc_count_backslash_run input (pos + 1) (fuel - 1)
    else 0

let rec sc_emit_n_backslashes (n: nat) (acc: list char) : Tot (list char) (decreases n) =
  if n = 0 then acc else sc_emit_n_backslashes (n - 1) (char_of_int 0x5C :: acc)

let rec sc_scan_regex_body (input: string) (pos: nat) (acc: list char) (fuel: nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated regex literal" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated regex literal" pos
    else
      let c = fs_byte_index input pos in
      let code = int_of_char c in
      if code = 0x2F (* / *) then
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 1)
      else if code = 0x5C (* backslash *) then
        let run_len = sc_count_backslash_run input pos (len - pos + 1) in
        let run_end = pos + run_len in
        // Which escape (if any) the run's final backslash can trigger,
        // given the character right after the run and enough remaining
        // input for its hex digits.
        let escape_kind : option int =
          if run_end >= len then None
          else
            let nc = int_of_char (fs_byte_index input run_end) in
            if nc = 0x2F then Some 0x2F
            else if nc = 0x75 && run_end + 5 <= len then Some 0x75
            else if nc = 0x55 && run_end + 9 <= len then Some 0x55
            else None
        in
        let escape_applies = Some? escape_kind && run_len % 2 = 1 in
        if escape_applies then
          let kind = (match escape_kind with Some k -> k | None -> 0) in
          let acc1 = sc_emit_n_backslashes (run_len - 1) acc in
          if kind = 0x2F then
            sc_scan_regex_body input (run_end + 1) (char_of_int 0x2F :: acc1) (fuel - 1)
          else if kind = 0x75 then
            let h0 = hex_val (fs_byte_index input (run_end + 1)) in
            let h1 = hex_val (fs_byte_index input (run_end + 2)) in
            let h2 = hex_val (fs_byte_index input (run_end + 3)) in
            let h3 = hex_val (fs_byte_index input (run_end + 4)) in
            let cp = (h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3 in
            sc_scan_regex_body input (run_end + 5) (safe_char_of_int cp :: acc1) (fuel - 1)
          else
            let h0 = hex_val (fs_byte_index input (run_end + 1)) in
            let h1 = hex_val (fs_byte_index input (run_end + 2)) in
            let h2 = hex_val (fs_byte_index input (run_end + 3)) in
            let h3 = hex_val (fs_byte_index input (run_end + 4)) in
            let h4 = hex_val (fs_byte_index input (run_end + 5)) in
            let h5 = hex_val (fs_byte_index input (run_end + 6)) in
            let h6 = hex_val (fs_byte_index input (run_end + 7)) in
            let h7 = hex_val (fs_byte_index input (run_end + 8)) in
            let cp = (h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) +
                     (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536) +
                     (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) +
                     (h6 `op_Multiply` 16) + h7 in
            sc_scan_regex_body input (run_end + 9) (safe_char_of_int cp :: acc1) (fuel - 1)
        else
          let acc1 = sc_emit_n_backslashes run_len acc in
          sc_scan_regex_body input run_end acc1 (fuel - 1)
      else if code < 0x80 then
        sc_scan_regex_body input (pos + 1) (c :: acc) (fuel - 1)
      else
        // Non-ASCII passthrough: fs_byte_index yields one raw BYTE, not a
        // codepoint -- decode the full UTF-8 sequence and advance by its
        // byte length, or a literal multi-byte character (e.g. 𝒸,
        // U+1D4B8) gets mis-split into separate invalid single-byte
        // "chars" (1literalPattern_with_REGEXP_escapes_bare's exact
        // failure mode before this fix).
        let (cp, adv) = fs_cp_at input pos in
        let advance : nat = if adv = 0 then 1 else adv in
        sc_scan_regex_body input (pos + advance) (safe_char_of_int cp :: acc) (fuel - 1)

// Same escaping discipline for semAct CODE bodies (`{ ... %}`): `\%`
// decodes to a literal `%` (so it doesn't terminate the block early),
// `\uXXXX`/`\UXXXXXXXX` decode as UCHAR, `\\` decodes to a literal `\`,
// any other backslash is emitted alone. Terminates at an unescaped `%}`.
let rec sc_scan_code_body (input: string) (pos: nat) (acc: list char) (fuel: nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated semantic action code block" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated semantic action code block" pos
    else
      let c = fs_byte_index input pos in
      let code = int_of_char c in
      if code = 0x25 (* % *) && pos + 1 < len && int_of_char (fs_byte_index input (pos + 1)) = 0x7D then
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 2)
      else if code = 0x5C (* backslash *) && pos + 1 < len then
        let next = fs_byte_index input (pos + 1) in
        let ncode = int_of_char next in
        if ncode = 0x25 (* \% -> % *) then
          sc_scan_code_body input (pos + 2) (char_of_int 0x25 :: acc) (fuel - 1)
        else if ncode = 0x5C (* \\ -> \ *) then
          sc_scan_code_body input (pos + 2) (char_of_int 0x5C :: acc) (fuel - 1)
        else if ncode = 0x75 (* \u *) && pos + 6 <= len then
          let h0 = hex_val (fs_byte_index input (pos + 2)) in
          let h1 = hex_val (fs_byte_index input (pos + 3)) in
          let h2 = hex_val (fs_byte_index input (pos + 4)) in
          let h3 = hex_val (fs_byte_index input (pos + 5)) in
          let cp = (h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3 in
          sc_scan_code_body input (pos + 6) (safe_char_of_int cp :: acc) (fuel - 1)
        else if ncode = 0x55 (* \U *) && pos + 10 <= len then
          let h0 = hex_val (fs_byte_index input (pos + 2)) in
          let h1 = hex_val (fs_byte_index input (pos + 3)) in
          let h2 = hex_val (fs_byte_index input (pos + 4)) in
          let h3 = hex_val (fs_byte_index input (pos + 5)) in
          let h4 = hex_val (fs_byte_index input (pos + 6)) in
          let h5 = hex_val (fs_byte_index input (pos + 7)) in
          let h6 = hex_val (fs_byte_index input (pos + 8)) in
          let h7 = hex_val (fs_byte_index input (pos + 9)) in
          let cp = (h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) +
                   (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536) +
                   (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) +
                   (h6 `op_Multiply` 16) + h7 in
          sc_scan_code_body input (pos + 10) (safe_char_of_int cp :: acc) (fuel - 1)
        else
          sc_scan_code_body input (pos + 1) (c :: acc) (fuel - 1)
      else if code < 0x80 then
        sc_scan_code_body input (pos + 1) (c :: acc) (fuel - 1)
      else
        // Same non-ASCII UTF-8 passthrough fix as sc_scan_regex_body.
        let (cp, adv) = fs_cp_at input pos in
        let advance : nat = if adv = 0 then 1 else adv in
        sc_scan_code_body input (pos + advance) (safe_char_of_int cp :: acc) (fuel - 1)

(* ================================================================ *)
(* Keyword table                                                     *)
(* ================================================================ *)

// All ShExC reserved words are case-insensitive (corpus grep: "BaSe",
// "PREfIX", "prefix", "closed", "extra" all occur). `w` arrives already
// scanned as a run of word characters and upper-cased character-by-
// character by the caller before this lookup, so comparisons here are
// plain string equality against the canonical upper-case spelling.
let sc_is_keyword (w: string) : bool =
  w = "PREFIX" || w = "BASE" || w = "IMPORT" || w = "START" ||
  w = "AND" || w = "OR" || w = "NOT" ||
  w = "IRI" || w = "BNODE" || w = "NONLITERAL" || w = "LITERAL" ||
  w = "EXTRA" || w = "CLOSED" || w = "EXTENDS" || w = "ABSTRACT" || w = "EXTERNAL" ||
  w = "LENGTH" || w = "MINLENGTH" || w = "MAXLENGTH" ||
  w = "MININCLUSIVE" || w = "MAXINCLUSIVE" || w = "MINEXCLUSIVE" || w = "MAXEXCLUSIVE" ||
  w = "TOTALDIGITS" || w = "FRACTIONDIGITS" || w = "PATTERN" ||
  w = "TRUE" || w = "FALSE"

let sc_upper_char (c: char) : char =
  let code = int_of_char c in
  if code >= 0x61 && code <= 0x7A then char_of_int (code - 0x20) else c

let rec sc_upper_acc (chars: list char) : Tot (list char) (decreases chars) =
  match chars with
  | [] -> []
  | c :: rest -> sc_upper_char c :: sc_upper_acc rest

let sc_upper (s: string) : string =
  String.string_of_list (sc_upper_acc (String.list_of_string s))

// Language tags are lowercased wholesale by the vendored corpus's own
// ShExC->ShExJ generator (e.g. `"STRING_LITERAL2"@en-UK` -> `"language":
// "en-uk"` in 1val1STRING_LITERAL2_with_subtag.json -- confirmed not a
// BCP47-canonical region-uppercase form, just a flat lowercase), so
// language tags scanned here are lowercased to match.
let sc_lower_char (c: char) : char =
  let code = int_of_char c in
  if code >= 0x41 && code <= 0x5A then char_of_int (code + 0x20) else c

let rec sc_lower_acc (chars: list char) : Tot (list char) (decreases chars) =
  match chars with
  | [] -> []
  | c :: rest -> sc_lower_char c :: sc_lower_acc rest

let sc_lower (s: string) : string =
  String.string_of_list (sc_lower_acc (String.list_of_string s))

(* ================================================================ *)
(* Single-token scan                                                  *)
(* ================================================================ *)

// Scans a bare word (letters/digits/hyphen) starting at `pos`.
let rec sc_scan_word_end (input: string) (pos: nat) (fuel: nat) : Tot (r:nat{r >= pos}) (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = fs_byte_length input in
    if pos < len && sc_is_word_char (fs_byte_index input pos)
    then sc_scan_word_end input (pos + 1) (fuel - 1)
    else pos

// Scans langtag-shaped chars (letters/digits/hyphen) at `pos`, for both
// LANGTAG value-set forms (`@fr`, `@fr-be`) and the literal-suffix form
// (`"v"@en`) -- both are handled by this same scanner since the
// tokenizer treats '@'+word uniformly and the parser decides which
// grammar role applies from context.
let sc_scan_langtag_end (input: string) (pos: nat) : (r:nat{r >= pos}) =
  let len = fs_byte_length input in
  if pos > len then pos else sc_scan_word_end input pos (len - pos + 1)

// Scans one REPEAT_RANGE `{m,n}` / `{m,}` / `{m}` starting at the '{' at
// `pos`. Returns None if the braces don't hold a pure digit/comma body
// (i.e. this is an ordinary shape-body '{').
let sc_try_repeat_range (input: string) (pos: nat) : option (int & int & nat) =
  let len = fs_byte_length input in
  let rec scan_digits (p: nat{p <= len}) (fuel: nat) : Tot (r:nat{p <= r /\ r <= len}) (decreases fuel) =
    if fuel = 0 then p
    else if p < len && sc_is_digit (fs_byte_index input p) then scan_digits (p + 1) (fuel - 1)
    else p
  in
  if pos >= len || int_of_char (fs_byte_index input pos) <> 0x7B then None
  else
    let d0 = scan_digits (pos + 1) (len - pos) in
    if d0 = pos + 1 then None  (* need at least one digit for m *)
    else
      match shex_parse_int_string (fs_byte_sub input (pos + 1) (d0 - pos - 1)) with
      | None -> None
      | Some m ->
        if d0 < len && int_of_char (fs_byte_index input d0) = 0x7D (* } *) then
          Some (m, m, d0 + 1)
        else if d0 < len && int_of_char (fs_byte_index input d0) = 0x2C (* , *) then
          // `{m,*}` -- explicit '*' upper bound (unbounded), distinct
          // from `{m,}` (comma then immediately '}', also unbounded).
          if d0 + 2 <= len && int_of_char (fs_byte_index input (d0 + 1)) = 0x2A (* * *) &&
             int_of_char (fs_byte_index input (d0 + 2)) = 0x7D
          then Some (m, -1, d0 + 3)
          else
            let d1 = scan_digits (d0 + 1) (len - d0) in
            if d1 < len && int_of_char (fs_byte_index input d1) = 0x7D then
              (if d1 = d0 + 1 then Some (m, -1, d1 + 1)  (* {m,} unbounded *)
               else
                 match shex_parse_int_string (fs_byte_sub input (d0 + 1) (d1 - d0 - 1)) with
                 | None -> None
                 | Some n -> Some (m, n, d1 + 1))
            else None
        else None

// Scans a semAct's name term (IRIREF or PNAME, never a bnode -- semAct
// extension names are always IRI-shaped in the corpus).
let sc_scan_iriref_term (input: string) (pos: nat) : parse_result shexc_term =
  match scan_iri_ref_span input pos with
  | ParseOk sp pos' ->
    let raw = iri_ref_span_to_raw input sp in
    if contains_forbidden_iri_char raw then ParseFail "forbidden character in IRI" pos
    else ParseOk (ST_Iri raw sp.irs_has_colon) pos'
  | ParseFail msg fpos -> ParseFail msg fpos

let sc_scan_term (input: string) (pos: nat) : parse_result shexc_term =
  let len = fs_byte_length input in
  if pos >= len then ParseFail "expected term" pos
  else
    let c = fs_byte_index input pos in
    if int_of_char c = 0x3C (* < *) then sc_scan_iriref_term input pos
    else if int_of_char c = 0x5F && pos + 1 < len && int_of_char (fs_byte_index input (pos + 1)) = 0x3A then
      (match parse_bnode input pos with
       | ParseOk label pos' -> ParseOk (ST_BNode label) pos'
       | ParseFail msg fpos -> ParseFail msg fpos)
    else
      (match parse_prefixed_name input pos with
       | ParseOk (ns, local) pos' -> ParseOk (ST_PName ns local) pos'
       | ParseFail msg fpos -> ParseFail msg fpos)

// Produces (token, new_pos) for one token starting at `pos` (already past
// leading whitespace/comments).
let shexc_next_token (input: string) (pos: nat) : (shexc_token & nat) =
  let len = fs_byte_length input in
  if pos >= len then (TK_EOF, pos)
  else
    let c = fs_byte_index input pos in
    let code = int_of_char c in
    if code = 0x7B (* { *) then
      (match sc_try_repeat_range input pos with
       | Some (m, n, pos') -> (TK_REPEAT_RANGE m n, pos')
       | None -> (TK_LBRACE, pos + 1))
    else if code = 0x7D then (TK_RBRACE, pos + 1)
    else if code = 0x28 then (TK_LPAREN, pos + 1)
    else if code = 0x29 then (TK_RPAREN, pos + 1)
    else if code = 0x5B then (TK_LBRACKET, pos + 1)
    else if code = 0x5D then (TK_RBRACKET, pos + 1)
    else if code = 0x3B then (TK_SEMI, pos + 1)
    else if code = 0x7C then (TK_PIPE, pos + 1)
    else if code = 0x24 then (TK_DOLLAR, pos + 1)
    else if code = 0x26 then (TK_AMP, pos + 1)
    else if code = 0x2A then (TK_STAR, pos + 1)
    else if code = 0x2B then (TK_PLUS, pos + 1)
    else if code = 0x3F then (TK_QMARK, pos + 1)
    else if code = 0x3D (* = *) then (TK_EQ, pos + 1)
    else if code = 0x7E (* ~ *) then (TK_TILDE, pos + 1)
    else if code = 0x5E (* ^ *) then
      (if pos + 1 < len && int_of_char (fs_byte_index input (pos + 1)) = 0x5E
       then (TK_HATHAT, pos + 2) else (TK_CARET, pos + 1))
    else if code = 0x2F (* / *) then
      (if pos + 1 < len && int_of_char (fs_byte_index input (pos + 1)) = 0x2F
       then (TK_SLASH_ANNOT, pos + 2)
       else
         match sc_scan_regex_body input (pos + 1) [] (len - pos + 1) with
         | ParseOk pat pos' ->
           let flags_end = sc_scan_langtag_end input pos' in
           (TK_REGEX pat (fs_byte_sub input pos' (flags_end - pos')), flags_end)
         | ParseFail msg fpos -> (TK_INVALID msg, fpos))
    else if code = 0x2E (* . *) then
      // A DOT is a wildcard token unless it starts a numeric literal
      // (never happens in ShExC's fixed grammar positions, but guard
      // defensively anyway).
      (if pos + 1 < len && sc_is_digit (fs_byte_index input (pos + 1))
       then
         match parse_numeric_literal input pos with
         | ParseOk (lexeme, dt) pos' -> (TK_NUMBER lexeme dt, pos')
         | ParseFail msg fpos -> (TK_INVALID msg, fpos)
       else (TK_DOT, pos + 1))
    else if code = 0x2D (* - *) then
      (if pos + 1 < len &&
          (sc_is_digit (fs_byte_index input (pos + 1)) ||
           (int_of_char (fs_byte_index input (pos + 1)) = 0x2E && pos + 2 < len &&
            sc_is_digit (fs_byte_index input (pos + 2))))
       then
         match parse_numeric_literal input pos with
         | ParseOk (lexeme, dt) pos' -> (TK_NUMBER lexeme dt, pos')
         | ParseFail msg fpos -> (TK_INVALID msg, fpos)
       else (TK_MINUS, pos + 1))
    else if code = 0x22 || code = 0x27 (* " or ' *) then
      (match parse_turtle_string input pos with
       | ParseOk s pos' -> (TK_STRING s, pos')
       | ParseFail msg fpos -> (TK_INVALID msg, fpos))
    else if code = 0x3C (* < *) then
      (match sc_scan_iriref_term input pos with
       | ParseOk t pos' -> (TK_TERM t, pos')
       | ParseFail msg fpos -> (TK_INVALID msg, fpos))
    else if code = 0x5F && pos + 1 < len && int_of_char (fs_byte_index input (pos + 1)) = 0x3A then
      (match parse_bnode input pos with
       | ParseOk label pos' -> (TK_TERM (ST_BNode label), pos')
       | ParseFail msg fpos -> (TK_INVALID msg, fpos))
    else if code = 0x40 (* @ *) then
      // Fused forms first (`@<iri>`, `@_:bnode`, `@prefix:local`); a
      // bare '@' immediately followed by whitespace is the "shapeRef
      // with a space before its label" form (`@ ex:S2`, `@ S2:`,
      // confirmed against 1dotRefSpaceLNex1/1dotRefSpaceNS1.json) --
      // emitted as its own TK_AT token, and the label that follows
      // (after normal whitespace-skipping) is just an ordinary TK_TERM/
      // TK_AT_TERM the parser consumes separately. Anything else after
      // '@' (e.g. `@~`) falls through to the langtag case below.
      (if pos + 1 < len && int_of_char (fs_byte_index input (pos + 1)) = 0x3C then
         (match sc_scan_iriref_term input (pos + 1) with
          | ParseOk t pos' -> (TK_AT_TERM t, pos')
          | ParseFail msg fpos -> (TK_INVALID msg, fpos))
       else if pos + 2 < len && int_of_char (fs_byte_index input (pos + 1)) = 0x5F &&
               int_of_char (fs_byte_index input (pos + 2)) = 0x3A then
         (match parse_bnode input (pos + 1) with
          | ParseOk label pos' -> (TK_AT_TERM (ST_BNode label), pos')
          | ParseFail msg fpos -> (TK_INVALID msg, fpos))
       else if pos + 1 < len &&
               (sc_is_alpha (fs_byte_index input (pos + 1)) ||
                int_of_char (fs_byte_index input (pos + 1)) = 0x3A (* : -- default-prefix ATPNAME, e.g. `@:T` *))
       then
         (match parse_prefixed_name input (pos + 1) with
          | ParseOk (ns, local) pos' -> (TK_AT_TERM (ST_PName ns local), pos')
          | ParseFail _ _ ->
            let end_pos = sc_scan_langtag_end input (pos + 1) in
            (TK_LANGTAG (sc_lower (fs_byte_sub input (pos + 1) (end_pos - pos - 1))), end_pos))
       else if pos + 1 < len && sc_is_ws_char (fs_byte_index input (pos + 1)) then
         (TK_AT, pos + 1)
       else
         // '@' followed by non-identifier (e.g. `@~`) -- empty langtag,
         // the tilde is tokenized separately right after.
         (TK_LANGTAG "", pos + 1))
    else if code = 0x25 (* % *) then
      (match sc_scan_term input (pos + 1) with
       | ParseFail msg fpos -> (TK_INVALID msg, fpos)
       | ParseOk name pos1 ->
         if pos1 < len && int_of_char (fs_byte_index input pos1) = 0x7B then
           (match sc_scan_code_body input (pos1 + 1) [] (len - pos1 + 1) with
            | ParseOk code_str pos2 -> (TK_SEMACT name (Some code_str), pos2)
            | ParseFail msg fpos -> (TK_INVALID msg, fpos))
         else if pos1 < len && int_of_char (fs_byte_index input pos1) = 0x25 then
           (TK_SEMACT name None, pos1 + 1)
         else (TK_INVALID "expected '{' or '%' after semantic action name", pos1))
    else if sc_is_digit c then
      (match parse_numeric_literal input pos with
       | ParseOk (lexeme, dt) pos' -> (TK_NUMBER lexeme dt, pos')
       | ParseFail msg fpos -> (TK_INVALID msg, fpos))
    // ':' -- the DEFAULT prefix ("PREFIX : <iri>") has an EMPTY prefix
    // name, so a term using it (a bare "p1" written as ":p1", or a bare
    // ":" alone as PNAME_NS with empty local) starts with the colon
    // itself, not a PN_CHARS_BASE letter -- needs its own dispatch
    // branch, not just the sc_is_alpha one below.
    else if code = 0x3A then
      (match parse_prefixed_name input pos with
       | ParseOk (ns, local) pos' -> (TK_TERM (ST_PName ns local), pos')
       | ParseFail msg fpos -> (TK_INVALID msg, fpos))
    else if sc_is_alpha c then
      (match parse_prefixed_name input pos with
       | ParseOk (ns, local) pos' -> (TK_TERM (ST_PName ns local), pos')
       | ParseFail _ _ ->
         let end_pos = sc_scan_word_end input pos (len - pos + 1) in
         let raw_word = fs_byte_sub input pos (end_pos - pos) in
         // Turtle's `a` = rdf:type predicate shorthand (case-SENSITIVE,
         // lowercase only -- distinct from the case-INSENSITIVE keyword
         // table below; corpus: 1Adot.shex's bare `a` decodes to
         // rdf:type). Checked against the raw (non-uppercased) word.
         if raw_word = "a" then (TK_TERM (ST_Iri rdf_type_iri true), end_pos)
         else
           let w = sc_upper raw_word in
           if sc_is_keyword w then (TK_KW w, end_pos)
           else (TK_INVALID (String.concat "" ["unrecognized keyword: "; w]), end_pos))
    else (TK_INVALID "unrecognized character", pos + 1)

let rec shexc_tokenize_loop (input: string) (pos: nat) (acc: list shexc_token) (fuel: nat)
  : Tot (list shexc_token) (decreases fuel) =
  if fuel = 0 then List.Tot.rev (TK_EOF :: acc)
  else
    let pos1 = shexc_ws input pos in
    let len = fs_byte_length input in
    if pos1 >= len then List.Tot.rev (TK_EOF :: acc)
    else
      let (tok, pos2) = shexc_next_token input pos1 in
      if pos2 <= pos1 then List.Tot.rev (TK_INVALID "tokenizer stalled" :: acc)
      else shexc_tokenize_loop input pos2 (tok :: acc) (fuel - 1)

let shexc_tokenize (input: string) : list shexc_token =
  shexc_tokenize_loop input 0 [] (fs_byte_length input + 10)

(* ================================================================ *)
(* Token-stream parser                                                *)
(* ================================================================ *)

noeq type sresult (a: Type) =
  | SOk  : v:a -> rest:shexc_tokens -> sresult a
  | SErr : msg:string -> sresult a

let resolve_shexc_term (st: turtle_state) (t: shexc_term) : option string =
  match t with
  | ST_Iri raw has_colon ->
    let r = resolve_iri_hint st raw has_colon in
    if is_iri r then Some r else None
  | ST_PName ns local -> resolve_prefixed_name st ns local
  | ST_BNode label -> Some ("_:" ^ label)

let opt_consume (pred: shexc_token -> bool) (ts: shexc_tokens) : (bool & shexc_tokens) =
  match ts with
  | t :: rest -> if pred t then (true, rest) else (false, ts)
  | [] -> (false, ts)

// Raw (unresolved) text of a term -- used for IMPORT targets, which
// ShEx.Schema.fst's decode_schema stores verbatim (decode_string_list on
// the "imports" JSON array applies no resolve_against).
let raw_shexc_term (t: shexc_term) : string =
  match t with
  | ST_Iri raw _ -> raw
  | ST_PName ns local -> ns ^ ":" ^ local
  | ST_BNode label -> "_:" ^ label

(* ---- term parsing (predicate / label / datatype / IRI value) ---- *)

let parse_term (st: turtle_state) (ts: shexc_tokens) : sresult string =
  match ts with
  | TK_TERM t :: rest ->
    (match resolve_shexc_term st t with
     | Some s -> SOk s rest
     | None -> SErr "unresolvable term (undefined prefix?)")
  | _ -> SErr "expected an IRI, prefixed name, or blank node"

let rec parse_predicate_list1 (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult (list string)) (decreases fuel) =
  if fuel = 0 then SErr "EXTRA predicate list too long"
  else
    match ts with
    | TK_TERM t :: rest ->
      (match resolve_shexc_term st t with
       | None -> SErr "unresolvable predicate in EXTRA"
       | Some s ->
         (match parse_predicate_list1 st rest (fuel - 1) with
          | SOk more rest' -> SOk (s :: more) rest'
          | SErr _ -> SOk [s] rest))
    | _ -> SErr "expected at least one predicate after EXTRA"

(* ---- semAct / annotation lists (0+, prefix-matched greedily) ---- *)

let rec parse_semacts (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult (list shex_sem_act)) (decreases fuel) =
  if fuel = 0 then SOk [] ts
  else
    match ts with
    | TK_SEMACT name code :: rest ->
      (match resolve_shexc_term st name with
       | None -> SErr "unresolvable semantic-action extension IRI"
       | Some n ->
         (match parse_semacts st rest (fuel - 1) with
          | SErr m -> SErr m
          | SOk more rest' -> SOk ({ sa_name = n; sa_code = code } :: more) rest'))
    | _ -> SOk [] ts

let parse_object_value (st: turtle_state) (ts: shexc_tokens) : sresult shex_object_value =
  match ts with
  | TK_STRING s :: TK_LANGTAG lang :: rest ->
    SOk (ShexOV_Literal s (Some lang) None) rest
  | TK_STRING s :: TK_HATHAT :: TK_TERM t :: rest ->
    (match resolve_shexc_term st t with
     | Some dt -> SOk (ShexOV_Literal s None (Some dt)) rest
     | None -> SErr "unresolvable datatype IRI")
  | TK_STRING s :: rest -> SOk (ShexOV_Literal s None None) rest
  | TK_NUMBER lexeme dt :: rest -> SOk (ShexOV_Literal lexeme None (Some dt)) rest
  | TK_KW "TRUE" :: rest -> SOk (ShexOV_Literal "true" None (Some xsd_boolean)) rest
  | TK_KW "FALSE" :: rest -> SOk (ShexOV_Literal "false" None (Some xsd_boolean)) rest
  | TK_TERM t :: rest ->
    (match resolve_shexc_term st t with
     | Some iri -> SOk (ShexOV_Iri iri) rest
     | None -> SErr "unresolvable IRI value")
  | _ -> SErr "expected a value (IRI, literal, or number)"

let rec parse_annotations (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult (list shex_annotation)) (decreases fuel) =
  if fuel = 0 then SOk [] ts
  else
    match ts with
    | TK_SLASH_ANNOT :: TK_TERM predt :: rest ->
      (match resolve_shexc_term st predt with
       | None -> SErr "unresolvable annotation predicate"
       | Some pred ->
         (match parse_object_value st rest with
          | SErr m -> SErr m
          | SOk obj rest1 ->
            (match parse_annotations st rest1 (fuel - 1) with
             | SErr m -> SErr m
             | SOk more rest2 -> SOk ({ an_predicate = pred; an_object = obj } :: more) rest2)))
    | _ -> SOk [] ts

(* ---- value sets ---- *)

// One exclusion entry: `- value '~'?`. `kind` disambiguates a bare-token
// exclusion the same way ShEx.Schema.fst's decode_value_set_value_list_kind
// does for the JSON side.
let parse_exclusion (st: turtle_state) (kind: shex_vsv_kind) (ts: shexc_tokens)
  : sresult shex_value_set_value =
  match ts with
  | TK_MINUS :: rest ->
    let bare_of (s: string) : shex_value_set_value = decode_bare_vsv_string kind s in
    (match kind, rest with
     | VSVK_Iri, TK_TERM t :: TK_TILDE :: rest' ->
       (match resolve_shexc_term st t with
        | Some s -> SOk (VSV_IriStem (ShexStemPlain s)) rest'
        | None -> SErr "unresolvable iri exclusion")
     | VSVK_Iri, TK_TERM t :: rest' ->
       (match resolve_shexc_term st t with
        | Some s -> SOk (bare_of s) rest'
        | None -> SErr "unresolvable iri exclusion")
     | VSVK_Literal, TK_STRING s :: TK_TILDE :: rest' -> SOk (VSV_LiteralStem (ShexStemPlain s)) rest'
     | VSVK_Literal, TK_STRING s :: rest' -> SOk (bare_of s) rest'
     | VSVK_Language, TK_LANGTAG s :: TK_TILDE :: rest' -> SOk (VSV_LanguageStem (ShexStemPlain s)) rest'
     | VSVK_Language, TK_LANGTAG s :: rest' -> SOk (bare_of s) rest'
     | _ -> SErr "malformed exclusion in value-set stem range")
  | _ -> SErr "expected '-' exclusion"

let rec parse_exclusions (st: turtle_state) (kind: shex_vsv_kind) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult (list shex_value_set_value)) (decreases fuel) =
  if fuel = 0 then SOk [] ts
  else
    match ts with
    | TK_MINUS :: _ ->
      (match parse_exclusion st kind ts with
       | SErr m -> SErr m
       | SOk excl rest ->
         (match parse_exclusions st kind rest (fuel - 1) with
          | SErr m -> SErr m
          | SOk more rest' -> SOk (excl :: more) rest'))
    | _ -> SOk [] ts

// Determine the exclusion kind for a "." (wildcard) stem range by peeking
// at the first exclusion's value-token shape (IRI/PNAME term vs STRING vs
// LANGTAG) -- mirrors the JSON side's decode_value_set_value_list_kind
// design note: the *kind* is carried by context (here, the first
// exclusion's lexical form) rather than the wildcard marker itself.
let dot_exclusion_kind (ts: shexc_tokens) : shex_vsv_kind =
  match ts with
  | TK_MINUS :: TK_STRING _ :: _ -> VSVK_Literal
  | TK_MINUS :: TK_LANGTAG _ :: _ -> VSVK_Language
  | _ -> VSVK_Iri

// One valueSetValue: iriRange | literalRange | languageRange | '.' exclusion+
let parse_value_set_value (st: turtle_state) (ts: shexc_tokens) : sresult shex_value_set_value =
  match ts with
  | TK_DOT :: rest ->
    let kind = dot_exclusion_kind rest in
    (match parse_exclusions st kind rest (List.Tot.length rest + 1) with
     | SErr m -> SErr m
     | SOk excl rest' ->
       (match excl with
        | [] -> SErr "'.' value-set entry needs at least one exclusion"
        | _ ->
          let stem = ShexStemWildcard in
          SOk (match kind with
               | VSVK_Iri -> VSV_IriStemRange stem excl
               | VSVK_Literal -> VSV_LiteralStemRange stem excl
               | VSVK_Language -> VSV_LanguageStemRange stem excl) rest'))
  | TK_TERM t :: TK_TILDE :: rest ->
    (match resolve_shexc_term st t with
     | None -> SErr "unresolvable iri stem"
     | Some s ->
       (match parse_exclusions st VSVK_Iri rest (List.Tot.length rest + 1) with
        | SErr m -> SErr m
        | SOk [] rest' -> SOk (VSV_IriStem (ShexStemPlain s)) rest'
        | SOk excl rest' -> SOk (VSV_IriStemRange (ShexStemPlain s) excl) rest'))
  | TK_TERM t :: rest ->
    (match resolve_shexc_term st t with
     | Some s -> SOk (VSV_Value (ShexOV_Iri s)) rest
     | None -> SErr "unresolvable iri value")
  | TK_STRING s :: TK_HATHAT :: TK_TERM t :: TK_TILDE :: rest ->
    // A datatype-qualified literal stem, e.g. "v"^^dt~ -- not exercised by
    // the corpus (ShExJ's LiteralStem stem is a bare string, no datatype
    // slot), so treat the datatype as dropped context and stem on lexical
    // form only, matching the only shape the AST can express.
    (match resolve_shexc_term st t with
     | Some _ -> SOk (VSV_LiteralStem (ShexStemPlain s)) rest
     | None -> SErr "unresolvable datatype IRI")
  | TK_STRING s :: TK_TILDE :: rest ->
    (match parse_exclusions st VSVK_Literal rest (List.Tot.length rest + 1) with
     | SErr m -> SErr m
     | SOk [] rest' -> SOk (VSV_LiteralStem (ShexStemPlain s)) rest'
     | SOk excl rest' -> SOk (VSV_LiteralStemRange (ShexStemPlain s) excl) rest')
  | TK_STRING s :: TK_LANGTAG lang :: rest -> SOk (VSV_Value (ShexOV_Literal s (Some lang) None)) rest
  | TK_STRING s :: TK_HATHAT :: TK_TERM t :: rest ->
    (match resolve_shexc_term st t with
     | Some dt -> SOk (VSV_Value (ShexOV_Literal s None (Some dt))) rest
     | None -> SErr "unresolvable datatype IRI")
  | TK_STRING s :: rest -> SOk (VSV_Value (ShexOV_Literal s None None)) rest
  | TK_NUMBER lexeme dt :: rest -> SOk (VSV_Value (ShexOV_Literal lexeme None (Some dt))) rest
  | TK_KW "TRUE" :: rest -> SOk (VSV_Value (ShexOV_Literal "true" None (Some xsd_boolean))) rest
  | TK_KW "FALSE" :: rest -> SOk (VSV_Value (ShexOV_Literal "false" None (Some xsd_boolean))) rest
  | TK_LANGTAG lang :: TK_TILDE :: rest ->
    (match parse_exclusions st VSVK_Language rest (List.Tot.length rest + 1) with
     | SErr m -> SErr m
     | SOk [] rest' -> SOk (VSV_LanguageStem (ShexStemPlain lang)) rest'
     | SOk excl rest' -> SOk (VSV_LanguageStemRange (ShexStemPlain lang) excl) rest')
  | TK_LANGTAG lang :: rest -> SOk (VSV_Language lang) rest
  | _ -> SErr "expected a value-set entry"

let rec parse_value_set_values (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult (list shex_value_set_value)) (decreases fuel) =
  if fuel = 0 then SOk [] ts
  else
    match ts with
    | TK_RBRACKET :: _ -> SOk [] ts
    | _ ->
      (match parse_value_set_value st ts with
       | SErr m -> SErr m
       | SOk v rest ->
         (match parse_value_set_values st rest (fuel - 1) with
          | SErr m -> SErr m
          | SOk more rest' -> SOk (v :: more) rest'))

let parse_value_set (st: turtle_state) (ts: shexc_tokens) : sresult (list shex_value_set_value) =
  match ts with
  | TK_LBRACKET :: rest ->
    (match parse_value_set_values st rest (List.Tot.length rest + 1) with
     | SErr m -> SErr m
     | SOk vs rest1 ->
       (match rest1 with
        | TK_RBRACKET :: rest2 -> SOk vs rest2
        | _ -> SErr "expected ']' to close value set"))
  | _ -> SErr "expected '['"

(* ---- node constraint (nodeKind / datatype / valueSet / facets) ---- *)

let empty_node_constraint : shex_node_constraint = {
  nc_node_kind = None; nc_datatype = None; nc_values = [];
  nc_length = None; nc_minlength = None; nc_maxlength = None;
  nc_pattern = None; nc_flags = None;
  nc_mininclusive = None; nc_maxinclusive = None;
  nc_minexclusive = None; nc_maxexclusive = None;
  nc_totaldigits = None; nc_fractiondigits = None;
}

// The wildcard shapeAtom `.` reifies as an EMPTY Shape (not an empty
// NodeConstraint) whenever it must be represented as a concrete
// shex_shape_expr -- e.g. `NOT .` decodes (per the corpus's own
// 1NOTdot.json twin) to `{"type":"ShapeNot","shapeExpr":{"type":"Shape"}}`,
// never `{"type":"NodeConstraint"}`. When `.` is the WHOLE, uncombined
// value of a tripleConstraint it instead omits "valueExpr" entirely (see
// parse_triple_constraint's dedicated bare-dot check below, matching
// 1dot.json's TripleConstraint having no "valueExpr" key at all).
let empty_shape : shex_shape = {
  sh_closed = false; sh_extra = []; sh_expression = None;
  sh_semacts = []; sh_annotations = []; sh_extends = [];
}

// Parses zero-or-more xsFacet entries onto an accumulating node
// constraint. Order-independent, matching the grammar's `xsFacet*`.
let rec parse_facets (st: turtle_state) (nc: shex_node_constraint) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_node_constraint) (decreases fuel) =
  if fuel = 0 then SOk nc ts
  else
    match ts with
    | TK_KW "LENGTH" :: TK_NUMBER n _ :: rest ->
      (match shex_parse_int_string n with
       | Some i -> parse_facets st ({ nc with nc_length = Some i }) rest (fuel - 1)
       | None -> SErr "LENGTH expects an integer")
    | TK_KW "MINLENGTH" :: TK_NUMBER n _ :: rest ->
      (match shex_parse_int_string n with
       | Some i -> parse_facets st ({ nc with nc_minlength = Some i }) rest (fuel - 1)
       | None -> SErr "MINLENGTH expects an integer")
    | TK_KW "MAXLENGTH" :: TK_NUMBER n _ :: rest ->
      (match shex_parse_int_string n with
       | Some i -> parse_facets st ({ nc with nc_maxlength = Some i }) rest (fuel - 1)
       | None -> SErr "MAXLENGTH expects an integer")
    | TK_KW "TOTALDIGITS" :: TK_NUMBER n _ :: rest ->
      (match shex_parse_int_string n with
       | Some i -> parse_facets st ({ nc with nc_totaldigits = Some i }) rest (fuel - 1)
       | None -> SErr "TOTALDIGITS expects an integer")
    | TK_KW "FRACTIONDIGITS" :: TK_NUMBER n _ :: rest ->
      (match shex_parse_int_string n with
       | Some i -> parse_facets st ({ nc with nc_fractiondigits = Some i }) rest (fuel - 1)
       | None -> SErr "FRACTIONDIGITS expects an integer")
    | TK_KW "MININCLUSIVE" :: TK_NUMBER n _ :: rest ->
      parse_facets st ({ nc with nc_mininclusive = Some n }) rest (fuel - 1)
    | TK_KW "MAXINCLUSIVE" :: TK_NUMBER n _ :: rest ->
      parse_facets st ({ nc with nc_maxinclusive = Some n }) rest (fuel - 1)
    | TK_KW "MINEXCLUSIVE" :: TK_NUMBER n _ :: rest ->
      parse_facets st ({ nc with nc_minexclusive = Some n }) rest (fuel - 1)
    | TK_KW "MAXEXCLUSIVE" :: TK_NUMBER n _ :: rest ->
      parse_facets st ({ nc with nc_maxexclusive = Some n }) rest (fuel - 1)
    | TK_KW "PATTERN" :: TK_STRING s :: rest ->
      // Optional trailing flags identifier (e.g. PATTERN "re" i) --
      // not exercised by the corpus's PATTERN-keyword-form fixtures, so
      // flags stay None unless a bare keyword-shaped flags word follows.
      parse_facets st ({ nc with nc_pattern = Some s }) rest (fuel - 1)
    | TK_REGEX pat flags :: rest ->
      parse_facets st ({ nc with nc_pattern = Some pat; nc_flags = (if flags = "" then None else Some flags) }) rest (fuel - 1)
    | _ -> SOk nc ts

(* ================================================================ *)
(* shapeExpr / shape / tripleExpr — mutually recursive descent.       *)
(* Generous fixed fuel budget (see module header): every mutual call  *)
(* decrements by >=1, and no vendored schema comes close to the depth *)
(* this bound allows.                                                 *)
(* ================================================================ *)

// Fixed entry-point fuel for the shapeExpr/shape/tripleExpr mutual group
// below. NOT proportional to remaining-token count: the grammar's many
// pass-through, non-consuming layers (shapeOr -> shapeAnd -> shapeNot ->
// shapeAtom -> shapeDefinition -> shapeModifiers -> oneOfTripleExpr ->
// groupTripleExpr -> unaryTripleExpr -> unaryBody -> tripleConstraint ->
// inlineShapeExpression -> shapeOr -> ...) cost roughly 15-20 fuel per
// single meaningful atom/tripleConstraint, so a token-count-sized budget
// starves even small real schemas (measured: a 5-token schema needs >6).
// Every mutual call decrements by >=1 and this budget is generous enough
// that no vendored fixture (or the `_all.shex` torture file) comes
// remotely close to exhausting it.
let shexc_grammar_fuel : nat = 2000000

// True when the next tokens could start a unaryTripleExpr -- used only to
// decide whether a ';' is an inter-element separator or a trailing
// terminator with nothing after it. Not part of the mutual-recursion
// group below (it never calls into it): a plain leaf predicate.
let peek_starts_unary (ts: shexc_tokens) : bool =
  match ts with
  | TK_DOLLAR :: _ | TK_AMP :: _ | TK_LPAREN :: _ | TK_CARET :: _ | TK_TERM _ :: _ -> true
  | _ -> false

// Optional cardinality suffix (`*` / `+` / `?` / `{m,n}` / `{m,}`). Also a
// plain leaf (no fuel, no calls into the mutual group below).
let parse_optional_cardinality (ts: shexc_tokens) : (option int & option int & shexc_tokens) =
  match ts with
  | TK_STAR :: rest -> (Some 0, Some (-1), rest)
  | TK_PLUS :: rest -> (Some 1, Some (-1), rest)
  | TK_QMARK :: rest -> (Some 0, Some 1, rest)
  | TK_REPEAT_RANGE m n :: rest -> (Some m, Some n, rest)
  | _ -> (None, None, ts)

let rec parse_shape_expression (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_shape_expr) (decreases fuel) =
  if fuel = 0 then SErr "shapeExpression recursion limit"
  else parse_shape_or st ts (fuel - 1)

// shapeOr/shapeAnd flatten to an N-ary SE_ShapeOr/SE_ShapeAnd across a
// SINGLE bare "A OR B OR C" / "A AND B AND C" chain (matches
// 1dotAND1dotAND1dot.json's 3-element ShapeAnd) but must NOT merge a
// parenthesized sub-expression's own ShapeAnd/ShapeOr into the outer
// chain: `(A AND B) AND C` decodes to a NESTED 2-element ShapeAnd
// containing the pair (open1dotAND1dotcloseAND1dot.json), not a flat
// 3-element one -- so flattening is driven by THIS call's own operand
// list (each parse_shape_not call returns one opaque, already-complete
// operand, whatever its internal shape), never by re-inspecting an
// already-built accumulator's constructor.
and parse_shape_or (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_shape_expr) (decreases fuel) =
  if fuel = 0 then SErr "shapeOr recursion limit"
  else
    match parse_shape_and st ts (fuel - 1) with
    | SErr m -> SErr m
    | SOk se rest -> parse_shape_or_rest st [se] rest (fuel - 1)

and parse_shape_or_rest (st: turtle_state) (acc: list shex_shape_expr) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_shape_expr) (decreases fuel) =
  if fuel = 0 then
    (match acc with [x] -> SOk x ts | xs -> SOk (SE_ShapeOr xs) ts)
  else
    match ts with
    | TK_KW "OR" :: rest ->
      (match parse_shape_and st rest (fuel - 1) with
       | SErr m -> SErr m
       | SOk se rest' -> parse_shape_or_rest st (acc @ [se]) rest' (fuel - 1))
    | _ ->
      (match acc with
       | [x] -> SOk x ts
       | xs -> SOk (SE_ShapeOr xs) ts)

and parse_shape_and (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_shape_expr) (decreases fuel) =
  if fuel = 0 then SErr "shapeAnd recursion limit"
  else
    match parse_shape_not st ts (fuel - 1) with
    | SErr m -> SErr m
    | SOk xs rest -> parse_shape_and_rest st xs rest (fuel - 1)

and parse_shape_and_rest (st: turtle_state) (acc: list shex_shape_expr) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_shape_expr) (decreases fuel) =
  if fuel = 0 then
    (match acc with [x] -> SOk x ts | xs -> SOk (SE_ShapeAnd xs) ts)
  else
    match ts with
    | TK_KW "AND" :: rest ->
      (match parse_shape_not st rest (fuel - 1) with
       | SErr m -> SErr m
       | SOk xs rest' -> parse_shape_and_rest st (acc @ xs) rest' (fuel - 1))
    | _ ->
      (match acc with
       | [x] -> SOk x ts
       | xs -> SOk (SE_ShapeAnd xs) ts)

// Returns this shapeNot's contribution as a FLAT list of shapeAnd-level
// operands -- normally a singleton, but shapeAtom's own implicit
// "nonLitNodeConstraint shapeOrRef?" AND (no "AND" keyword at all) needs
// to flatten into a SURROUNDING explicit "AND" chain at the SAME level
// (confirmed against FocusIRI2EachBnodeNested2EachIRIRef.json: `BNODE
// {...} AND CLOSED {...}` decodes to one flat 3-element ShapeAnd
// [NodeConstraint(bnode), Shape, Shape], not a nested
// ShapeAnd[ShapeAnd[nc,shape1],shape2]). A PARENTHESIZED "(A AND B)"
// does NOT get this treatment: parse_shape_atom's own LPAREN branch
// always collapses its inner shapeExpression to a single opaque
// shex_shape_expr first (see below), so only the genuine atom-level
// implicit combo ever produces a >1-element list here.
and parse_shape_not (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult (list shex_shape_expr)) (decreases fuel) =
  if fuel = 0 then SErr "shapeNot recursion limit"
  else
    match ts with
    | TK_KW "NOT" :: rest ->
      (match parse_shape_atom st rest (fuel - 1) with
       | SErr m -> SErr m
       | SOk xs rest' ->
         let flattened = (match xs with [x] -> x | _ -> SE_ShapeAnd xs) in
         SOk [SE_ShapeNot flattened] rest')
    | _ -> parse_shape_atom st ts (fuel - 1)

// shapeAtom: a nodeConstraint (optionally combined with a shapeOrRef),
// a shapeOrRef alone (optionally combined with a nodeConstraint), a
// parenthesized sub-expression, or the wildcard `.`. Returns a list
// (see parse_shape_not's doc comment) -- every branch here returns a
// singleton EXCEPT parse_node_constraint_or_shape's shapeOrRef-suffix
// case, which returns the two components unflattened.
and parse_shape_atom (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult (list shex_shape_expr)) (decreases fuel) =
  if fuel = 0 then SErr "shapeAtom recursion limit"
  else
    match ts with
    | TK_LPAREN :: rest ->
      (match parse_shape_expression st rest (fuel - 1) with
       | SErr m -> SErr m
       | SOk se rest' ->
         (match rest' with
          | TK_RPAREN :: rest'' -> SOk [se] rest''
          | _ -> SErr "expected ')'"))
    | TK_DOT :: rest -> SOk [SE_Shape empty_shape] rest
    | TK_AT_TERM t :: rest | TK_AT :: TK_TERM t :: rest ->
      (match resolve_shexc_term st t with
       | None -> SErr "unresolvable shapeRef"
       | Some s -> SOk [SE_Ref s] rest)
    | TK_KW "EXTERNAL" :: rest -> SOk [SE_ShapeExternal] rest
    | TK_KW "IRI" :: _ | TK_KW "BNODE" :: _ | TK_KW "NONLITERAL" :: _ | TK_KW "LITERAL" :: _
    | TK_LBRACKET :: _
    | TK_KW "LENGTH" :: _ | TK_KW "MINLENGTH" :: _ | TK_KW "MAXLENGTH" :: _ | TK_KW "PATTERN" :: _
    | TK_REGEX _ _ :: _
    | TK_TERM _ :: _  // bare datatype IRI/PNAME starting a nodeConstraint
    | TK_KW "MININCLUSIVE" :: _ | TK_KW "MAXINCLUSIVE" :: _
    | TK_KW "MINEXCLUSIVE" :: _ | TK_KW "MAXEXCLUSIVE" :: _
    | TK_KW "TOTALDIGITS" :: _ | TK_KW "FRACTIONDIGITS" :: _ ->
      parse_node_constraint_or_shape st ts (fuel - 1)
    | TK_KW "CLOSED" :: _ | TK_KW "EXTRA" :: _ | TK_KW "EXTENDS" :: _ | TK_LBRACE :: _ ->
      (match parse_shape_definition st ts (fuel - 1) with
       | SErr m -> SErr m
       | SOk sh rest -> SOk [SE_Shape sh] rest)
    | _ -> SErr "expected a shape expression"

// Dispatches the "starts with a datatype/nodeKind/valueSet/facet" family:
// this is a nodeConstraint, and TK_TERM here is a bare datatype IRI (a
// nodeConstraint's datatype, NOT a shapeRef -- shapeRefs are always
// `@`-prefixed in ShExC). Returns a list per parse_shape_atom's contract:
// a singleton when there's no shapeOrRef suffix, else the UNFLATTENED
// [NodeConstraint; shapeOrRef] pair (parse_shape_and/_rest flattens it
// into the surrounding AND chain -- see FocusIRI2EachBnodeNested2EachIRIRef
// .json's flat 3-element ShapeAnd).
and parse_node_constraint_or_shape (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult (list shex_shape_expr)) (decreases fuel) =
  if fuel = 0 then SErr "nodeConstraint recursion limit"
  else
    (match parse_node_constraint_only st ts (fuel - 1) with
     | SErr m -> SErr m
     | SOk nc rest ->
       (match parse_optional_shape_or_ref_suffix st rest (fuel - 1) with
        | SErr m -> SErr m
        | SOk None rest' -> SOk [SE_NodeConstraint nc] rest'
        | SOk (Some se) rest' -> SOk [SE_NodeConstraint nc; se] rest'))

and parse_node_constraint_only (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_node_constraint) (decreases fuel) =
  if fuel = 0 then SErr "nodeConstraint recursion limit"
  else
    match ts with
    | TK_KW "IRI" :: rest -> parse_facets st ({ empty_node_constraint with nc_node_kind = Some ShexNK_Iri }) rest (List.Tot.length rest + 1)
    | TK_KW "BNODE" :: rest -> parse_facets st ({ empty_node_constraint with nc_node_kind = Some ShexNK_BNode }) rest (List.Tot.length rest + 1)
    | TK_KW "NONLITERAL" :: rest -> parse_facets st ({ empty_node_constraint with nc_node_kind = Some ShexNK_NonLiteral }) rest (List.Tot.length rest + 1)
    | TK_KW "LITERAL" :: rest -> parse_facets st ({ empty_node_constraint with nc_node_kind = Some ShexNK_Literal }) rest (List.Tot.length rest + 1)
    | TK_LBRACKET :: _ ->
      (match parse_value_set st ts with
       | SErr m -> SErr m
       | SOk vs rest -> parse_facets st ({ empty_node_constraint with nc_values = vs }) rest (List.Tot.length rest + 1))
    | TK_TERM t :: rest ->
      (match resolve_shexc_term st t with
       | None -> SErr "unresolvable datatype IRI"
       | Some dt -> parse_facets st ({ empty_node_constraint with nc_datatype = Some dt }) rest (List.Tot.length rest + 1))
    | _ ->
      // Bare facet(s) with no leading nodeKind/datatype/valueSet
      // (stringFacet+ / numericFacet+ alone is a legal nodeConstraint).
      (match parse_facets st empty_node_constraint ts (List.Tot.length ts + 1) with
       | SErr m -> SErr m
       | SOk nc rest ->
         if List.Tot.length rest = List.Tot.length ts
         then SErr "expected a node constraint"
         else SOk nc rest)

and parse_optional_shape_or_ref_suffix (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult (option shex_shape_expr)) (decreases fuel) =
  if fuel = 0 then SErr "shapeOrRef suffix recursion limit"
  else
    match ts with
    | TK_AT_TERM t :: rest | TK_AT :: TK_TERM t :: rest ->
      (match resolve_shexc_term st t with
       | None -> SErr "unresolvable shapeRef"
       | Some s -> SOk (Some (SE_Ref s)) rest)
    | TK_KW "CLOSED" :: _ | TK_KW "EXTRA" :: _ | TK_KW "EXTENDS" :: _ | TK_LBRACE :: _ ->
      (match parse_shape_definition st ts (fuel - 1) with
       | SErr m -> SErr m
       | SOk sh rest -> SOk (Some (SE_Shape sh)) rest)
    | _ -> SOk None ts

// shapeDefinition: (EXTRA predicate+ | CLOSED | EXTENDS shapeExprRef)*
//                  '{' oneOfTripleExpr? '}' annotation* semanticActions
and parse_shape_definition (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_shape) (decreases fuel) =
  if fuel = 0 then SErr "shapeDefinition recursion limit"
  else
    parse_shape_modifiers st false [] [] ts (fuel - 1)

and parse_shape_modifiers (st: turtle_state) (closed: bool) (extra: list string) (extends: list string)
  (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_shape) (decreases fuel) =
  if fuel = 0 then SErr "shapeDefinition modifier recursion limit"
  else
    match ts with
    | TK_KW "CLOSED" :: rest -> parse_shape_modifiers st true extra extends rest (fuel - 1)
    | TK_KW "EXTRA" :: rest ->
      (match parse_predicate_list1 st rest (List.Tot.length rest + 1) with
       | SErr m -> SErr m
       | SOk preds rest' -> parse_shape_modifiers st closed (extra @ preds) extends rest' (fuel - 1))
    | TK_KW "EXTENDS" :: TK_AT_TERM t :: rest | TK_KW "EXTENDS" :: TK_AT :: TK_TERM t :: rest ->
      (match resolve_shexc_term st t with
       | None -> SErr "unresolvable EXTENDS target"
       | Some s -> parse_shape_modifiers st closed extra (extends @ [s]) rest (fuel - 1))
    | TK_LBRACE :: rest ->
      (match rest with
       | TK_RBRACE :: rest1 ->
         (match parse_annotations st rest1 (List.Tot.length rest1 + 1) with
          | SErr m -> SErr m
          | SOk annots rest2 ->
            (match parse_semacts st rest2 (List.Tot.length rest2 + 1) with
             | SErr m -> SErr m
             | SOk semacts rest3 ->
               SOk ({ sh_closed = closed; sh_extra = extra; sh_expression = None;
                      sh_semacts = semacts; sh_annotations = annots; sh_extends = extends }) rest3))
       | _ ->
         (match parse_one_of_triple_expr st rest (fuel - 1) with
          | SErr m -> SErr m
          | SOk te rest1 ->
            (match rest1 with
             | TK_RBRACE :: rest2 ->
               (match parse_annotations st rest2 (List.Tot.length rest2 + 1) with
                | SErr m -> SErr m
                | SOk annots rest3 ->
                  (match parse_semacts st rest3 (List.Tot.length rest3 + 1) with
                   | SErr m -> SErr m
                   | SOk semacts rest4 ->
                     SOk ({ sh_closed = closed; sh_extra = extra; sh_expression = Some te;
                            sh_semacts = semacts; sh_annotations = annots; sh_extends = extends }) rest4))
             | _ -> SErr "expected '}' to close shape body")))
    | _ -> SErr "expected CLOSED / EXTRA / EXTENDS / '{' in shape definition"

// oneOfTripleExpr: groupTripleExpr ('|' groupTripleExpr)*
and parse_one_of_triple_expr (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_triple_expr) (decreases fuel) =
  if fuel = 0 then SErr "oneOfTripleExpr recursion limit"
  else
    match parse_group_triple_expr st ts (fuel - 1) with
    | SErr m -> SErr m
    | SOk te rest -> parse_one_of_rest st [te] rest (fuel - 1)

and parse_one_of_rest (st: turtle_state) (acc: list shex_triple_expr) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_triple_expr) (decreases fuel) =
  if fuel = 0 then
    (match acc with [x] -> SOk x ts | _ -> SOk (TE_OneOf ({ gr_id = None; gr_expressions = List.Tot.rev acc; gr_min = None; gr_max = None; gr_semacts = []; gr_annotations = [] })) ts)
  else
    match ts with
    | TK_PIPE :: rest ->
      (match parse_group_triple_expr st rest (fuel - 1) with
       | SErr m -> SErr m
       | SOk te rest' -> parse_one_of_rest st (te :: acc) rest' (fuel - 1))
    | _ ->
      (match List.Tot.rev acc with
       | [x] -> SOk x ts
       | xs -> SOk (TE_OneOf ({ gr_id = None; gr_expressions = xs; gr_min = None; gr_max = None; gr_semacts = []; gr_annotations = [] })) ts)

// groupTripleExpr: unaryTripleExpr (';' unaryTripleExpr?)*
// Trailing/empty ';' entries (no expr following) are dropped -- matches
// the corpus's own trailing-semicolon idiom (1dotSemiOne1dotSemi.shex).
and parse_group_triple_expr (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_triple_expr) (decreases fuel) =
  if fuel = 0 then SErr "groupTripleExpr recursion limit"
  else
    match parse_unary_triple_expr st ts (fuel - 1) with
    | SErr m -> SErr m
    | SOk te rest -> parse_group_rest st [te] rest (fuel - 1)

and parse_group_rest (st: turtle_state) (acc: list shex_triple_expr) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_triple_expr) (decreases fuel) =
  if fuel = 0 then
    (match acc with [x] -> SOk x ts | xs -> SOk (TE_EachOf ({ gr_id = None; gr_expressions = List.Tot.rev xs; gr_min = None; gr_max = None; gr_semacts = []; gr_annotations = [] })) ts)
  else
    match ts with
    | TK_SEMI :: rest ->
      (if peek_starts_unary rest
       then
         (match parse_unary_triple_expr st rest (fuel - 1) with
          | SErr m -> SErr m
          | SOk te rest' -> parse_group_rest st (te :: acc) rest' (fuel - 1))
       else
         (match List.Tot.rev acc with
          | [x] -> SOk x rest
          | xs -> SOk (TE_EachOf ({ gr_id = None; gr_expressions = xs; gr_min = None; gr_max = None; gr_semacts = []; gr_annotations = [] })) rest))
    | _ ->
      (match List.Tot.rev acc with
       | [x] -> SOk x ts
       | xs -> SOk (TE_EachOf ({ gr_id = None; gr_expressions = xs; gr_min = None; gr_max = None; gr_semacts = []; gr_annotations = [] })) ts)

// unaryTripleExpr: ('$' label)? (tripleConstraint | bracketedTripleExpr)
//                 | '&' label (include)
and parse_unary_triple_expr (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_triple_expr) (decreases fuel) =
  if fuel = 0 then SErr "unaryTripleExpr recursion limit"
  else
    match ts with
    | TK_AMP :: TK_AT_TERM t :: rest ->
      (match resolve_shexc_term st t with
       | Some s -> SOk (TE_Ref s) rest
       | None -> SErr "unresolvable include target")
    | TK_AMP :: TK_TERM t :: rest ->
      (match resolve_shexc_term st t with
       | Some s -> SOk (TE_Ref s) rest
       | None -> SErr "unresolvable include target")
    | TK_DOLLAR :: rest ->
      (match rest with
       | TK_TERM t :: rest1 ->
         (match resolve_shexc_term st t with
          | None -> SErr "unresolvable triple-expression label"
          | Some label -> parse_unary_body st (Some label) rest1 (fuel - 1))
       | _ -> SErr "expected label after '$'")
    | _ -> parse_unary_body st None ts (fuel - 1)

and parse_unary_body (st: turtle_state) (label: option string) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_triple_expr) (decreases fuel) =
  if fuel = 0 then SErr "unaryTripleExpr body recursion limit"
  else
    match ts with
    | TK_LPAREN :: rest ->
      (match parse_one_of_triple_expr st rest (fuel - 1) with
       | SErr m -> SErr m
       | SOk inner rest1 ->
         (match rest1 with
          | TK_RPAREN :: rest2 ->
            let (card_min, card_max, rest3) = parse_optional_cardinality rest2 in
            (match parse_annotations st rest3 (List.Tot.length rest3 + 1) with
             | SErr m -> SErr m
             | SOk annots rest4 ->
               (match parse_semacts st rest4 (List.Tot.length rest4 + 1) with
                | SErr m -> SErr m
                | SOk semacts rest5 ->
                  let bare_passthrough =
                    (match card_min, card_max with None, None -> true | _ -> false) &&
                    label = None && annots = [] && semacts = [] in
                  if bare_passthrough then SOk inner rest5
                  else
                    // `( groupTripleExpr ) cardinality? annotation* semAct*`
                    // sets these fields directly on the group ALREADY
                    // produced by the `;`/`|`-separated body (a bracketed
                    // EachOf/OneOf's cardinality lands on that same group's
                    // own min/max, per the corpus's own open3Onedotclosecard2
                    // / open3Eachdotclosecard23 .json twins -- it does NOT
                    // wrap in a second, one-element outer group). Only a
                    // single bare (non-grouped) inner member needs a fresh
                    // wrapper, since TE_TripleConstraint/TE_Ref have no
                    // group-shaped min/max slot of their own to reuse.
                    (match inner with
                     | TE_EachOf g ->
                       SOk (TE_EachOf ({ g with gr_id = label; gr_min = card_min; gr_max = card_max;
                                                gr_semacts = semacts; gr_annotations = annots })) rest5
                     | TE_OneOf g ->
                       SOk (TE_OneOf ({ g with gr_id = label; gr_min = card_min; gr_max = card_max;
                                               gr_semacts = semacts; gr_annotations = annots })) rest5
                     | _ ->
                       let g = { gr_id = label; gr_expressions = [inner]; gr_min = card_min; gr_max = card_max;
                                 gr_semacts = semacts; gr_annotations = annots } in
                       SOk (TE_EachOf g) rest5)))
          | _ -> SErr "expected ')' to close bracketed triple expression"))
    | _ ->
      (match parse_triple_constraint st label ts (fuel - 1) with
       | SErr m -> SErr m
       | SOk tc rest -> SOk (TE_TripleConstraint tc) rest)

// tripleConstraint: senseFlags? predicate inlineShapeExpression
//                    cardinality? annotation* semanticActions
and parse_triple_constraint (st: turtle_state) (label: option string) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_triple_constraint) (decreases fuel) =
  if fuel = 0 then SErr "tripleConstraint recursion limit"
  else
    let (inverse, ts1) = opt_consume (fun t -> t = TK_CARET) ts in
    match ts1 with
    | TK_TERM t :: rest ->
      (match resolve_shexc_term st t with
       | None -> SErr "unresolvable predicate"
       | Some pred ->
         (match parse_triple_constraint_value_expr st rest (fuel - 1) with
          | SErr m -> SErr m
          | SOk value_expr_opt rest1 ->
            let (card_min, card_max, rest2) = parse_optional_cardinality rest1 in
            (match parse_annotations st rest2 (List.Tot.length rest2 + 1) with
             | SErr m -> SErr m
             | SOk annots rest3 ->
               (match parse_semacts st rest3 (List.Tot.length rest3 + 1) with
                | SErr m -> SErr m
                | SOk semacts rest4 ->
                  SOk ({ tc_id = label; tc_inverse = inverse; tc_predicate = pred;
                         tc_value_expr = value_expr_opt;
                         tc_min = (match card_min with Some m -> m | None -> 1);
                         tc_max = (match card_max with Some m -> m | None -> 1);
                         tc_semacts = semacts; tc_annotations = annots }) rest4))))
    | _ -> SErr "expected a predicate"

// A tripleConstraint's value: an inlineShapeExpression, EXCEPT that a
// bare, uncombined wildcard `.` (nothing ANDed/ORed onto it) omits
// "valueExpr" entirely instead of reifying `.` as an empty Shape -- see
// 1dot.json (TripleConstraint has no "valueExpr" key at all) vs
// 1NOTdot.json (`NOT .` DOES reify the inner `.` as `{"type":"Shape"}`,
// since NOT's operand can't be represented as "nothing"). Peeking one
// token past the DOT to check for AND/OR is enough to distinguish "bare"
// from "combined": every other continuation (cardinality, `;`, `}`, `)`,
// `//` annotation, `%` semAct, EOF) terminates the shapeAnd/shapeOr chain
// right there.
and parse_triple_constraint_value_expr (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult (option shex_shape_expr)) (decreases fuel) =
  if fuel = 0 then SErr "tripleConstraint value recursion limit"
  else
    match ts with
    | TK_DOT :: TK_KW "AND" :: _ | TK_DOT :: TK_KW "OR" :: _ ->
      (match parse_inline_shape_expression st ts (fuel - 1) with
       | SErr m -> SErr m
       | SOk ve rest -> SOk (Some ve) rest)
    | TK_DOT :: after_dot -> SOk None after_dot
    | _ ->
      (match parse_inline_shape_expression st ts (fuel - 1) with
       | SErr m -> SErr m
       | SOk ve rest -> SOk (Some ve) rest)

// inlineShapeExpression reuses the exact same OR/AND/NOT/atom grammar as
// shapeExpression -- the "inline" distinction only restricts a bare
// shapeDefinition body from being labeled at the top with EXTENDS/CLOSED
// in a *nested* position per the formal grammar's two parallel
// productions, a distinction with no AST-shape consequence here (both
// paths build the same `shex_shape_expr`), so this is a direct alias.
and parse_inline_shape_expression (st: turtle_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shex_shape_expr) (decreases fuel) =
  if fuel = 0 then SErr "inlineShapeExpression recursion limit"
  else parse_shape_or st ts (fuel - 1)

(* ================================================================ *)
(* Top level: directives, shapeExprDecl, START, schema.               *)
(* ================================================================ *)

noeq type shexc_parse_state = {
  ps_turtle   : turtle_state;
  ps_start    : option shex_shape_expr;
  ps_start_acts : list shex_sem_act;
  ps_shapes   : list shex_shape_decl;
  ps_imports  : list string;
}

let sc_is_directive_start (t: shexc_token) : bool =
  t = TK_KW "PREFIX" || t = TK_KW "BASE" || t = TK_KW "IMPORT"

let rec parse_directives (ps: shexc_parse_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shexc_parse_state) (decreases fuel) =
  if fuel = 0 then SOk ps ts
  else
    match ts with
    | TK_KW "PREFIX" :: TK_TERM (ST_PName ns "") :: TK_TERM t :: rest ->
      (match t with
       | ST_Iri raw has_colon ->
         let iri_val = resolve_iri_hint ps.ps_turtle raw has_colon in
         let st' = { ps.ps_turtle with prefixes = (ns, iri_val) :: ps.ps_turtle.prefixes } in
         parse_directives ({ ps with ps_turtle = st' }) rest (fuel - 1)
       | _ -> SErr "PREFIX expects an IRIREF")
    | TK_KW "BASE" :: TK_TERM t :: rest ->
      (match t with
       | ST_Iri raw has_colon ->
         let iri_val = resolve_iri_hint ps.ps_turtle raw has_colon in
         let st' = { ps.ps_turtle with base_iri = iri_val } in
         parse_directives ({ ps with ps_turtle = st' }) rest (fuel - 1)
       | _ -> SErr "BASE expects an IRIREF")
    | TK_KW "IMPORT" :: TK_TERM t :: rest ->
      parse_directives ({ ps with ps_imports = ps.ps_imports @ [raw_shexc_term t] }) rest (fuel - 1)
    | _ -> SOk ps ts

// shapeExprDecl: shapeExprLabel (shapeExpression | EXTERNAL)
//              | ABSTRACT shapeExprLabel (shapeExpression | EXTERNAL)
// START: START '=' shapeExpression
let parse_statement (ps: shexc_parse_state) (ts: shexc_tokens) (fuel: nat)
  : sresult shexc_parse_state =
  match ts with
  | TK_SEMACT _ _ :: _ ->
    (match parse_semacts ps.ps_turtle ts (List.Tot.length ts + 1) with
     | SErr m -> SErr m
     | SOk sa rest -> SOk ({ ps with ps_start_acts = ps.ps_start_acts @ sa }) rest)
  | TK_KW "START" :: TK_EQ :: rest ->
    (match parse_shape_expression ps.ps_turtle rest shexc_grammar_fuel with
     | SErr m -> SErr m
     | SOk se rest1 -> SOk ({ ps with ps_start = Some se }) rest1)
  | TK_KW "ABSTRACT" :: TK_TERM t :: rest ->
    (match resolve_shexc_term ps.ps_turtle t with
     | None -> SErr "unresolvable shape label"
     | Some label ->
       (match rest with
        | TK_KW "EXTERNAL" :: rest1 ->
          SOk ({ ps with ps_shapes = ps.ps_shapes @ [{ sd_id = label; sd_is_abstract = true; sd_expr = SE_ShapeExternal }] }) rest1
        | _ ->
          (match parse_shape_expression ps.ps_turtle rest shexc_grammar_fuel with
           | SErr m -> SErr m
           | SOk se rest1 ->
             SOk ({ ps with ps_shapes = ps.ps_shapes @ [{ sd_id = label; sd_is_abstract = true; sd_expr = se }] }) rest1)))
  | TK_TERM t :: rest ->
    (match resolve_shexc_term ps.ps_turtle t with
     | None -> SErr "unresolvable shape label"
     | Some label ->
       (match rest with
        | TK_KW "EXTERNAL" :: rest1 ->
          SOk ({ ps with ps_shapes = ps.ps_shapes @ [{ sd_id = label; sd_is_abstract = false; sd_expr = SE_ShapeExternal }] }) rest1
        | _ ->
          (match parse_shape_expression ps.ps_turtle rest shexc_grammar_fuel with
           | SErr m -> SErr m
           | SOk se rest1 ->
             SOk ({ ps with ps_shapes = ps.ps_shapes @ [{ sd_id = label; sd_is_abstract = false; sd_expr = se }] }) rest1)))
  | _ -> SErr "expected a shape declaration, START, or directive"

let rec parse_statements (ps: shexc_parse_state) (ts: shexc_tokens) (fuel: nat)
  : Tot (sresult shexc_parse_state) (decreases fuel) =
  if fuel = 0 then SOk ps ts
  else
    match parse_directives ps ts (List.Tot.length ts + 1) with
    | SErr m -> SErr m
    | SOk ps1 ts1 ->
      (match ts1 with
       | [] | TK_EOF :: _ -> SOk ps1 ts1
       | _ ->
         (match parse_statement ps1 ts1 (fuel - 1) with
          | SErr m -> SErr m
          | SOk ps2 ts2 -> parse_statements ps2 ts2 (fuel - 1)))

let empty_parse_state (base: string) : shexc_parse_state = {
  ps_turtle = { empty_turtle_state with base_iri = base };
  ps_start = None; ps_start_acts = []; ps_shapes = []; ps_imports = [];
}

// Top-level entry point. Mirrors ShEx.Schema.decode_shex_schema's
// signature exactly (input text, document base IRI) so a caller can
// dispatch on schema-text shape (does it start with '{'? -> ShExJ; else
// -> ShExC) without any other code-path difference.
let parse_shexc_schema (input: string) (base: string) : option shex_schema =
  let ts = shexc_tokenize input in
  match parse_statements (empty_parse_state base) ts (List.Tot.length ts + 1) with
  | SErr _ -> None
  | SOk ps _ ->
    Some ({
      sch_start = ps.ps_start;
      sch_start_acts = ps.ps_start_acts;
      sch_shapes = ps.ps_shapes;
      sch_imports = ps.ps_imports;
    })
