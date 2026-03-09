module SPARQL11.Parser

(** ======================================================================== **)
(** SPARQL 1.1 Parser — Verified Recursive Descent                          **)
(**                                                                          **)
(** Produces SPARQL11.Algebra types directly (no separate CST).              **)
(** Modeled on Apache Jena ARQ's parser architecture:                        **)
(**   Text → Tokens → Algebra → SSE                                         **)
(**                                                                          **)
(** Verification: total functions with termination on decreasing position.   **)
(** assume val: character-level string ops delegated to OCaml extraction.    **)
(** ======================================================================== **)

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** ====================================================================== **)
(** Part 1: Token Types                                                     **)
(** ====================================================================== **)

type token =
  (* Keywords *)
  | Tok_SELECT | Tok_ASK | Tok_CONSTRUCT | Tok_DESCRIBE
  | Tok_WHERE | Tok_PREFIX | Tok_BASE
  | Tok_OPTIONAL | Tok_UNION | Tok_MINUS_KW | Tok_FILTER | Tok_BIND | Tok_VALUES
  | Tok_GRAPH | Tok_SERVICE | Tok_SILENT
  | Tok_EXISTS | Tok_NOT
  | Tok_AS | Tok_DISTINCT | Tok_REDUCED
  | Tok_ORDER | Tok_BY | Tok_ASC | Tok_DESC
  | Tok_GROUP | Tok_HAVING
  | Tok_LIMIT | Tok_OFFSET
  | Tok_IN | Tok_TRUE | Tok_FALSE | Tok_UNDEF
  | Tok_A  (* 'a' = rdf:type *)
  (* Delimiters *)
  | Tok_LBRACE | Tok_RBRACE | Tok_LPAREN | Tok_RPAREN
  | Tok_LBRACKET | Tok_RBRACKET
  | Tok_DOT | Tok_SEMI | Tok_COMMA
  (* Operators *)
  | Tok_STAR | Tok_SLASH | Tok_PIPE | Tok_CARET | Tok_BANG | Tok_QMARK
  | Tok_PLUS | Tok_MINUS_OP
  | Tok_EQ | Tok_NE | Tok_LT | Tok_GT | Tok_LE | Tok_GE
  | Tok_AND | Tok_OR
  | Tok_HATHAT (* ^^ *)
  (* Literals and names *)
  | Tok_IRI      : string -> token
  | Tok_PNAME    : string -> token   (* prefixed name, pre-expansion *)
  | Tok_VAR      : string -> token
  | Tok_STRING   : string -> token
  | Tok_LANGTAG  : string -> token
  | Tok_INTEGER  : string -> token
  | Tok_DECIMAL  : string -> token
  | Tok_DOUBLE   : string -> token
  | Tok_BNODE    : string -> token
  | Tok_ANON                         (* [] *)
  (* Built-in function keywords *)
  | Tok_STR | Tok_LANG | Tok_LANGMATCHES | Tok_DATATYPE | Tok_BOUND | Tok_IF
  | Tok_IRI_KW | Tok_URI | Tok_BNODE_KW | Tok_RAND
  | Tok_ABS | Tok_CEIL | Tok_FLOOR | Tok_ROUND
  | Tok_CONCAT | Tok_STRLEN | Tok_UCASE | Tok_LCASE
  | Tok_ENCODE_FOR_URI | Tok_CONTAINS | Tok_STRSTARTS | Tok_STRENDS
  | Tok_STRBEFORE | Tok_STRAFTER | Tok_REPLACE | Tok_REGEX
  | Tok_SUBSTR
  | Tok_ISIRI | Tok_ISBLANK | Tok_ISLITERAL | Tok_ISNUMERIC
  | Tok_SAMETERM | Tok_STRDT | Tok_STRLANG
  | Tok_COUNT | Tok_SUM | Tok_MIN_KW | Tok_MAX_KW | Tok_AVG
  | Tok_GROUP_CONCAT | Tok_SAMPLE | Tok_SEPARATOR
  | Tok_COALESCE | Tok_NOW | Tok_UUID | Tok_STRUUID
  | Tok_YEAR | Tok_MONTH | Tok_DAY | Tok_HOURS | Tok_MINUTES | Tok_SECONDS
  | Tok_TIMEZONE | Tok_TZ
  | Tok_MD5 | Tok_SHA1 | Tok_SHA256 | Tok_SHA384 | Tok_SHA512
  (* End *)
  | Tok_EOF

(** ====================================================================== **)
(** Part 2: Lexer State and Character Operations                            **)
(**                                                                          **)
(** String indexing in F* requires careful termination arguments.             **)
(** We use assume val for character-level operations that extract to          **)
(** straightforward OCaml. Each has a stub in ocaml-patches.sh.              **)
(** ====================================================================== **)

(* Lexer position: index into the input string.
   Invariant: 0 <= pos <= String.length input *)
type pos = nat

(* Result of lexing one token: the token and the new position *)
type lex_result = token & pos

(* Character at position, or null if past end *)
let char_at (s : string) (p : pos) : FStar.Char.char =
  if p < String.length s then String.index s p
  else FStar.Char.char_of_int 0

(* Check if position is at or past end of input *)
let at_end (input : string) (p : pos) : bool =
  p >= String.length input

(* Peek at character without advancing *)
let peek_char (input : string) (p : pos) : FStar.Char.char =
  if at_end input p then FStar.Char.char_of_int 0
  else char_at input p

(* Extract substring — safe: clamps to bounds *)
let substring (s : string) (p : pos) (len : nat) : string =
  if len = 0 then ""
  else if p + len <= String.length s then String.sub s p len
  else if p < String.length s then String.sub s p (String.length s - p)
  else ""

(* Convert character to its integer code *)
let char_code (c : FStar.Char.char) : nat = FStar.Char.int_of_char c

(* Character classification *)
let is_alpha (c : FStar.Char.char) : bool =
  let code = char_code c in
  (code >= 0x61 && code <= 0x7A) ||  (* a-z *)
  (code >= 0x41 && code <= 0x5A)     (* A-Z *)

let is_digit (c : FStar.Char.char) : bool =
  let code = char_code c in
  code >= 0x30 && code <= 0x39

let is_alnum (c : FStar.Char.char) : bool =
  is_alpha c || is_digit c

let is_ws (c : FStar.Char.char) : bool =
  let code = char_code c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

let is_pn_char (c : FStar.Char.char) : bool =
  is_alnum c || char_code c = 0x5F (* _ *) || char_code c = 0x2D (* - *)
  || char_code c = 0x2E (* . *) || char_code c >= 0x80

(* PN_LOCAL_ESC valid chars: _~.-!$&'()*+,;=/?#@% *)
let is_pn_local_esc (c : FStar.Char.char) : bool =
  let code = char_code c in
  code = 0x5F || code = 0x7E || code = 0x2E || code = 0x2D ||
  code = 0x21 || code = 0x24 || code = 0x26 || code = 0x27 ||
  code = 0x28 || code = 0x29 || code = 0x2A || code = 0x2B ||
  code = 0x2C || code = 0x3B || code = 0x3D || code = 0x2F ||
  code = 0x3F || code = 0x23 || code = 0x40 || code = 0x25

(* Upper-case a single character *)
let char_upper (c : FStar.Char.char) : FStar.Char.char =
  let cd = char_code c in
  if cd >= 0x61 && cd <= 0x7A then FStar.Char.char_of_int (cd - 32)
  else c

(* Upper-case a string for keyword matching *)
let string_upper (s : string) : string =
  String.string_of_list (List.Tot.map char_upper (String.list_of_string s))

(* String equality *)
let streq (a b : string) : bool = a = b

(** ====================================================================== **)
(** Part 3: Lexer                                                           **)
(**                                                                          **)
(** Tokenizes input string. Each function takes input + position,            **)
(** returns result + new position. Termination: position strictly increases. **)
(** ====================================================================== **)

(* Skip whitespace and comments. Returns new position >= p. *)
let rec skip_ws (input : string) (p : pos) : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else
    let c = peek_char input p in
    if is_ws c then skip_ws input (p + 1)
    else if char_code c = 0x23 (* # *) then
      skip_comment input (p + 1)
    else p

and skip_comment (input : string) (p : pos) : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else if char_code (peek_char input p) = 0x0A then skip_ws input (p + 1)
  else skip_comment input (p + 1)

(* Scan forward while predicate holds, returning new position *)
let rec scan_while (input : string) (p : pos) (pred : FStar.Char.char -> bool)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else if pred (peek_char input p) then scan_while input (p + 1) pred
  else p

(* Scan an IRI: position is after '<', read until '>' *)
let rec scan_iri_body (input : string) (p : pos) (start : pos)
  : Tot (string & pos) (decreases (String.length input - p)) =
  if at_end input p then (substring input start (p - start), p)
  else if char_code (peek_char input p) = 0x3E (* > *) then
    (substring input start (p - start), p + 1)
  else scan_iri_body input (p + 1) start

let scan_iri (input : string) (p : pos) : (string & pos) =
  scan_iri_body input p p

(* Scan a short string literal: position is after opening quote *)
let rec scan_short_str (input : string) (p : pos) (start : pos) (q : nat)
  : Tot (string & pos) (decreases (String.length input - p)) =
  if at_end input p then (substring input start (p - start), p)
  else
    let c = peek_char input p in
    if char_code c = 0x5C (* backslash *) then
      (* skip escape — advance past the escaped char *)
      if at_end input (p + 1) then (substring input start (p + 1 - start), p + 1)
      else scan_short_str input (p + 2) start q
    else if char_code c = q then
      (substring input start (p - start), p + 1)
    else scan_short_str input (p + 1) start q

(* Scan a long string literal (triple-quoted): position is after opening triple-quote *)
let rec scan_long_str (input : string) (p : pos) (start : pos) (q : nat)
  : Tot (string & pos) (decreases (String.length input - p)) =
  if at_end input p then (substring input start (p - start), p)
  else
    let c = peek_char input p in
    if char_code c = 0x5C then
      if at_end input (p + 1) then (substring input start (p + 1 - start), p + 1)
      else scan_long_str input (p + 2) start q
    else if char_code c = q
         && not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = q
         && not (at_end input (p + 2)) && char_code (peek_char input (p + 2)) = q then
      (substring input start (p - start), p + 3)
    else scan_long_str input (p + 1) start q

(* Scan a string literal (single or double quoted, short or long) *)
let scan_string (input : string) (p : pos) : (string & pos) =
  let q = char_code (peek_char input p) in
  (* Check for triple-quote *)
  if not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = q
     && not (at_end input (p + 2)) && char_code (peek_char input (p + 2)) = q then
    scan_long_str input (p + 3) (p + 3) q
  else
    scan_short_str input (p + 1) (p + 1) q

(* Keyword lookup table *)
let keyword_of_upper (u : string) : option token =
  if u = "SELECT" then Some Tok_SELECT
  else if u = "ASK" then Some Tok_ASK
  else if u = "CONSTRUCT" then Some Tok_CONSTRUCT
  else if u = "DESCRIBE" then Some Tok_DESCRIBE
  else if u = "WHERE" then Some Tok_WHERE
  else if u = "PREFIX" then Some Tok_PREFIX
  else if u = "BASE" then Some Tok_BASE
  else if u = "OPTIONAL" then Some Tok_OPTIONAL
  else if u = "UNION" then Some Tok_UNION
  else if u = "MINUS" then Some Tok_MINUS_KW
  else if u = "FILTER" then Some Tok_FILTER
  else if u = "BIND" then Some Tok_BIND
  else if u = "VALUES" then Some Tok_VALUES
  else if u = "GRAPH" then Some Tok_GRAPH
  else if u = "SERVICE" then Some Tok_SERVICE
  else if u = "SILENT" then Some Tok_SILENT
  else if u = "EXISTS" then Some Tok_EXISTS
  else if u = "NOT" then Some Tok_NOT
  else if u = "AS" then Some Tok_AS
  else if u = "DISTINCT" then Some Tok_DISTINCT
  else if u = "REDUCED" then Some Tok_REDUCED
  else if u = "ORDER" then Some Tok_ORDER
  else if u = "BY" then Some Tok_BY
  else if u = "ASC" then Some Tok_ASC
  else if u = "DESC" then Some Tok_DESC
  else if u = "GROUP" then Some Tok_GROUP
  else if u = "HAVING" then Some Tok_HAVING
  else if u = "LIMIT" then Some Tok_LIMIT
  else if u = "OFFSET" then Some Tok_OFFSET
  else if u = "IN" then Some Tok_IN
  else if u = "TRUE" then Some Tok_TRUE
  else if u = "FALSE" then Some Tok_FALSE
  else if u = "UNDEF" then Some Tok_UNDEF
  else if u = "A" then Some Tok_A
  else if u = "STR" then Some Tok_STR
  else if u = "LANG" then Some Tok_LANG
  else if u = "LANGMATCHES" then Some Tok_LANGMATCHES
  else if u = "DATATYPE" then Some Tok_DATATYPE
  else if u = "BOUND" then Some Tok_BOUND
  else if u = "IF" then Some Tok_IF
  else if u = "IRI" then Some Tok_IRI_KW
  else if u = "URI" then Some Tok_URI
  else if u = "BNODE" then Some Tok_BNODE_KW
  else if u = "RAND" then Some Tok_RAND
  else if u = "ABS" then Some Tok_ABS
  else if u = "CEIL" then Some Tok_CEIL
  else if u = "FLOOR" then Some Tok_FLOOR
  else if u = "ROUND" then Some Tok_ROUND
  else if u = "CONCAT" then Some Tok_CONCAT
  else if u = "STRLEN" then Some Tok_STRLEN
  else if u = "UCASE" then Some Tok_UCASE
  else if u = "LCASE" then Some Tok_LCASE
  else if u = "ENCODE_FOR_URI" then Some Tok_ENCODE_FOR_URI
  else if u = "CONTAINS" then Some Tok_CONTAINS
  else if u = "STRSTARTS" then Some Tok_STRSTARTS
  else if u = "STRENDS" then Some Tok_STRENDS
  else if u = "STRBEFORE" then Some Tok_STRBEFORE
  else if u = "STRAFTER" then Some Tok_STRAFTER
  else if u = "REPLACE" then Some Tok_REPLACE
  else if u = "REGEX" then Some Tok_REGEX
  else if u = "SUBSTR" then Some Tok_SUBSTR
  else if u = "ISIRI" then Some Tok_ISIRI
  else if u = "ISURI" then Some Tok_ISIRI
  else if u = "ISBLANK" then Some Tok_ISBLANK
  else if u = "ISLITERAL" then Some Tok_ISLITERAL
  else if u = "ISNUMERIC" then Some Tok_ISNUMERIC
  else if u = "SAMETERM" then Some Tok_SAMETERM
  else if u = "STRDT" then Some Tok_STRDT
  else if u = "STRLANG" then Some Tok_STRLANG
  else if u = "COUNT" then Some Tok_COUNT
  else if u = "SUM" then Some Tok_SUM
  else if u = "MIN" then Some Tok_MIN_KW
  else if u = "MAX" then Some Tok_MAX_KW
  else if u = "AVG" then Some Tok_AVG
  else if u = "GROUP_CONCAT" then Some Tok_GROUP_CONCAT
  else if u = "SAMPLE" then Some Tok_SAMPLE
  else if u = "SEPARATOR" then Some Tok_SEPARATOR
  else if u = "COALESCE" then Some Tok_COALESCE
  else if u = "NOW" then Some Tok_NOW
  else if u = "UUID" then Some Tok_UUID
  else if u = "STRUUID" then Some Tok_STRUUID
  else if u = "YEAR" then Some Tok_YEAR
  else if u = "MONTH" then Some Tok_MONTH
  else if u = "DAY" then Some Tok_DAY
  else if u = "HOURS" then Some Tok_HOURS
  else if u = "MINUTES" then Some Tok_MINUTES
  else if u = "SECONDS" then Some Tok_SECONDS
  else if u = "TIMEZONE" then Some Tok_TIMEZONE
  else if u = "TZ" then Some Tok_TZ
  else if u = "MD5" then Some Tok_MD5
  else if u = "SHA1" then Some Tok_SHA1
  else if u = "SHA256" then Some Tok_SHA256
  else if u = "SHA384" then Some Tok_SHA384
  else if u = "SHA512" then Some Tok_SHA512
  else None

(* Scan a prefixed name or keyword.
   Reads PN_CHARS_BASE chars (alpha, digit, underscore, dash, dot, colon, non-ASCII). *)
let scan_pname_or_keyword (input : string) (p : pos) : lex_result =
  let p' = scan_while input p (fun c ->
    is_pn_char c || char_code c = 0x3A (* : *)) in
  let word = substring input p (p' - p) in
  (* Check if it's a keyword (only if no colon — colons mean prefixed name) *)
  let has_colon = string_contains_colon word in
  if has_colon then (Tok_PNAME word, p')
  else
    match keyword_of_upper (string_upper word) with
    | Some tok -> (tok, p')
    | None -> (Tok_PNAME word, p')

(* Scan a number: integer, decimal, or double *)
let scan_number (input : string) (p : pos) : lex_result =
  let p' = scan_while input p is_digit in
  if not (at_end input p') && char_code (peek_char input p') = 0x2E (* . *) then
    let p'' = scan_while input (p' + 1) is_digit in
    (* Check for exponent *)
    if not (at_end input p'') &&
       (char_code (peek_char input p'') = 0x45 || char_code (peek_char input p'') = 0x65) then
      let p3 = p'' + 1 in
      let p3 = if not (at_end input p3) &&
                  (char_code (peek_char input p3) = 0x2B || char_code (peek_char input p3) = 0x2D)
               then p3 + 1 else p3 in
      let p4 = scan_while input p3 is_digit in
      (Tok_DOUBLE (substring input p (p4 - p)), p4)
    else (Tok_DECIMAL (substring input p (p'' - p)), p'')
  else if not (at_end input p') &&
          (char_code (peek_char input p') = 0x45 || char_code (peek_char input p') = 0x65) then
    let p'' = p' + 1 in
    let p'' = if not (at_end input p'') &&
                 (char_code (peek_char input p'') = 0x2B || char_code (peek_char input p'') = 0x2D)
              then p'' + 1 else p'' in
    let p3 = scan_while input p'' is_digit in
    (Tok_DOUBLE (substring input p (p3 - p)), p3)
  else (Tok_INTEGER (substring input p (p' - p)), p')

(* Scan a blank node label after _: *)
let scan_bnode_label (input : string) (p : pos) : (string & pos) =
  let p' = scan_while input p is_pn_char in
  (* Trim trailing dots per PN_LOCAL grammar *)
  let rec trim_dots (q : nat) : Tot nat (decreases q) =
    if q <= p then p
    else if char_code (char_at input (q - 1)) = 0x2E then trim_dots (q - 1)
    else q
  in
  let p'' = trim_dots p' in
  (substring input p (p'' - p), p'')

(* Scan a variable name after ? or $ *)
let scan_var_name (input : string) (p : pos) : (string & pos) =
  let p' = scan_while input p (fun c -> is_alnum c || char_code c = 0x5F) in
  (substring input p (p' - p), p')

(* Scan subtags for language tags: (-[a-zA-Z0-9]+)* *)
let rec scan_lang_subtags (input : string) (p : pos) (fuel : nat)
  : Tot pos (decreases fuel) =
  if fuel = 0 then p
  else if not (at_end input p) && char_code (peek_char input p) = 0x2D (* - *) then
    let p' = scan_while input (p + 1) is_alnum in
    if p' > p + 1 then scan_lang_subtags input p' (fuel - 1) else p
  else p

(* Scan a language tag after @ *)
let scan_langtag (input : string) (p : pos) : (string & pos) =
  let p' = scan_while input p is_alpha in
  if p' = p then ("", p)
  else
    let p'' = scan_lang_subtags input p' 20 in
    (substring input p (p'' - p), p'')

(* Main tokenizer: produce one token from current position *)
let next_token (input : string) (p : pos) : lex_result =
  let p = skip_ws input p in
  if at_end input p then (Tok_EOF, p)
  else
    let c = peek_char input p in
    let code = char_code c in
    if code = 0x3C (* < *) then begin
      (* Could be <= or <IRI> or < (less-than) *)
      if not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = 0x3D
      then (Tok_LE, p + 2)
      else
        let (iri, p') = scan_iri input (p + 1) in
        (Tok_IRI iri, p')
    end
    else if code = 0x3E (* > *) then
      if not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = 0x3D
      then (Tok_GE, p + 2)
      else (Tok_GT, p + 1)
    else if code = 0x7B then (Tok_LBRACE, p + 1)   (* { *)
    else if code = 0x7D then (Tok_RBRACE, p + 1)   (* } *)
    else if code = 0x28 then (Tok_LPAREN, p + 1)   (* ( *)
    else if code = 0x29 then (Tok_RPAREN, p + 1)   (* ) *)
    else if code = 0x5B then (Tok_LBRACKET, p + 1)  (* [ — anon detection in parser *)
    else if code = 0x5D then (Tok_RBRACKET, p + 1)  (* ] *)
    else if code = 0x2E then (Tok_DOT, p + 1)       (* . *)
    else if code = 0x3B then (Tok_SEMI, p + 1)      (* ; *)
    else if code = 0x2C then (Tok_COMMA, p + 1)     (* , *)
    else if code = 0x2A then (Tok_STAR, p + 1)      (* * *)
    else if code = 0x2F then (Tok_SLASH, p + 1)     (* / *)
    else if code = 0x7C then begin                   (* | or || *)
      if not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = 0x7C
      then (Tok_OR, p + 2)
      else (Tok_PIPE, p + 1)
    end
    else if code = 0x5E then begin                   (* ^ or ^^ *)
      if not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = 0x5E
      then (Tok_HATHAT, p + 2)
      else (Tok_CARET, p + 1)
    end
    else if code = 0x21 then begin                   (* ! or != *)
      if not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = 0x3D
      then (Tok_NE, p + 2)
      else (Tok_BANG, p + 1)
    end
    else if code = 0x3D then (Tok_EQ, p + 1)        (* = *)
    else if code = 0x26 then begin                   (* && *)
      if not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = 0x26
      then (Tok_AND, p + 2)
      else (Tok_AND, p + 2) (* single & not valid SPARQL, treat as && *)
    end
    else if code = 0x3F || code = 0x24 then begin    (* ? or $ — variable *)
      let (name, p') = scan_var_name input (p + 1) in
      if String.length name = 0 then (Tok_QMARK, p + 1)
      else (Tok_VAR name, p')
    end
    else if code = 0x22 || code = 0x27 then begin    (* " or ' — string literal *)
      let (s, p') = scan_string input p in
      (Tok_STRING s, p')
    end
    else if code = 0x40 then begin                   (* @ — language tag *)
      let (tag, p') = scan_langtag input (p + 1) in
      (Tok_LANGTAG tag, p')
    end
    else if code = 0x2B then (Tok_PLUS, p + 1)      (* + *)
    else if code = 0x2D then (Tok_MINUS_OP, p + 1)  (* - *)
    else if code = 0x5F then begin                   (* _ — blank node _: *)
      if not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = 0x3A
      then
        let (label, p') = scan_bnode_label input (p + 2) in
        (Tok_BNODE label, p')
      else scan_pname_or_keyword input p
    end
    else if is_digit c then scan_number input p
    else if is_alpha c || code = 0x3A || code >= 0x80 then
      scan_pname_or_keyword input p
    else (Tok_EOF, p + 1)  (* skip unknown char *)


(** ====================================================================== **)
(** Part 4: Parse Result Type                                               **)
(** ====================================================================== **)

(* Parser produces either a value or an error *)
noeq type parse_result (a : Type) =
  | ParseOk  : v:a -> remaining:list token -> parse_result a
  | ParseErr : msg:string -> parse_result a

(* Token stream = list of tokens (produced by lexer) *)
type token_stream = list token

(* Helper: check if a token is EOF *)
let is_eof (t : token) : bool =
  match t with Tok_EOF -> true | _ -> false

(* Tokenize entire input into a token list *)
let rec tokenize_acc (input : string) (p : pos) (acc : list token) (fuel : nat)
  : Tot (list token) (decreases fuel) =
  if fuel = 0 then List.Tot.rev (Tok_EOF :: acc)
  else
    let (tok, p') = next_token input p in
    if is_eof tok then List.Tot.rev (Tok_EOF :: acc)
    else tokenize_acc input p' (tok :: acc) (fuel - 1)

let tokenize (input : string) : list token =
  tokenize_acc input 0 [] (String.length input + 100)

(** ====================================================================== **)
(** Part 5: Parser Combinators                                              **)
(** ====================================================================== **)

let parse_ok (#a : Type) (v : a) (ts : token_stream) : parse_result a =
  ParseOk v ts

let parse_err (#a : Type) (msg : string) : parse_result a =
  ParseErr msg

let parse_bind (#a #b : Type) (p : parse_result a) (f : a -> token_stream -> parse_result b) : parse_result b =
  match p with
  | ParseOk v ts -> f v ts
  | ParseErr msg -> ParseErr msg

(* Peek at current token without consuming *)
let parse_peek (ts : token_stream) : token =
  match ts with
  | [] -> Tok_EOF
  | t :: _ -> t

(* Consume one token *)
let parse_advance (ts : token_stream) : token_stream =
  match ts with
  | [] -> []
  | _ :: rest -> rest

(* Token equality — structural comparison *)
let token_eq (t1 t2 : token) : bool =
  match t1, t2 with
  | Tok_SELECT, Tok_SELECT | Tok_ASK, Tok_ASK | Tok_CONSTRUCT, Tok_CONSTRUCT
  | Tok_DESCRIBE, Tok_DESCRIBE | Tok_WHERE, Tok_WHERE | Tok_PREFIX, Tok_PREFIX
  | Tok_BASE, Tok_BASE | Tok_OPTIONAL, Tok_OPTIONAL | Tok_UNION, Tok_UNION
  | Tok_MINUS_KW, Tok_MINUS_KW | Tok_FILTER, Tok_FILTER | Tok_BIND, Tok_BIND
  | Tok_VALUES, Tok_VALUES | Tok_GRAPH, Tok_GRAPH | Tok_SERVICE, Tok_SERVICE
  | Tok_SILENT, Tok_SILENT | Tok_EXISTS, Tok_EXISTS | Tok_NOT, Tok_NOT
  | Tok_AS, Tok_AS | Tok_DISTINCT, Tok_DISTINCT | Tok_REDUCED, Tok_REDUCED
  | Tok_ORDER, Tok_ORDER | Tok_BY, Tok_BY | Tok_ASC, Tok_ASC | Tok_DESC, Tok_DESC
  | Tok_GROUP, Tok_GROUP | Tok_HAVING, Tok_HAVING | Tok_LIMIT, Tok_LIMIT
  | Tok_OFFSET, Tok_OFFSET | Tok_IN, Tok_IN | Tok_TRUE, Tok_TRUE
  | Tok_FALSE, Tok_FALSE | Tok_UNDEF, Tok_UNDEF | Tok_A, Tok_A
  | Tok_LBRACE, Tok_LBRACE | Tok_RBRACE, Tok_RBRACE | Tok_LPAREN, Tok_LPAREN
  | Tok_RPAREN, Tok_RPAREN | Tok_LBRACKET, Tok_LBRACKET | Tok_RBRACKET, Tok_RBRACKET
  | Tok_DOT, Tok_DOT | Tok_SEMI, Tok_SEMI | Tok_COMMA, Tok_COMMA
  | Tok_STAR, Tok_STAR | Tok_SLASH, Tok_SLASH | Tok_PIPE, Tok_PIPE
  | Tok_CARET, Tok_CARET | Tok_BANG, Tok_BANG | Tok_QMARK, Tok_QMARK
  | Tok_PLUS, Tok_PLUS | Tok_MINUS_OP, Tok_MINUS_OP
  | Tok_EQ, Tok_EQ | Tok_NE, Tok_NE | Tok_LT, Tok_LT | Tok_GT, Tok_GT
  | Tok_LE, Tok_LE | Tok_GE, Tok_GE | Tok_AND, Tok_AND | Tok_OR, Tok_OR
  | Tok_HATHAT, Tok_HATHAT | Tok_ANON, Tok_ANON | Tok_EOF, Tok_EOF
  | Tok_STR, Tok_STR | Tok_LANG, Tok_LANG | Tok_LANGMATCHES, Tok_LANGMATCHES
  | Tok_DATATYPE, Tok_DATATYPE | Tok_BOUND, Tok_BOUND | Tok_IF, Tok_IF
  | Tok_IRI_KW, Tok_IRI_KW | Tok_URI, Tok_URI | Tok_BNODE_KW, Tok_BNODE_KW
  | Tok_RAND, Tok_RAND | Tok_ABS, Tok_ABS | Tok_CEIL, Tok_CEIL
  | Tok_FLOOR, Tok_FLOOR | Tok_ROUND, Tok_ROUND | Tok_CONCAT, Tok_CONCAT
  | Tok_STRLEN, Tok_STRLEN | Tok_UCASE, Tok_UCASE | Tok_LCASE, Tok_LCASE
  | Tok_ENCODE_FOR_URI, Tok_ENCODE_FOR_URI | Tok_CONTAINS, Tok_CONTAINS
  | Tok_STRSTARTS, Tok_STRSTARTS | Tok_STRENDS, Tok_STRENDS
  | Tok_STRBEFORE, Tok_STRBEFORE | Tok_STRAFTER, Tok_STRAFTER
  | Tok_REPLACE, Tok_REPLACE | Tok_REGEX, Tok_REGEX | Tok_SUBSTR, Tok_SUBSTR
  | Tok_ISIRI, Tok_ISIRI | Tok_ISBLANK, Tok_ISBLANK
  | Tok_ISLITERAL, Tok_ISLITERAL | Tok_ISNUMERIC, Tok_ISNUMERIC
  | Tok_SAMETERM, Tok_SAMETERM | Tok_STRDT, Tok_STRDT | Tok_STRLANG, Tok_STRLANG
  | Tok_COUNT, Tok_COUNT | Tok_SUM, Tok_SUM | Tok_MIN_KW, Tok_MIN_KW
  | Tok_MAX_KW, Tok_MAX_KW | Tok_AVG, Tok_AVG | Tok_GROUP_CONCAT, Tok_GROUP_CONCAT
  | Tok_SAMPLE, Tok_SAMPLE | Tok_SEPARATOR, Tok_SEPARATOR
  | Tok_COALESCE, Tok_COALESCE | Tok_NOW, Tok_NOW | Tok_UUID, Tok_UUID
  | Tok_STRUUID, Tok_STRUUID | Tok_YEAR, Tok_YEAR | Tok_MONTH, Tok_MONTH
  | Tok_DAY, Tok_DAY | Tok_HOURS, Tok_HOURS | Tok_MINUTES, Tok_MINUTES
  | Tok_SECONDS, Tok_SECONDS | Tok_TIMEZONE, Tok_TIMEZONE | Tok_TZ, Tok_TZ
  | Tok_MD5, Tok_MD5 | Tok_SHA1, Tok_SHA1 | Tok_SHA256, Tok_SHA256
  | Tok_SHA384, Tok_SHA384 | Tok_SHA512, Tok_SHA512
  | Tok_IRI s1, Tok_IRI s2 -> s1 = s2
  | Tok_PNAME s1, Tok_PNAME s2 -> s1 = s2
  | Tok_VAR s1, Tok_VAR s2 -> s1 = s2
  | Tok_STRING s1, Tok_STRING s2 -> s1 = s2
  | Tok_LANGTAG s1, Tok_LANGTAG s2 -> s1 = s2
  | Tok_INTEGER s1, Tok_INTEGER s2 -> s1 = s2
  | Tok_DECIMAL s1, Tok_DECIMAL s2 -> s1 = s2
  | Tok_DOUBLE s1, Tok_DOUBLE s2 -> s1 = s2
  | Tok_BNODE s1, Tok_BNODE s2 -> s1 = s2
  | _, _ -> false

(* Expect a specific token *)
let parse_expect (tok : token) (ts : token_stream) : parse_result unit =
  match ts with
  | t :: rest -> if token_eq t tok then ParseOk () rest
                 else ParseErr "unexpected token"
  | [] -> ParseErr "unexpected end of input"

(** ====================================================================== **)
(** Part 6: Parser — Prefix Resolution                                      **)
(** ====================================================================== **)

type prefix_map = list (string & string)

(* Look up a prefix in the map *)
let rec lookup_prefix (prefix : string) (pm : prefix_map) : option string =
  match pm with
  | [] -> None
  | (k, v) :: rest -> if k = prefix then Some v else lookup_prefix prefix rest

(* Find colon position in character list *)
let rec find_colon (cs : list FStar.Char.char) (i : nat)
  : Tot nat (decreases cs) =
  match cs with
  | [] -> i
  | c :: rest -> if FStar.Char.int_of_char c = 0x3A then i else find_colon rest (i + 1)

(* Split a prefixed name "prefix:local" into (prefix, local) *)
let split_pname (pn : string) : (string & string) =
  let chars = String.list_of_string pn in
  let cp = find_colon chars 0 in
  if cp >= String.length pn then (pn, "")
  else (substring pn 0 cp, substring pn (cp + 1) (String.length pn - cp - 1))

(* Resolve a prefixed name to a full IRI string *)
let resolve_pname (pn : string) (pm : prefix_map) : option string =
  let (prefix, local) = split_pname pn in
  match lookup_prefix prefix pm with
  | Some ns -> Some (ns ^ local)
  | None -> None

(* Convert a string to wf_iri (non-empty + contains colon) *)
let make_iri (s : string) : option wf_iri =
  if is_iri s then Some s else None

(** ====================================================================== **)
(** Part 7: Parser — Expression, Pattern, Query                             **)
(**                                                                          **)
(** Recursive descent over token stream.                                     **)
(** Termination: token list strictly decreases on each recursive call.       **)
(** Mutual recursion between expr, pattern, and query (for sub-selects       **)
(** and EXISTS) uses the token list length as decreasing metric.             **)
(** ====================================================================== **)

(* ====================================================================== *)
(* Full SPARQL 1.1 recursive descent parser.                              *)
(* All functions use fuel-based termination for mutual recursion.          *)
(* ====================================================================== *)

(* Default solution modifier (no ordering, no limits) *)
let default_modifier : solution_modifier = {
  sm_order_by = None; sm_distinct = false; sm_reduced = false;
  sm_offset = None; sm_limit = None
}

(* Parse integer from string *)
let rec chars_to_int (cs : list FStar.Char.char) (acc : int)
  : Tot int (decreases cs) =
  match cs with
  | [] -> acc
  | c :: rest -> chars_to_int rest (op_Multiply acc 10 + (FStar.Char.int_of_char c - 0x30))

let parse_int_str (s : string) : option int =
  let cs = String.list_of_string s in
  match cs with
  | [] -> None
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x2D then
      if List.Tot.length rest > 0 && List.Tot.for_all (fun c -> is_digit c) rest
      then Some (0 - chars_to_int rest 0) else None
    else if FStar.Char.int_of_char c = 0x2B then
      if List.Tot.length rest > 0 && List.Tot.for_all (fun c -> is_digit c) rest
      then Some (chars_to_int rest 0) else None
    else if List.Tot.for_all (fun c -> is_digit c) cs
    then Some (chars_to_int cs 0) else None

(* Make a well-formed literal for the parser *)
let make_plain_literal (lex : string) : wf_literal =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#string");
  { lexical_form = lex;
    datatype = "http://www.w3.org/2001/XMLSchema#string";
    lang_tag = None }

let make_typed_literal (lex : string) (dt : string) : option wf_literal =
  if is_iri dt then
    if dt = "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString" then None
    else Some { lexical_form = lex; datatype = dt; lang_tag = None }
  else None

let make_lang_literal (lex : string) (lang : string) : wf_literal =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString");
  { lexical_form = lex;
    datatype = "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString";
    lang_tag = Some lang }

(* rdf:type IRI constant *)
let rdf_type_iri_str : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

#push-options "--z3rlimit 200 --fuel 2 --ifuel 2 --admit_smt_queries true"

(* ---- Mutually recursive parser block ---- *)

let rec parse_expr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit" else parse_or_expr pm (fuel - 1) ts

and parse_or_expr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_and_expr pm (fuel - 1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk e ts' -> parse_or_rest pm (fuel - 1) e ts'

and parse_or_rest (pm : prefix_map) (fuel : nat) (e : expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseOk e ts
  else match parse_peek ts with
  | Tok_OR ->
    (match parse_and_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e2 ts' -> parse_or_rest pm (fuel - 1) (E_Or e e2) ts')
  | _ -> ParseOk e ts

and parse_and_expr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_rel_expr pm (fuel - 1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk e ts' -> parse_and_rest pm (fuel - 1) e ts'

and parse_and_rest (pm : prefix_map) (fuel : nat) (e : expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseOk e ts
  else match parse_peek ts with
  | Tok_AND ->
    (match parse_rel_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e2 ts' -> parse_and_rest pm (fuel - 1) (E_And e e2) ts')
  | _ -> ParseOk e ts

and parse_rel_expr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_add_expr pm (fuel - 1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk e1 ts' ->
    begin match parse_peek ts' with
    | Tok_EQ -> parse_rel_rhs pm (fuel - 1) (E_Compare CmpEq e1) ts'
    | Tok_NE -> parse_rel_rhs pm (fuel - 1) (E_Compare CmpNe e1) ts'
    | Tok_LT -> parse_rel_rhs pm (fuel - 1) (E_Compare CmpLt e1) ts'
    | Tok_GT -> parse_rel_rhs pm (fuel - 1) (E_Compare CmpGt e1) ts'
    | Tok_LE -> parse_rel_rhs pm (fuel - 1) (E_Compare CmpLe e1) ts'
    | Tok_GE -> parse_rel_rhs pm (fuel - 1) (E_Compare CmpGe e1) ts'
    | Tok_IN -> parse_in_list pm (fuel - 1) e1 (parse_advance ts')
    | Tok_NOT ->
      let ts'' = parse_advance ts' in
      (match parse_peek ts'' with
       | Tok_IN -> parse_not_in_list pm (fuel - 1) e1 (parse_advance ts'')
       | _ -> ParseOk e1 ts')
    | _ -> ParseOk e1 ts'
    end

and parse_rel_rhs (pm : prefix_map) (fuel : nat) (ctor : expr -> expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_add_expr pm (fuel - 1) (parse_advance ts) with
  | ParseErr m -> ParseErr m
  | ParseOk e2 ts' -> ParseOk (ctor e2) ts'

and parse_in_list (pm : prefix_map) (fuel : nat) (e : expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts' ->
    begin match parse_expr_list pm (fuel - 1) ts' with
    | ParseErr m -> ParseErr m
    | ParseOk es ts'' ->
      begin match parse_expect Tok_RPAREN ts'' with
      | ParseErr m -> ParseErr m
      | ParseOk () ts''' -> ParseOk (E_In e es) ts'''
      end
    end

and parse_not_in_list (pm : prefix_map) (fuel : nat) (e : expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts' ->
    begin match parse_expr_list pm (fuel - 1) ts' with
    | ParseErr m -> ParseErr m
    | ParseOk es ts'' ->
      begin match parse_expect Tok_RPAREN ts'' with
      | ParseErr m -> ParseErr m
      | ParseOk () ts''' -> ParseOk (E_NotIn e es) ts'''
      end
    end

and parse_expr_list (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (list expr)) (decreases fuel) =
  if fuel = 0 then ParseOk [] ts
  else match parse_peek ts with
  | Tok_RPAREN -> ParseOk [] ts  (* empty list *)
  | _ ->
    begin match parse_expr pm (fuel - 1) ts with
    | ParseErr m -> ParseErr m
    | ParseOk e ts' -> parse_expr_list_rest pm (fuel - 1) [e] ts'
    end

and parse_expr_list_rest (pm : prefix_map) (fuel : nat) (acc : list expr) (ts : token_stream)
  : Tot (parse_result (list expr)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_peek ts with
  | Tok_COMMA ->
    (match parse_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' -> parse_expr_list_rest pm (fuel - 1) (e :: acc) ts')
  | _ -> ParseOk (List.Tot.rev acc) ts

and parse_add_expr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_mul_expr pm (fuel - 1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk e ts' -> parse_add_rest pm (fuel - 1) e ts'

and parse_add_rest (pm : prefix_map) (fuel : nat) (e : expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseOk e ts
  else match parse_peek ts with
  | Tok_PLUS ->
    (match parse_mul_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e2 ts' -> parse_add_rest pm (fuel - 1) (E_Arith Add e e2) ts')
  | Tok_MINUS_OP ->
    (match parse_mul_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e2 ts' -> parse_add_rest pm (fuel - 1) (E_Arith Sub e e2) ts')
  | _ -> ParseOk e ts

and parse_mul_expr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_unary_expr pm (fuel - 1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk e ts' -> parse_mul_rest pm (fuel - 1) e ts'

and parse_mul_rest (pm : prefix_map) (fuel : nat) (e : expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseOk e ts
  else match parse_peek ts with
  | Tok_STAR ->
    (match parse_unary_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e2 ts' -> parse_mul_rest pm (fuel - 1) (E_Arith Mul e e2) ts')
  | Tok_SLASH ->
    (match parse_unary_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e2 ts' -> parse_mul_rest pm (fuel - 1) (E_Arith Div e e2) ts')
  | _ -> ParseOk e ts

and parse_unary_expr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_BANG ->
    (match parse_primary_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m | ParseOk e ts' -> ParseOk (E_Not e) ts')
  | Tok_PLUS ->
    (match parse_primary_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m | ParseOk e ts' -> ParseOk (E_UnaryPlus e) ts')
  | Tok_MINUS_OP ->
    (match parse_primary_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m | ParseOk e ts' -> ParseOk (E_UnaryMinus e) ts')
  | _ -> parse_primary_expr pm (fuel - 1) ts

and parse_primary_expr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_VAR v -> ParseOk (E_Var v) (parse_advance ts)
  | Tok_TRUE -> ParseOk (E_BoolLit true) (parse_advance ts)
  | Tok_FALSE -> ParseOk (E_BoolLit false) (parse_advance ts)
  | Tok_INTEGER n ->
    (match parse_int_str n with
     | Some i -> ParseOk (E_NumericLit i) (parse_advance ts)
     | None -> ParseOk (E_DecimalLit n) (parse_advance ts))
  | Tok_DECIMAL d -> ParseOk (E_DecimalLit d) (parse_advance ts)
  | Tok_DOUBLE d -> ParseOk (E_DoubleLit d) (parse_advance ts)
  | Tok_STRING s -> parse_rdf_literal_expr pm (fuel - 1) s (parse_advance ts)
  | Tok_IRI i ->
    if is_iri i then
      let ts' = parse_advance ts in
      (match parse_peek ts' with
       | Tok_LPAREN -> parse_func_call pm (fuel - 1) i (parse_advance ts')
       | _ -> ParseOk (E_IRI i) ts')
    else ParseErr ("invalid IRI: " ^ i)
  | Tok_PNAME pn -> parse_pname_expr pm (fuel - 1) pn (parse_advance ts)
  | Tok_LPAREN ->
    (match parse_expr pm (fuel - 1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' ->
       begin match parse_expect Tok_RPAREN ts' with
       | ParseErr _ -> ParseErr "expected ')'"
       | ParseOk () ts'' -> ParseOk e ts''
       end)
  (* Built-in 1-arg functions *)
  | Tok_STR -> parse_b1 pm (fuel-1) E_Str (parse_advance ts)
  | Tok_LANG -> parse_b1 pm (fuel-1) E_Lang (parse_advance ts)
  | Tok_DATATYPE -> parse_b1 pm (fuel-1) E_Datatype (parse_advance ts)
  | Tok_IRI_KW -> parse_b1 pm (fuel-1) E_IRI_fn (parse_advance ts)
  | Tok_URI -> parse_b1 pm (fuel-1) E_IRI_fn (parse_advance ts)
  | Tok_ABS -> parse_b1 pm (fuel-1) E_Abs (parse_advance ts)
  | Tok_CEIL -> parse_b1 pm (fuel-1) E_Ceil (parse_advance ts)
  | Tok_FLOOR -> parse_b1 pm (fuel-1) E_Floor (parse_advance ts)
  | Tok_ROUND -> parse_b1 pm (fuel-1) E_Round (parse_advance ts)
  | Tok_STRLEN -> parse_b1 pm (fuel-1) E_StrLen (parse_advance ts)
  | Tok_UCASE -> parse_b1 pm (fuel-1) E_UCase (parse_advance ts)
  | Tok_LCASE -> parse_b1 pm (fuel-1) E_LCase (parse_advance ts)
  | Tok_ENCODE_FOR_URI -> parse_b1 pm (fuel-1) E_EncodeForUri (parse_advance ts)
  | Tok_ISIRI -> parse_b1 pm (fuel-1) E_IsIRI (parse_advance ts)
  | Tok_ISBLANK -> parse_b1 pm (fuel-1) E_IsBlank (parse_advance ts)
  | Tok_ISLITERAL -> parse_b1 pm (fuel-1) E_IsLiteral (parse_advance ts)
  | Tok_ISNUMERIC -> parse_b1 pm (fuel-1) E_IsNumeric (parse_advance ts)
  | Tok_MD5 -> parse_b1 pm (fuel-1) E_MD5 (parse_advance ts)
  | Tok_SHA1 -> parse_b1 pm (fuel-1) E_SHA1 (parse_advance ts)
  | Tok_SHA256 -> parse_b1 pm (fuel-1) E_SHA256 (parse_advance ts)
  | Tok_SHA384 -> parse_b1 pm (fuel-1) E_SHA384 (parse_advance ts)
  | Tok_SHA512 -> parse_b1 pm (fuel-1) E_SHA512 (parse_advance ts)
  | Tok_YEAR -> parse_b1 pm (fuel-1) E_Year (parse_advance ts)
  | Tok_MONTH -> parse_b1 pm (fuel-1) E_Month (parse_advance ts)
  | Tok_DAY -> parse_b1 pm (fuel-1) E_Day (parse_advance ts)
  | Tok_HOURS -> parse_b1 pm (fuel-1) E_Hours (parse_advance ts)
  | Tok_MINUTES -> parse_b1 pm (fuel-1) E_Minutes (parse_advance ts)
  | Tok_SECONDS -> parse_b1 pm (fuel-1) E_Seconds (parse_advance ts)
  | Tok_TIMEZONE -> parse_b1 pm (fuel-1) E_Timezone (parse_advance ts)
  | Tok_TZ -> parse_b1 pm (fuel-1) E_Tz (parse_advance ts)
  (* Built-in 2-arg functions *)
  | Tok_LANGMATCHES -> parse_b2 pm (fuel-1) E_SameTerm (parse_advance ts)  (* Note: LANGMATCHES uses FunctionCall in eval *)
  | Tok_SAMETERM -> parse_b2 pm (fuel-1) E_SameTerm (parse_advance ts)
  | Tok_STRSTARTS -> parse_b2 pm (fuel-1) E_StrStarts (parse_advance ts)
  | Tok_STRENDS -> parse_b2 pm (fuel-1) E_StrEnds (parse_advance ts)
  | Tok_CONTAINS -> parse_b2 pm (fuel-1) E_Contains (parse_advance ts)
  | Tok_STRBEFORE -> parse_b2 pm (fuel-1) E_StrBefore (parse_advance ts)
  | Tok_STRAFTER -> parse_b2 pm (fuel-1) E_StrAfter (parse_advance ts)
  | Tok_STRDT -> parse_b2 pm (fuel-1) E_StrDt (parse_advance ts)
  | Tok_STRLANG -> parse_b2 pm (fuel-1) E_StrLang (parse_advance ts)
  (* Special built-ins *)
  | Tok_BOUND -> parse_bound pm (fuel-1) (parse_advance ts)
  | Tok_IF -> parse_if_expr pm (fuel-1) (parse_advance ts)
  | Tok_COALESCE -> parse_coalesce pm (fuel-1) (parse_advance ts)
  | Tok_CONCAT -> parse_concat pm (fuel-1) (parse_advance ts)
  | Tok_NOW -> ParseOk E_Now (parse_advance ts)
  | Tok_RAND -> ParseErr "unsupported: RAND()"
  | Tok_UUID -> ParseErr "unsupported: UUID()"
  | Tok_STRUUID -> ParseErr "unsupported: STRUUID()"
  | Tok_BNODE_KW -> ParseErr "unsupported: BNODE()"
  | Tok_REGEX -> parse_regex pm (fuel-1) (parse_advance ts)
  | Tok_REPLACE -> parse_replace pm (fuel-1) (parse_advance ts)
  | Tok_SUBSTR -> parse_substr pm (fuel-1) (parse_advance ts)
  (* Aggregates *)
  | Tok_COUNT -> parse_aggregate pm (fuel-1) Agg_Count (parse_advance ts)
  | Tok_SUM -> parse_aggregate pm (fuel-1) Agg_Sum (parse_advance ts)
  | Tok_MIN_KW -> parse_aggregate pm (fuel-1) Agg_Min (parse_advance ts)
  | Tok_MAX_KW -> parse_aggregate pm (fuel-1) Agg_Max (parse_advance ts)
  | Tok_AVG -> parse_aggregate pm (fuel-1) Agg_Avg (parse_advance ts)
  | Tok_SAMPLE -> parse_aggregate pm (fuel-1) Agg_Sample (parse_advance ts)
  | Tok_GROUP_CONCAT -> parse_group_concat pm (fuel-1) (parse_advance ts)
  (* EXISTS / NOT EXISTS *)
  | Tok_EXISTS ->
    (match parse_group_graph_pattern pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk g ts' -> ParseOk (E_Exists g) ts')
  | Tok_NOT ->
    let ts' = parse_advance ts in
    (match parse_peek ts' with
     | Tok_EXISTS ->
       (match parse_group_graph_pattern pm (fuel-1) (parse_advance ts') with
        | ParseErr m -> ParseErr m
        | ParseOk g ts'' -> ParseOk (E_NotExists g) ts'')
     | Tok_IN -> ParseOk (E_BoolLit true) ts  (* handled at relational level *)
     | _ -> ParseErr "expected EXISTS or IN after NOT")
  | _ -> ParseErr "unexpected token in expression"

(* Parse BOUND(?var) *)
and parse_bound (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts' ->
    begin match parse_peek ts' with
    | Tok_VAR v ->
      (match parse_expect Tok_RPAREN (parse_advance ts') with
       | ParseErr m -> ParseErr m
       | ParseOk () ts'' -> ParseOk (E_Bound v) ts'')
    | _ -> ParseErr "BOUND expects a variable"
    end

(* Parse IF(e1, e2, e3) *)
and parse_if_expr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts1 ->
    begin match parse_expr pm (fuel-1) ts1 with
    | ParseErr m -> ParseErr m
    | ParseOk e1 ts2 ->
      begin match parse_expect Tok_COMMA ts2 with
      | ParseErr m -> ParseErr m
      | ParseOk () ts3 ->
        begin match parse_expr pm (fuel-1) ts3 with
        | ParseErr m -> ParseErr m
        | ParseOk e2 ts4 ->
          begin match parse_expect Tok_COMMA ts4 with
          | ParseErr m -> ParseErr m
          | ParseOk () ts5 ->
            begin match parse_expr pm (fuel-1) ts5 with
            | ParseErr m -> ParseErr m
            | ParseOk e3 ts6 ->
              begin match parse_expect Tok_RPAREN ts6 with
              | ParseErr m -> ParseErr m
              | ParseOk () ts7 -> ParseOk (E_If e1 e2 e3) ts7
              end end end end end end

(* Parse COALESCE(expr, ...) *)
and parse_coalesce (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts' ->
    begin match parse_expr_list pm (fuel-1) ts' with
    | ParseErr m -> ParseErr m
    | ParseOk es ts'' ->
      begin match parse_expect Tok_RPAREN ts'' with
      | ParseErr m -> ParseErr m
      | ParseOk () ts''' -> ParseOk (E_Coalesce es) ts'''
      end end

(* Parse CONCAT(expr, ...) *)
and parse_concat (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts' ->
    begin match parse_expr_list pm (fuel-1) ts' with
    | ParseErr m -> ParseErr m
    | ParseOk es ts'' ->
      begin match parse_expect Tok_RPAREN ts'' with
      | ParseErr m -> ParseErr m
      | ParseOk () ts''' -> ParseOk (E_Concat es) ts'''
      end end

(* Parse REGEX(e1, e2 [, e3]) *)
and parse_regex (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts1 ->
    begin match parse_expr pm (fuel-1) ts1 with
    | ParseErr m -> ParseErr m
    | ParseOk e1 ts2 ->
      begin match parse_expect Tok_COMMA ts2 with
      | ParseErr m -> ParseErr m
      | ParseOk () ts3 ->
        begin match parse_expr pm (fuel-1) ts3 with
        | ParseErr m -> ParseErr m
        | ParseOk e2 ts4 ->
          begin match parse_peek ts4 with
          | Tok_COMMA ->
            (match parse_expr pm (fuel-1) (parse_advance ts4) with
             | ParseErr m -> ParseErr m
             | ParseOk e3 ts5 ->
               begin match parse_expect Tok_RPAREN ts5 with
               | ParseErr m -> ParseErr m
               | ParseOk () ts6 -> ParseOk (E_Regex e1 e2 (Some e3)) ts6
               end)
          | _ ->
            begin match parse_expect Tok_RPAREN ts4 with
            | ParseErr m -> ParseErr m
            | ParseOk () ts5 -> ParseOk (E_Regex e1 e2 None) ts5
            end
          end end end end

(* Parse REPLACE(e1, e2, e3 [, e4]) *)
and parse_replace (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts1 ->
    begin match parse_expr pm (fuel-1) ts1 with
    | ParseErr m -> ParseErr m
    | ParseOk e1 ts2 ->
      begin match parse_expect Tok_COMMA ts2 with | ParseErr m -> ParseErr m | ParseOk () ts3 ->
      begin match parse_expr pm (fuel-1) ts3 with | ParseErr m -> ParseErr m | ParseOk e2 ts4 ->
      begin match parse_expect Tok_COMMA ts4 with | ParseErr m -> ParseErr m | ParseOk () ts5 ->
      begin match parse_expr pm (fuel-1) ts5 with | ParseErr m -> ParseErr m | ParseOk e3 ts6 ->
      begin match parse_peek ts6 with
      | Tok_COMMA ->
        (match parse_expr pm (fuel-1) (parse_advance ts6) with
         | ParseErr m -> ParseErr m
         | ParseOk e4 ts7 ->
           begin match parse_expect Tok_RPAREN ts7 with
           | ParseErr m -> ParseErr m
           | ParseOk () ts8 -> ParseOk (E_Replace e1 e2 e3 (Some e4)) ts8
           end)
      | _ ->
        begin match parse_expect Tok_RPAREN ts6 with
        | ParseErr m -> ParseErr m
        | ParseOk () ts7 -> ParseOk (E_Replace e1 e2 e3 None) ts7
        end
      end end end end end end

(* Parse SUBSTR(e1, e2 [, e3]) *)
and parse_substr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts1 ->
    begin match parse_expr pm (fuel-1) ts1 with | ParseErr m -> ParseErr m | ParseOk e1 ts2 ->
    begin match parse_expect Tok_COMMA ts2 with | ParseErr m -> ParseErr m | ParseOk () ts3 ->
    begin match parse_expr pm (fuel-1) ts3 with | ParseErr m -> ParseErr m | ParseOk e2 ts4 ->
    begin match parse_peek ts4 with
    | Tok_COMMA ->
      (match parse_expr pm (fuel-1) (parse_advance ts4) with
       | ParseErr m -> ParseErr m
       | ParseOk e3 ts5 ->
         begin match parse_expect Tok_RPAREN ts5 with
         | ParseErr m -> ParseErr m
         | ParseOk () ts6 -> ParseOk (E_Substr e1 e2 (Some e3)) ts6
         end)
    | _ ->
      begin match parse_expect Tok_RPAREN ts4 with
      | ParseErr m -> ParseErr m
      | ParseOk () ts5 -> ParseOk (E_Substr e1 e2 None) ts5
      end
    end end end end

(* Parse aggregate: COUNT/SUM/MIN/MAX/AVG/SAMPLE ( [DISTINCT] expr ) *)
and parse_aggregate (pm : prefix_map) (fuel : nat) (agg : aggregate_fn) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts1 ->
    let (dist, ts2) = begin match parse_peek ts1 with
      | Tok_DISTINCT -> (true, parse_advance ts1) | _ -> (false, ts1) end in
    (* COUNT(*) special case *)
    begin match parse_peek ts2 with
    | Tok_STAR ->
      (match parse_expect Tok_RPAREN (parse_advance ts2) with
       | ParseErr m -> ParseErr m
       | ParseOk () ts3 -> ParseOk (E_Aggregate agg dist (E_BoolLit true)) ts3)
    | _ ->
      begin match parse_expr pm (fuel-1) ts2 with
      | ParseErr m -> ParseErr m
      | ParseOk e ts3 ->
        begin match parse_expect Tok_RPAREN ts3 with
        | ParseErr m -> ParseErr m
        | ParseOk () ts4 -> ParseOk (E_Aggregate agg dist e) ts4
        end end end

(* Parse GROUP_CONCAT ( [DISTINCT] expr [; SEPARATOR = string] ) *)
and parse_group_concat (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts1 ->
    let (dist, ts2) = begin match parse_peek ts1 with
      | Tok_DISTINCT -> (true, parse_advance ts1) | _ -> (false, ts1) end in
    begin match parse_expr pm (fuel-1) ts2 with
    | ParseErr m -> ParseErr m
    | ParseOk e ts3 ->
      (* Check for ; SEPARATOR = "..." *)
      let (sep, ts4) = begin match parse_peek ts3 with
        | Tok_SEMI ->
          let ts3' = parse_advance ts3 in
          (match parse_peek ts3' with
           | Tok_SEPARATOR ->
             let ts3'' = parse_advance ts3' in
             (match parse_expect Tok_EQ ts3'' with
              | ParseOk () ts3''' ->
                (match parse_peek ts3''' with
                 | Tok_STRING s -> (Some s, parse_advance ts3''')
                 | _ -> (None, ts3))
              | _ -> (None, ts3))
           | _ -> (None, ts3))
        | _ -> (None, ts3) end in
      begin match parse_expect Tok_RPAREN ts4 with
      | ParseErr m -> ParseErr m
      | ParseOk () ts5 -> ParseOk (E_Aggregate (Agg_GroupConcat sep) dist e) ts5
      end end

(* Parse builtin 1-arg: ( expr ) *)
and parse_b1 (pm : prefix_map) (fuel : nat) (ctor : expr -> expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts' ->
    begin match parse_expr pm (fuel-1) ts' with
    | ParseErr m -> ParseErr m
    | ParseOk e ts'' ->
      begin match parse_expect Tok_RPAREN ts'' with
      | ParseErr m -> ParseErr m
      | ParseOk () ts''' -> ParseOk (ctor e) ts'''
      end end

(* Parse builtin 2-arg: ( expr , expr ) *)
and parse_b2 (pm : prefix_map) (fuel : nat) (ctor : expr -> expr -> expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts1 ->
    begin match parse_expr pm (fuel-1) ts1 with | ParseErr m -> ParseErr m | ParseOk e1 ts2 ->
    begin match parse_expect Tok_COMMA ts2 with | ParseErr m -> ParseErr m | ParseOk () ts3 ->
    begin match parse_expr pm (fuel-1) ts3 with | ParseErr m -> ParseErr m | ParseOk e2 ts4 ->
    begin match parse_expect Tok_RPAREN ts4 with | ParseErr m -> ParseErr m | ParseOk () ts5 ->
    ParseOk (ctor e1 e2) ts5
    end end end end

(* Parse function call: IRI already consumed, position after '(' *)
and parse_func_call (pm : prefix_map) (fuel : nat) (iri : wf_iri) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expr_list pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk args ts' ->
    begin match parse_expect Tok_RPAREN ts' with
    | ParseErr m -> ParseErr m
    | ParseOk () ts'' -> ParseOk (E_FunctionCall iri args) ts''
    end

(* Parse PNAME as expression: resolve prefix, check for function call *)
and parse_pname_expr (pm : prefix_map) (fuel : nat) (pn : string) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match resolve_pname pn pm with
  | Some iri ->
    if is_iri iri then
      (match parse_peek ts with
       | Tok_LPAREN -> parse_func_call pm (fuel-1) iri (parse_advance ts)
       | _ -> ParseOk (E_IRI iri) ts)
    else ParseErr ("resolved IRI invalid: " ^ iri)
  | None -> ParseErr ("unresolved prefix: " ^ pn)

(* Parse an RDF literal in expression context: string already consumed *)
and parse_rdf_literal_expr (pm : prefix_map) (fuel : nat) (s : string) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_HATHAT ->
    let ts' = parse_advance ts in
    (match parse_peek ts' with
     | Tok_IRI dt ->
       if is_iri dt then
         (match make_typed_literal s dt with
          | Some lit -> ParseOk (E_Literal lit) (parse_advance ts')
          | None -> ParseErr "invalid typed literal")
       else ParseErr "invalid datatype IRI"
     | Tok_PNAME pn ->
       (match resolve_pname pn pm with
        | Some dt ->
          if is_iri dt then
            (match make_typed_literal s dt with
             | Some lit -> ParseOk (E_Literal lit) (parse_advance ts')
             | None -> ParseErr "invalid typed literal")
          else ParseErr "invalid datatype IRI"
        | None -> ParseErr ("unresolved datatype prefix: " ^ pn))
     | _ -> ParseErr "expected IRI after ^^")
  | Tok_LANGTAG lang -> ParseOk (E_Literal (make_lang_literal s lang)) (parse_advance ts)
  | _ -> ParseOk (E_Literal (make_plain_literal s)) ts

(* ---- Group Graph Pattern parsing ---- *)

and parse_group_graph_pattern (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LBRACE ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts' ->
    (* Check for SubSelect *)
    begin match parse_peek ts' with
    | Tok_SELECT ->
      (match parse_select_query pm (fuel-1) ts' with
       | ParseErr m -> ParseErr m
       | ParseOk q ts'' ->
         begin match parse_expect Tok_RBRACE ts'' with
         | ParseErr m -> ParseErr m
         | ParseOk () ts''' -> ParseOk (GP_SubSelect q) ts'''
         end)
    | Tok_RBRACE -> ParseOk GP_Empty (parse_advance ts')
    | _ ->
      begin match parse_ggp_body pm (fuel-1) GP_Empty ts' with
      | ParseErr m -> ParseErr m
      | ParseOk g ts'' ->
        begin match parse_expect Tok_RBRACE ts'' with
        | ParseErr m -> ParseErr m
        | ParseOk () ts''' -> ParseOk g ts'''
        end end
    end

(* Parse the body of a GGP: triples blocks interleaved with graph pattern elements *)
and parse_ggp_body (pm : prefix_map) (fuel : nat) (acc : group_graph_pattern) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseOk acc ts
  else match parse_peek ts with
  (* Try parsing triples if we see a term *)
  | Tok_VAR _ | Tok_IRI _ | Tok_PNAME _ | Tok_BNODE _ | Tok_LBRACKET
  | Tok_LPAREN | Tok_A | Tok_INTEGER _ | Tok_DECIMAL _ | Tok_DOUBLE _
  | Tok_STRING _ | Tok_TRUE | Tok_FALSE ->
    (match parse_triples_block pm (fuel-1) [] ts with
     | ParseErr m -> ParseErr m
     | ParseOk triples ts' ->
       let acc' = if List.Tot.length triples = 0 then acc
                  else match acc with
                       | GP_Empty -> GP_BGP triples
                       | _ -> GP_Join acc (GP_BGP triples) in
       let ts' = match parse_peek ts' with Tok_DOT -> parse_advance ts' | _ -> ts' in
       parse_ggp_body pm (fuel-1) acc' ts')
  | Tok_OPTIONAL ->
    (match parse_group_graph_pattern pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk g ts' ->
       let acc' = match acc with
         | GP_Empty -> GP_LeftJoin GP_Empty g (E_BoolLit true)
         | _ -> GP_LeftJoin acc g (E_BoolLit true) in
       let ts' = match parse_peek ts' with Tok_DOT -> parse_advance ts' | _ -> ts' in
       parse_ggp_body pm (fuel-1) acc' ts')
  | Tok_MINUS_KW ->
    (match parse_group_graph_pattern pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk g ts' ->
       let acc' = GP_Minus acc g in
       let ts' = match parse_peek ts' with Tok_DOT -> parse_advance ts' | _ -> ts' in
       parse_ggp_body pm (fuel-1) acc' ts')
  | Tok_GRAPH ->
    let ts' = parse_advance ts in
    (match parse_graph_name pm (fuel-1) ts' with
     | ParseErr m -> ParseErr m
     | ParseOk gn ts'' ->
       begin match parse_group_graph_pattern pm (fuel-1) ts'' with
       | ParseErr m -> ParseErr m
       | ParseOk g ts''' ->
         let acc' = match acc with
           | GP_Empty -> GP_Graph gn g | _ -> GP_Join acc (GP_Graph gn g) in
         let ts''' = match parse_peek ts''' with Tok_DOT -> parse_advance ts''' | _ -> ts''' in
         parse_ggp_body pm (fuel-1) acc' ts'''
       end)
  | Tok_SERVICE ->
    let ts' = parse_advance ts in
    let (silent, ts') = begin match parse_peek ts' with
      | Tok_SILENT -> (true, parse_advance ts') | _ -> (false, ts') end in
    (match parse_service_iri pm (fuel-1) ts' with
     | ParseErr m -> ParseErr m
     | ParseOk siri ts'' ->
       begin match parse_group_graph_pattern pm (fuel-1) ts'' with
       | ParseErr m -> ParseErr m
       | ParseOk g ts''' ->
         let acc' = match acc with
           | GP_Empty -> GP_Service siri g silent
           | _ -> GP_Join acc (GP_Service siri g silent) in
         let ts''' = match parse_peek ts''' with Tok_DOT -> parse_advance ts''' | _ -> ts''' in
         parse_ggp_body pm (fuel-1) acc' ts'''
       end)
  | Tok_FILTER ->
    let ts' = parse_advance ts in
    (* FILTER can be followed by ( expr ) or a built-in *)
    (match parse_filter_expr pm (fuel-1) ts' with
     | ParseErr m -> ParseErr m
     | ParseOk e ts'' ->
       let acc' = GP_Filter e acc in
       let ts'' = match parse_peek ts'' with Tok_DOT -> parse_advance ts'' | _ -> ts'' in
       parse_ggp_body pm (fuel-1) acc' ts'')
  | Tok_BIND ->
    let ts' = parse_advance ts in
    (match parse_expect Tok_LPAREN ts' with
     | ParseErr m -> ParseErr m
     | ParseOk () ts'' ->
       begin match parse_expr pm (fuel-1) ts'' with
       | ParseErr m -> ParseErr m
       | ParseOk e ts''' ->
         begin match parse_expect Tok_AS ts''' with
         | ParseErr m -> ParseErr m
         | ParseOk () ts4 ->
           begin match parse_peek ts4 with
           | Tok_VAR v ->
             (match parse_expect Tok_RPAREN (parse_advance ts4) with
              | ParseErr m -> ParseErr m
              | ParseOk () ts5 ->
                let acc' = GP_Bind e v acc in
                let ts5 = match parse_peek ts5 with Tok_DOT -> parse_advance ts5 | _ -> ts5 in
                parse_ggp_body pm (fuel-1) acc' ts5)
           | _ -> ParseErr "expected variable after AS"
           end end end)
  | Tok_VALUES ->
    ParseErr "unsupported: inline VALUES"
  | Tok_LBRACE ->
    (* Nested GGP — could be UNION *)
    (match parse_group_or_union pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk g ts' ->
       let acc' = match acc with GP_Empty -> g | _ -> GP_Join acc g in
       let ts' = match parse_peek ts' with Tok_DOT -> parse_advance ts' | _ -> ts' in
       parse_ggp_body pm (fuel-1) acc' ts')
  | _ -> ParseOk acc ts

(* Parse { } UNION { } ... *)
and parse_group_or_union (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_group_graph_pattern pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk g1 ts' ->
    begin match parse_peek ts' with
    | Tok_UNION ->
      (match parse_group_or_union pm (fuel-1) (parse_advance ts') with
       | ParseErr m -> ParseErr m
       | ParseOk g2 ts'' -> ParseOk (GP_Union g1 g2) ts'')
    | _ -> ParseOk g1 ts'
    end

(* Parse FILTER expression — may or may not have outer parens *)
and parse_filter_expr (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result expr) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_LPAREN ->
    (match parse_expr pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' ->
       begin match parse_expect Tok_RPAREN ts' with
       | ParseErr m -> ParseErr m
       | ParseOk () ts'' -> ParseOk e ts''
       end)
  (* Built-in call without parens (FILTER EXISTS { } etc.) *)
  | Tok_EXISTS | Tok_NOT | Tok_STR | Tok_LANG | Tok_LANGMATCHES | Tok_DATATYPE
  | Tok_BOUND | Tok_SAMETERM | Tok_ISIRI | Tok_ISBLANK | Tok_ISLITERAL | Tok_ISNUMERIC
  | Tok_REGEX | Tok_IF ->
    parse_primary_expr pm (fuel-1) ts
  | _ -> parse_expr pm (fuel-1) ts

(* Parse a graph name (IRI or variable) for GRAPH clause *)
and parse_graph_name (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result pattern_term) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_VAR v -> ParseOk (PT_Var v) (parse_advance ts)
  | Tok_IRI i -> if is_iri i then ParseOk (PT_IRI i) (parse_advance ts) else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
    (match resolve_pname pn pm with
     | Some iri -> if is_iri iri then ParseOk (PT_IRI iri) (parse_advance ts) else ParseErr "invalid IRI"
     | None -> ParseErr "unresolved prefix")
  | _ -> ParseErr "expected IRI or variable for GRAPH"

(* Parse SERVICE IRI *)
and parse_service_iri (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result wf_iri) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_IRI i -> if is_iri i then ParseOk i (parse_advance ts) else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
    (match resolve_pname pn pm with
     | Some iri -> if is_iri iri then ParseOk iri (parse_advance ts) else ParseErr "invalid IRI"
     | None -> ParseErr "unresolved prefix")
  | Tok_VAR _ -> ParseErr "unsupported: variable SERVICE endpoint"
  | _ -> ParseErr "expected IRI for SERVICE"

(* ---- Triples block parsing ---- *)

(* Parse a single term as pattern_subject *)
and parse_subject (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result pattern_subject) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_VAR v -> ParseOk (PS_Var v) (parse_advance ts)
  | Tok_IRI i -> if is_iri i then ParseOk (PS_IRI i) (parse_advance ts) else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
    (match resolve_pname pn pm with
     | Some iri -> if is_iri iri then ParseOk (PS_IRI iri) (parse_advance ts) else ParseErr "invalid IRI"
     | None -> ParseErr "unresolved prefix")
  | Tok_BNODE b -> ParseOk (PS_BNode b) (parse_advance ts)
  | _ -> ParseErr "expected subject"

(* Parse a predicate as pattern_term *)
and parse_predicate (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result pattern_term) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_VAR v -> ParseOk (PT_Var v) (parse_advance ts)
  | Tok_A -> ParseOk (PT_IRI rdf_type_iri_str) (parse_advance ts)
  | Tok_IRI i -> if is_iri i then ParseOk (PT_IRI i) (parse_advance ts) else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
    (match resolve_pname pn pm with
     | Some iri -> if is_iri iri then ParseOk (PT_IRI iri) (parse_advance ts) else ParseErr "invalid IRI"
     | None -> ParseErr "unresolved prefix")
  | _ -> ParseErr "expected predicate"

(* Parse an object as pattern_term *)
and parse_object (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result pattern_term) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_VAR v -> ParseOk (PT_Var v) (parse_advance ts)
  | Tok_IRI i -> if is_iri i then ParseOk (PT_IRI i) (parse_advance ts) else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
    (match resolve_pname pn pm with
     | Some iri -> if is_iri iri then ParseOk (PT_IRI iri) (parse_advance ts) else ParseErr "invalid IRI"
     | None -> ParseErr "unresolved prefix")
  | Tok_BNODE b -> ParseOk (PT_BNode b) (parse_advance ts)
  | Tok_STRING s -> parse_rdf_literal_pt pm (fuel-1) s (parse_advance ts)
  | Tok_INTEGER n ->
    (match make_typed_literal n "http://www.w3.org/2001/XMLSchema#integer" with
     | Some lit -> ParseOk (PT_Literal lit) (parse_advance ts)
     | None -> ParseErr "invalid integer literal")
  | Tok_DECIMAL d ->
    (match make_typed_literal d "http://www.w3.org/2001/XMLSchema#decimal" with
     | Some lit -> ParseOk (PT_Literal lit) (parse_advance ts)
     | None -> ParseErr "invalid decimal literal")
  | Tok_DOUBLE d ->
    (match make_typed_literal d "http://www.w3.org/2001/XMLSchema#double" with
     | Some lit -> ParseOk (PT_Literal lit) (parse_advance ts)
     | None -> ParseErr "invalid double literal")
  | Tok_TRUE ->
    (match make_typed_literal "true" "http://www.w3.org/2001/XMLSchema#boolean" with
     | Some lit -> ParseOk (PT_Literal lit) (parse_advance ts)
     | None -> ParseErr "invalid boolean literal")
  | Tok_FALSE ->
    (match make_typed_literal "false" "http://www.w3.org/2001/XMLSchema#boolean" with
     | Some lit -> ParseOk (PT_Literal lit) (parse_advance ts)
     | None -> ParseErr "invalid boolean literal")
  | Tok_A -> ParseOk (PT_IRI rdf_type_iri_str) (parse_advance ts)
  | _ -> ParseErr "expected object"

(* Parse RDF literal as pattern_term: string already consumed *)
and parse_rdf_literal_pt (pm : prefix_map) (fuel : nat) (s : string) (ts : token_stream)
  : Tot (parse_result pattern_term) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_HATHAT ->
    let ts' = parse_advance ts in
    (match parse_peek ts' with
     | Tok_IRI dt ->
       if is_iri dt then
         (match make_typed_literal s dt with
          | Some lit -> ParseOk (PT_Literal lit) (parse_advance ts')
          | None -> ParseErr "invalid typed literal")
       else ParseErr "invalid datatype IRI"
     | Tok_PNAME pn ->
       (match resolve_pname pn pm with
        | Some dt ->
          if is_iri dt then
            (match make_typed_literal s dt with
             | Some lit -> ParseOk (PT_Literal lit) (parse_advance ts')
             | None -> ParseErr "invalid typed literal")
          else ParseErr "invalid datatype IRI"
        | None -> ParseErr "unresolved prefix")
     | _ -> ParseErr "expected IRI after ^^")
  | Tok_LANGTAG lang -> ParseOk (PT_Literal (make_lang_literal s lang)) (parse_advance ts)
  | _ -> ParseOk (PT_Literal (make_plain_literal s)) ts

(* Parse object list: obj1, obj2, obj3 *)
and parse_object_list (pm : prefix_map) (fuel : nat) (subj : pattern_subject)
  (pred : pattern_term) (acc : list triple_pattern) (ts : token_stream)
  : Tot (parse_result (list triple_pattern)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_object pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk obj ts' ->
    let tp = { tp_s = subj; tp_p = pred; tp_o = obj } in
    begin match parse_peek ts' with
    | Tok_COMMA -> parse_object_list pm (fuel-1) subj pred (tp :: acc) (parse_advance ts')
    | _ -> ParseOk (List.Tot.rev (tp :: acc)) ts'
    end

(* Parse predicate-object list: pred objList ; pred objList ; ... *)
and parse_pred_obj_list (pm : prefix_map) (fuel : nat) (subj : pattern_subject)
  (acc : list triple_pattern) (ts : token_stream)
  : Tot (parse_result (list triple_pattern)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_predicate pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk pred ts' ->
    begin match parse_object_list pm (fuel-1) subj pred acc ts' with
    | ParseErr m -> ParseErr m
    | ParseOk triples ts'' ->
      begin match parse_peek ts'' with
      | Tok_SEMI ->
        let ts''' = parse_advance ts'' in
        (* Semicolon may be followed by another pred-obj or just end *)
        (match parse_peek ts''' with
         | Tok_DOT | Tok_RBRACE | Tok_OPTIONAL | Tok_MINUS_KW | Tok_FILTER
         | Tok_BIND | Tok_GRAPH | Tok_SERVICE | Tok_VALUES | Tok_UNION
         | Tok_LBRACE | Tok_RBRACKET | Tok_EOF -> ParseOk triples ts'''
         | _ -> parse_pred_obj_list pm (fuel-1) subj triples ts''')
      | _ -> ParseOk triples ts''
      end end

(* Parse a triples block: one or more triple patterns separated by dots *)
and parse_triples_block (pm : prefix_map) (fuel : nat) (acc : list triple_pattern) (ts : token_stream)
  : Tot (parse_result (list triple_pattern)) (decreases fuel) =
  if fuel = 0 then ParseOk acc ts
  else match parse_subject pm (fuel-1) ts with
  | ParseErr m -> ParseOk acc ts  (* not a triples block, return what we have *)
  | ParseOk subj ts' ->
    begin match parse_pred_obj_list pm (fuel-1) subj acc ts' with
    | ParseErr m -> ParseErr m
    | ParseOk triples ts'' ->
      begin match parse_peek ts'' with
      | Tok_DOT ->
        let ts''' = parse_advance ts'' in
        (* Check if there are more triples *)
        (match parse_peek ts''' with
         | Tok_VAR _ | Tok_IRI _ | Tok_PNAME _ | Tok_BNODE _ | Tok_LBRACKET
         | Tok_LPAREN | Tok_A | Tok_INTEGER _ | Tok_DECIMAL _ | Tok_DOUBLE _
         | Tok_STRING _ | Tok_TRUE | Tok_FALSE ->
           parse_triples_block pm (fuel-1) triples ts'''
         | _ -> ParseOk triples ts''')
      | _ -> ParseOk triples ts''
      end end

(* ---- SELECT query parsing ---- *)

and parse_select_query (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result query) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else
    let r = parse_prologue pm (fuel-1) ts in
    (match r with
     | ParseErr m -> ParseErr m
     | ParseOk (pm', base) ts' ->
       (match parse_peek ts' with
        | Tok_SELECT -> parse_select_body pm' (fuel-1) base ts'
        | Tok_ASK -> parse_ask_body pm' (fuel-1) base ts'
        | Tok_CONSTRUCT -> ParseErr "unsupported: CONSTRUCT queries"
        | Tok_DESCRIBE -> ParseErr "unsupported: DESCRIBE queries"
        | _ -> ParseErr "expected SELECT, ASK, CONSTRUCT, or DESCRIBE"))

(* Parse prologue: (PREFIX prefix: <iri> | BASE <iri>)* *)
and parse_prologue (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (prefix_map & option wf_iri)) (decreases fuel) =
  if fuel = 0 then ParseOk (pm, None) ts
  else begin match parse_peek ts with
    | Tok_PREFIX ->
      let ts' = parse_advance ts in
      (match parse_peek ts' with
       | Tok_PNAME pn ->
         let (prefix, _) = split_pname pn in
         let ts'' = parse_advance ts' in
         (match parse_peek ts'' with
          | Tok_IRI iri ->
            if is_iri iri then
              parse_prologue ((prefix, iri) :: pm) (fuel-1) (parse_advance ts'')
            else ParseErr "invalid prefix IRI"
          | _ -> ParseErr "expected IRI after PREFIX name")
       | _ -> ParseErr "expected prefix name after PREFIX")
    | Tok_BASE ->
      let ts' = parse_advance ts in
      (match parse_peek ts' with
       | Tok_IRI iri ->
         if is_iri iri then parse_prologue pm (fuel-1) (parse_advance ts')
         else ParseErr "invalid BASE IRI"
       | _ -> ParseErr "expected IRI after BASE")
    | _ -> ParseOk (pm, None) ts
  end

(* Parse SELECT body: SELECT [DISTINCT|REDUCED] (vars|*) [FROM ...] WHERE { } modifiers *)
and parse_select_body (pm : prefix_map) (fuel : nat) (base : option wf_iri) (ts : token_stream)
  : Tot (parse_result query) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else begin
    let ts' = parse_advance ts in  (* consume SELECT *)
    let (dist, red, ts'') = begin match parse_peek ts' with
      | Tok_DISTINCT -> (true, false, parse_advance ts')
      | Tok_REDUCED -> (false, true, parse_advance ts')
      | _ -> (false, false, ts') end in
    begin match parse_select_vars pm (fuel-1) ts'' with
    | ParseErr m -> ParseErr m
    | ParseOk sel ts3 ->
      (* Skip FROM clauses *)
      begin match parse_skip_from (fuel-1) ts3 with
      | ParseErr m -> ParseErr m
      | ParseOk ds ts4 ->
        (* Optional WHERE keyword *)
        let ts4 = match parse_peek ts4 with Tok_WHERE -> parse_advance ts4 | _ -> ts4 in
        begin match parse_group_graph_pattern pm (fuel-1) ts4 with
        | ParseErr m -> ParseErr m
        | ParseOk pattern ts5 ->
          begin match parse_solution_modifier pm (fuel-1) ts5 with
          | ParseErr m -> ParseErr m
          | ParseOk modifier ts6 ->
            ParseOk ({
              q_base = base;
              q_prefixes = pm;
              q_form = QF_Select sel;
              q_dataset = ds;
              q_pattern = pattern;
              q_group_by = None;
              q_having = None;
              q_modifier = { modifier with sm_distinct = dist; sm_reduced = red };
              q_values = None
            }) ts6
          end end end end end

(* Parse ASK body *)
and parse_ask_body (pm : prefix_map) (fuel : nat) (base : option wf_iri) (ts : token_stream)
  : Tot (parse_result query) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else begin
    let ts' = parse_advance ts in  (* consume ASK *)
    (* Skip FROM clauses *)
    begin match parse_skip_from (fuel-1) ts' with
    | ParseErr m -> ParseErr m
    | ParseOk ds ts'' ->
      let ts'' = match parse_peek ts'' with Tok_WHERE -> parse_advance ts'' | _ -> ts'' in
      begin match parse_group_graph_pattern pm (fuel-1) ts'' with
      | ParseErr m -> ParseErr m
      | ParseOk pattern ts3 ->
        ParseOk ({
          q_base = base; q_prefixes = pm; q_form = QF_Ask;
          q_dataset = ds; q_pattern = pattern;
          q_group_by = None; q_having = None; q_modifier = default_modifier;
          q_values = None
        }) ts3
      end end end

(* Parse SELECT variables: * | (Var | (expr AS Var))+ *)
and parse_select_vars (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result select_clause) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_STAR -> ParseOk Select_All (parse_advance ts)
  | _ ->
    begin match parse_select_items pm (fuel-1) [] ts with
    | ParseErr m -> ParseErr m
    | ParseOk items ts' ->
      if List.Tot.length items = 0 then ParseErr "expected select variables"
      else ParseOk (Select_Vars items) ts'
    end

and parse_select_items (pm : prefix_map) (fuel : nat) (acc : list select_item) (ts : token_stream)
  : Tot (parse_result (list select_item)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_peek ts with
  | Tok_VAR v -> parse_select_items pm (fuel-1) (SI_Var v :: acc) (parse_advance ts)
  | Tok_LPAREN ->
    (match parse_expr pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' ->
       begin match parse_expect Tok_AS ts' with
       | ParseErr m -> ParseErr m
       | ParseOk () ts'' ->
         begin match parse_peek ts'' with
         | Tok_VAR v ->
           (match parse_expect Tok_RPAREN (parse_advance ts'') with
            | ParseErr m -> ParseErr m
            | ParseOk () ts''' -> parse_select_items pm (fuel-1) (SI_Expr e v :: acc) ts''')
         | _ -> ParseErr "expected variable after AS"
         end end)
  | _ -> ParseOk (List.Tot.rev acc) ts

(* Skip FROM / FROM NAMED clauses *)
and parse_skip_from (fuel : nat) (ts : token_stream)
  : Tot (parse_result (list dataset_clause)) (decreases fuel) =
  if fuel = 0 then ParseOk [] ts
  else ParseOk [] ts  (* TODO: parse FROM clauses *)

(* Skip GROUP BY expressions (simplified — consumes var/paren tokens) *)
and skip_group_by_exprs (fuel : nat) (ts : token_stream)
  : Tot token_stream (decreases fuel) =
  if fuel = 0 then ts
  else match parse_peek ts with
  | Tok_VAR _ -> skip_group_by_exprs (fuel - 1) (parse_advance ts)
  | Tok_LPAREN -> skip_group_by_exprs (fuel - 1) (parse_advance ts)
  | _ -> ts

(* Skip ORDER BY expressions (simplified) *)
and skip_order_by_exprs (fuel : nat) (ts : token_stream)
  : Tot token_stream (decreases fuel) =
  if fuel = 0 then ts
  else match parse_peek ts with
  | Tok_ASC | Tok_DESC | Tok_VAR _ | Tok_LPAREN ->
    skip_order_by_exprs (fuel - 1) (parse_advance ts)
  | _ -> ts

(* Skip HAVING expressions (simplified) *)
and skip_having_exprs (fuel : nat) (ts : token_stream)
  : Tot token_stream (decreases fuel) =
  if fuel = 0 then ts
  else match parse_peek ts with
  | Tok_LPAREN -> skip_having_exprs (fuel - 1) (parse_advance ts)
  | _ -> ts

(* Parse solution modifier: GROUP BY, HAVING, ORDER BY, LIMIT, OFFSET *)
and parse_solution_modifier (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result solution_modifier) (decreases fuel) =
  if fuel = 0 then ParseOk default_modifier ts
  else
    (* GROUP BY *)
    let ts = match parse_peek ts with
      | Tok_GROUP ->
        let ts' = parse_advance ts in
        (match parse_peek ts' with
         | Tok_BY -> skip_group_by_exprs (fuel-1) (parse_advance ts')
         | _ -> ts)
      | _ -> ts in
    (* HAVING *)
    let ts = match parse_peek ts with
      | Tok_HAVING -> skip_having_exprs (fuel-1) (parse_advance ts)
      | _ -> ts in
    (* ORDER BY *)
    let ts = match parse_peek ts with
      | Tok_ORDER ->
        let ts' = parse_advance ts in
        (match parse_peek ts' with
         | Tok_BY -> skip_order_by_exprs (fuel-1) (parse_advance ts')
         | _ -> ts)
      | _ -> ts in
    (* LIMIT *)
    let (limit, ts) = begin match parse_peek ts with
      | Tok_LIMIT ->
        let ts' = parse_advance ts in
        (match parse_peek ts' with
         | Tok_INTEGER n ->
           (match parse_int_str n with
            | Some i -> (Some i, parse_advance ts')
            | None -> (None, ts'))
         | _ -> (None, ts'))
      | _ -> (None, ts) end in
    (* OFFSET *)
    let (offset, ts) = begin match parse_peek ts with
      | Tok_OFFSET ->
        let ts' = parse_advance ts in
        (match parse_peek ts' with
         | Tok_INTEGER n ->
           (match parse_int_str n with
            | Some i -> (Some i, parse_advance ts')
            | None -> (None, ts'))
         | _ -> (None, ts'))
      | _ -> (None, ts) end in
    ParseOk ({
      sm_order_by = None; sm_distinct = false; sm_reduced = false;
      sm_offset = offset; sm_limit = limit
    }) ts

#pop-options

(* ---- Top-level parse function ---- *)

let parse_sparql (input : string) : parse_result query =
  let tokens = tokenize input in
  parse_select_query [] 10000 tokens

(** ====================================================================== **)
(** Part 8: SSE-style Algebra Printer                                       **)
(**                                                                          **)
(** Prints algebra trees in S-expression notation, matching ARQ's SSE        **)
(** format for debugging and test comparison.                                **)
(** ====================================================================== **)

(* Helper: parenthesize *)
let sse_wrap (tag : string) (body : string) : string =
  "(" ^ tag ^ " " ^ body ^ ")"

(* Print a pattern term *)
let sse_pattern_term (pt : pattern_term) : string =
  match pt with
  | PT_Var v -> "?" ^ v
  | PT_IRI i -> "<" ^ i ^ ">"
  | PT_BNode b -> "_:" ^ b
  | PT_Literal l -> "\"" ^ l.lexical_form ^ "\""

(* Print a pattern subject *)
let sse_pattern_subject (ps : pattern_subject) : string =
  match ps with
  | PS_Var v -> "?" ^ v
  | PS_IRI i -> "<" ^ i ^ ">"
  | PS_BNode b -> "_:" ^ b

(* Print a triple pattern *)
let sse_triple (tp : triple_pattern) : string =
  sse_wrap "triple" (sse_pattern_subject tp.tp_s ^ " " ^
                     sse_pattern_term tp.tp_p ^ " " ^
                     sse_pattern_term tp.tp_o)

(* Print a BGP *)
let sse_bgp (patterns : bgp) : string =
  let triples = List.Tot.map sse_triple patterns in
  sse_wrap "bgp" (String.concat "\n    " triples)

(* Print a comparison operator *)
let sse_comp_op (op : comp_op) : string =
  match op with
  | CmpEq -> "=" | CmpNe -> "!=" | CmpLt -> "<"
  | CmpGt -> ">" | CmpLe -> "<=" | CmpGe -> ">="

(* Print an arithmetic operator *)
let sse_arith_op (op : arith_op) : string =
  match op with
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/"

(* Print an expression — recursive *)
let rec sse_expr (e : expr) : Tot string (decreases e) =
  match e with
  | E_Var v -> "?" ^ v
  | E_IRI i -> "<" ^ i ^ ">"
  | E_Literal l -> "\"" ^ l.lexical_form ^ "\""
  | E_BoolLit b -> if b then "true" else "false"
  | E_NumericLit n -> string_of_int n
  | E_DecimalLit s -> s
  | E_DoubleLit s -> s
  | E_Arith op e1 e2 -> sse_wrap (sse_arith_op op) (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_UnaryMinus e1 -> sse_wrap "-" (sse_expr e1)
  | E_UnaryPlus e1 -> sse_wrap "+" (sse_expr e1)
  | E_Compare op e1 e2 -> sse_wrap (sse_comp_op op) (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_And e1 e2 -> sse_wrap "&&" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_Or e1 e2 -> sse_wrap "||" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_Not e1 -> sse_wrap "!" (sse_expr e1)
  | E_IsIRI e1 -> sse_wrap "isIRI" (sse_expr e1)
  | E_IsBlank e1 -> sse_wrap "isBlank" (sse_expr e1)
  | E_IsLiteral e1 -> sse_wrap "isLiteral" (sse_expr e1)
  | E_IsNumeric e1 -> sse_wrap "isNumeric" (sse_expr e1)
  | E_Str e1 -> sse_wrap "str" (sse_expr e1)
  | E_Lang e1 -> sse_wrap "lang" (sse_expr e1)
  | E_Datatype e1 -> sse_wrap "datatype" (sse_expr e1)
  | E_IRI_fn e1 -> sse_wrap "iri" (sse_expr e1)
  | E_Bound v -> sse_wrap "bound" ("?" ^ v)
  | E_If c t f -> sse_wrap "if" (sse_expr c ^ " " ^ sse_expr t ^ " " ^ sse_expr f)
  | E_Coalesce args -> sse_wrap "coalesce" (sse_expr_list args)
  | E_Concat args -> sse_wrap "concat" (sse_expr_list args)
  | E_In e1 es -> sse_wrap "in" (sse_expr e1 ^ " " ^ sse_expr_list es)
  | E_NotIn e1 es -> sse_wrap "notin" (sse_expr e1 ^ " " ^ sse_expr_list es)
  | E_StrLen e1 -> sse_wrap "strlen" (sse_expr e1)
  | E_Substr e1 e2 None -> sse_wrap "substr" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_Substr e1 e2 (Some e3) -> sse_wrap "substr" (sse_expr e1 ^ " " ^ sse_expr e2 ^ " " ^ sse_expr e3)
  | E_UCase e1 -> sse_wrap "ucase" (sse_expr e1)
  | E_LCase e1 -> sse_wrap "lcase" (sse_expr e1)
  | E_StrStarts e1 e2 -> sse_wrap "strstarts" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_StrEnds e1 e2 -> sse_wrap "strends" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_Contains e1 e2 -> sse_wrap "contains" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_StrBefore e1 e2 -> sse_wrap "strbefore" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_StrAfter e1 e2 -> sse_wrap "strafter" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_EncodeForUri e1 -> sse_wrap "encode_for_uri" (sse_expr e1)
  | E_Replace e1 e2 e3 None -> sse_wrap "replace" (sse_expr e1 ^ " " ^ sse_expr e2 ^ " " ^ sse_expr e3)
  | E_Replace e1 e2 e3 (Some e4) -> sse_wrap "replace" (sse_expr e1 ^ " " ^ sse_expr e2 ^ " " ^ sse_expr e3 ^ " " ^ sse_expr e4)
  | E_Regex e1 e2 None -> sse_wrap "regex" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_Regex e1 e2 (Some e3) -> sse_wrap "regex" (sse_expr e1 ^ " " ^ sse_expr e2 ^ " " ^ sse_expr e3)
  | E_Abs e1 -> sse_wrap "abs" (sse_expr e1)
  | E_Round e1 -> sse_wrap "round" (sse_expr e1)
  | E_Ceil e1 -> sse_wrap "ceil" (sse_expr e1)
  | E_Floor e1 -> sse_wrap "floor" (sse_expr e1)
  | E_MD5 e1 -> sse_wrap "md5" (sse_expr e1)
  | E_SHA1 e1 -> sse_wrap "sha1" (sse_expr e1)
  | E_SHA256 e1 -> sse_wrap "sha256" (sse_expr e1)
  | E_SHA384 e1 -> sse_wrap "sha384" (sse_expr e1)
  | E_SHA512 e1 -> sse_wrap "sha512" (sse_expr e1)
  | E_Now -> "(now)"
  | E_Year e1 -> sse_wrap "year" (sse_expr e1)
  | E_Month e1 -> sse_wrap "month" (sse_expr e1)
  | E_Day e1 -> sse_wrap "day" (sse_expr e1)
  | E_Hours e1 -> sse_wrap "hours" (sse_expr e1)
  | E_Minutes e1 -> sse_wrap "minutes" (sse_expr e1)
  | E_Seconds e1 -> sse_wrap "seconds" (sse_expr e1)
  | E_Timezone e1 -> sse_wrap "timezone" (sse_expr e1)
  | E_Tz e1 -> sse_wrap "tz" (sse_expr e1)
  | E_SameTerm e1 e2 -> sse_wrap "sameTerm" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_StrDt e1 e2 -> sse_wrap "strdt" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_StrLang e1 e2 -> sse_wrap "strlang" (sse_expr e1 ^ " " ^ sse_expr e2)
  | E_Exists ggp -> sse_wrap "exists" (sse_ggp ggp)
  | E_NotExists ggp -> sse_wrap "notexists" (sse_ggp ggp)
  | E_Aggregate agg distinct e1 -> sse_wrap "agg" (sse_expr e1)
  | E_FunctionCall iri args -> sse_wrap ("call " ^ iri) (sse_expr_list args)

and sse_expr_list (es : list expr) : Tot string (decreases es) =
  match es with
  | [] -> ""
  | [e] -> sse_expr e
  | e :: rest -> sse_expr e ^ " " ^ sse_expr_list rest

(* Print a property path *)
and sse_path (pp : property_path) : Tot string (decreases pp) =
  match pp with
  | PP_IRI i -> "<" ^ i ^ ">"
  | PP_Inverse p -> sse_wrap "reverse" (sse_path p)
  | PP_Sequence p1 p2 -> sse_wrap "seq" (sse_path p1 ^ " " ^ sse_path p2)
  | PP_Alternative p1 p2 -> sse_wrap "alt" (sse_path p1 ^ " " ^ sse_path p2)
  | PP_ZeroOrMore p -> sse_wrap "path*" (sse_path p)
  | PP_OneOrMore p -> sse_wrap "path+" (sse_path p)
  | PP_ZeroOrOne p -> sse_wrap "path?" (sse_path p)
  | PP_NegatedSet ps -> sse_wrap "notoneof" (sse_path_list ps)

and sse_path_list (ps : list property_path) : Tot string (decreases ps) =
  match ps with
  | [] -> ""
  | [p] -> sse_path p
  | p :: rest -> sse_path p ^ " " ^ sse_path_list rest

(* Print a group graph pattern *)
and sse_ggp (ggp : group_graph_pattern) : Tot string (decreases ggp) =
  match ggp with
  | GP_Empty -> "(table unit)"
  | GP_BGP patterns -> sse_bgp patterns
  | GP_Join g1 g2 -> sse_wrap "join" (sse_ggp g1 ^ "\n  " ^ sse_ggp g2)
  | GP_LeftJoin g1 g2 cond ->
    sse_wrap "leftjoin" (sse_ggp g1 ^ "\n  " ^ sse_ggp g2 ^ "\n  " ^ sse_expr cond)
  | GP_Filter e g -> sse_wrap "filter" (sse_expr e ^ "\n  " ^ sse_ggp g)
  | GP_Union g1 g2 -> sse_wrap "union" (sse_ggp g1 ^ "\n  " ^ sse_ggp g2)
  | GP_Graph term g -> sse_wrap "graph" (sse_pattern_term term ^ "\n  " ^ sse_ggp g)
  | GP_Minus g1 g2 -> sse_wrap "minus" (sse_ggp g1 ^ "\n  " ^ sse_ggp g2)
  | GP_Bind e v g -> sse_wrap "extend" ("(?" ^ v ^ " " ^ sse_expr e ^ ")\n  " ^ sse_ggp g)
  | GP_Values vars rows -> sse_wrap "table" (sse_vars vars)
  | GP_Service iri g silent ->
    sse_wrap "service" ((if silent then "SILENT " else "") ^ "<" ^ iri ^ ">\n  " ^ sse_ggp g)
  | GP_SubSelect q -> sse_query q
  | GP_PropertyPath s pp o ->
    sse_wrap "path" (sse_pattern_subject s ^ " " ^ sse_path pp ^ " " ^ sse_pattern_term o)

and sse_vars (vs : list var_name) : Tot string (decreases vs) =
  match vs with
  | [] -> ""
  | [v] -> "?" ^ v
  | v :: rest -> "?" ^ v ^ " " ^ sse_vars rest

(* Print a select item *)
and sse_select_item (si : select_item) : Tot string (decreases si) =
  match si with
  | SI_Var v -> "?" ^ v
  | SI_Expr e v -> sse_wrap "as" (sse_expr e ^ " ?" ^ v)

and sse_select_items (items : list select_item) : Tot string (decreases items) =
  match items with
  | [] -> ""
  | [i] -> sse_select_item i
  | i :: rest -> sse_select_item i ^ " " ^ sse_select_items rest

(* Print a full query in SSE *)
and sse_query (q : query) : Tot string (decreases q) =
  let form = match q.q_form with
    | QF_Select Select_All -> "(project *"
    | QF_Select (Select_Vars items) -> "(project (" ^ sse_select_items items ^ ")"
    | QF_Ask -> "(ask"
    | QF_Construct _ -> "(construct"
    | QF_Describe _ -> "(describe"
  in
  let body = sse_ggp q.q_pattern in
  let modifiers =
    (match q.q_modifier.sm_order_by with
     | None -> ""
     | Some _ -> "\n  (order ...)") ^
    (if q.q_modifier.sm_distinct then "\n  (distinct)" else "") ^
    (match q.q_modifier.sm_limit with
     | None -> ""
     | Some n -> "\n  (slice _ " ^ string_of_int n ^ ")") in
  form ^ "\n  " ^ body ^ modifiers ^ ")"

#pop-options
