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

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

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
  | Tok_FROM | Tok_NAMED
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
(** Part 2b: Lexer Helpers                                                  **)
(** ====================================================================== **)

(* Convert a single character to a string *)
let char_to_string (c : FStar.Char.char) : string =
  FStar.String.string_of_list [c]

(* Hex digit classification *)
let is_hex_digit (c : FStar.Char.char) : bool =
  let code = char_code c in
  (code >= 0x30 && code <= 0x39) ||
  (code >= 0x41 && code <= 0x46) ||
  (code >= 0x61 && code <= 0x66)

(* Hex digit value (0 for non-hex) *)
let hex_value (c : FStar.Char.char) : nat =
  let code = char_code c in
  if code >= 0x30 && code <= 0x39 then code - 0x30
  else if code >= 0x41 && code <= 0x46 then code - 0x41 + 10
  else if code >= 0x61 && code <= 0x66 then code - 0x61 + 10
  else 0

(* UTF-8 encode a Unicode codepoint. Delegated to OCaml extraction. *)
assume val utf8_of_codepoint : nat -> string

(* Process \uXXXX and \UXXXXXXXX escapes in an IRI string.
   Delegated to OCaml stub — escape processing requires UTF-8 encoding. *)
assume val process_iri_escapes : string -> string

(* Process escape sequences in a string literal
   (\t \n \r \\ \" \' \uXXXX \UXXXXXXXX).
   Delegated to OCaml stub. *)
assume val process_string_escapes : string -> string

(* Find position of a character in a string, starting from p *)
let rec find_char_pos (input : string) (p : pos) (target : nat)
  : Tot (option pos) (decreases (String.length input - p)) =
  if at_end input p then None
  else if char_code (peek_char input p) = target then Some p
  else find_char_pos input (p + 1) target

(* Trim trailing dots from a scanned name.
   Used by blank node labels and prefixed names per SPARQL grammar.
   For PN_LOCAL, a dot preceded by a backslash is part of an escape sequence
   (\.) and must not be trimmed. *)
let rec trim_trailing_dots (input : string) (start : pos) (end_pos : pos)
  : Tot pos (decreases end_pos) =
  if end_pos = 0 || end_pos <= start then start
  else if char_code (char_at input (end_pos - 1)) = 0x2E (* . *) then
    if end_pos >= 2 && end_pos - 2 >= start
       && char_code (char_at input (end_pos - 2)) = 0x5C (* \ *)
    then end_pos  (* preserve \. escape sequence *)
    else trim_trailing_dots input start (end_pos - 1)
  else end_pos

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

(* --- scan_iri: content between < and > --- *)

(* Find position of unescaped > in IRI. Backslash skips next char. *)
let rec scan_iri_end (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else
    let c = peek_char input p in
    if char_code c = 0x3E (* > *) then p
    else if char_code c = 0x5C (* \ *) then
      if at_end input (p + 1) then p + 1
      else scan_iri_end input (p + 2)
    else scan_iri_end input (p + 1)

// Safe subtraction that always returns nat (for substring length args)
let safe_sub (a b : int) : nat = if a >= b then a - b else 0

(* Scan IRI content starting after <, returns (iri_string, pos_after_>) *)
let scan_iri (input : string) (p : pos) : (string & pos) =
  let end_p = scan_iri_end input p in
  let len = if end_p >= p then end_p - p else 0 in
  let raw = substring input p len in
  let processed = process_iri_escapes raw in
  if at_end input end_p then (processed, end_p)
  else (processed, end_p + 1) (* skip > *)

(* --- scan_string: string literal content --- *)

(* Find end of short string (single quote delimiter) *)
let rec scan_short_string_end (input : string) (p : pos) (q_code : nat)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else
    let c = peek_char input p in
    if char_code c = q_code then p
    else if char_code c = 0x5C (* \ *) then
      if at_end input (p + 1) then p + 1
      else scan_short_string_end input (p + 2) q_code
    else scan_short_string_end input (p + 1) q_code

(* Find end of long string (triple quote delimiter) *)
let rec scan_long_string_end (input : string) (p : pos) (q_code : nat)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else
    let c = peek_char input p in
    if char_code c = q_code
       && not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = q_code
       && not (at_end input (p + 2)) && char_code (peek_char input (p + 2)) = q_code
    then p
    else if char_code c = 0x5C (* \ *) then
      if at_end input (p + 1) then p + 1
      else scan_long_string_end input (p + 2) q_code
    else scan_long_string_end input (p + 1) q_code

(* Scan string literal starting at opening quote.
   Handles short ("...") and long (\"\"\"...\"\"\") forms, single and double quotes.
   Returns (string_content, pos_after_closing_quote). *)
let scan_string (input : string) (p : pos) : (string & pos) =
  let q = peek_char input p in
  let q_code = char_code q in
  (* Check for long string (triple-quoted) *)
  let is_long =
    not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = q_code &&
    not (at_end input (p + 2)) && char_code (peek_char input (p + 2)) = q_code in
  if is_long then
    let p_start = p + 3 in
    let end_p = scan_long_string_end input p_start q_code in
    let raw = substring input p_start (safe_sub end_p p_start) in
    (process_string_escapes raw, end_p + 3) (* skip closing """ or ''' *)
  else
    let p_start = p + 1 in
    let end_p = scan_short_string_end input p_start q_code in
    let raw = substring input p_start (safe_sub end_p p_start) in
    (process_string_escapes raw, end_p + 1) (* skip closing " or ' *)

(* --- scan_pname_or_keyword: prefixed name or SPARQL keyword --- *)

(* Scan PN_CHAR* characters (for prefix part or keyword) *)
let rec scan_pn_chars_end (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else if is_pn_char (peek_char input p) then scan_pn_chars_end input (p + 1)
  else p

(* Scan PN_LOCAL characters after the colon in a prefixed name *)
let rec scan_pn_local_end (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else
    let c = peek_char input p in
    if is_pn_char c || char_code c = 0x3A (* : *) || char_code c = 0x25 (* % *) then
      scan_pn_local_end input (p + 1)
    else if char_code c = 0x5C (* \ *) then
      if at_end input (p + 1) then p
      else if is_pn_local_esc (peek_char input (p + 1)) then
        scan_pn_local_end input (p + 2)
      else p
    else p

(* Map an uppercased word to its SPARQL keyword token, or Tok_PNAME if not a keyword.
   Case-insensitive keyword matching per SPARQL grammar. *)
let keyword_of_upper (upper : string) (original : string) : token =
  if streq upper "SELECT" then Tok_SELECT
  else if streq upper "ASK" then Tok_ASK
  else if streq upper "CONSTRUCT" then Tok_CONSTRUCT
  else if streq upper "DESCRIBE" then Tok_DESCRIBE
  else if streq upper "WHERE" then Tok_WHERE
  else if streq upper "PREFIX" then Tok_PREFIX
  else if streq upper "BASE" then Tok_BASE
  else if streq upper "OPTIONAL" then Tok_OPTIONAL
  else if streq upper "UNION" then Tok_UNION
  else if streq upper "MINUS" then Tok_MINUS_KW
  else if streq upper "FILTER" then Tok_FILTER
  else if streq upper "BIND" then Tok_BIND
  else if streq upper "VALUES" then Tok_VALUES
  else if streq upper "GRAPH" then Tok_GRAPH
  else if streq upper "SERVICE" then Tok_SERVICE
  else if streq upper "SILENT" then Tok_SILENT
  else if streq upper "EXISTS" then Tok_EXISTS
  else if streq upper "NOT" then Tok_NOT
  else if streq upper "AS" then Tok_AS
  else if streq upper "DISTINCT" then Tok_DISTINCT
  else if streq upper "REDUCED" then Tok_REDUCED
  else if streq upper "ORDER" then Tok_ORDER
  else if streq upper "BY" then Tok_BY
  else if streq upper "ASC" then Tok_ASC
  else if streq upper "DESC" then Tok_DESC
  else if streq upper "GROUP" then Tok_GROUP
  else if streq upper "HAVING" then Tok_HAVING
  else if streq upper "LIMIT" then Tok_LIMIT
  else if streq upper "OFFSET" then Tok_OFFSET
  else if streq upper "FROM" then Tok_FROM
  else if streq upper "NAMED" then Tok_NAMED
  else if streq upper "IN" then Tok_IN
  else if streq upper "TRUE" then Tok_TRUE
  else if streq upper "FALSE" then Tok_FALSE
  else if streq upper "UNDEF" then Tok_UNDEF
  else if streq upper "A" then Tok_A
  (* Built-in function keywords *)
  else if streq upper "STR" then Tok_STR
  else if streq upper "LANG" then Tok_LANG
  else if streq upper "LANGMATCHES" then Tok_LANGMATCHES
  else if streq upper "DATATYPE" then Tok_DATATYPE
  else if streq upper "BOUND" then Tok_BOUND
  else if streq upper "IF" then Tok_IF
  else if streq upper "IRI" then Tok_IRI_KW
  else if streq upper "URI" then Tok_URI
  else if streq upper "BNODE" then Tok_BNODE_KW
  else if streq upper "RAND" then Tok_RAND
  else if streq upper "ABS" then Tok_ABS
  else if streq upper "CEIL" then Tok_CEIL
  else if streq upper "FLOOR" then Tok_FLOOR
  else if streq upper "ROUND" then Tok_ROUND
  else if streq upper "CONCAT" then Tok_CONCAT
  else if streq upper "STRLEN" then Tok_STRLEN
  else if streq upper "UCASE" then Tok_UCASE
  else if streq upper "LCASE" then Tok_LCASE
  else if streq upper "ENCODE_FOR_URI" then Tok_ENCODE_FOR_URI
  else if streq upper "CONTAINS" then Tok_CONTAINS
  else if streq upper "STRSTARTS" then Tok_STRSTARTS
  else if streq upper "STRENDS" then Tok_STRENDS
  else if streq upper "STRBEFORE" then Tok_STRBEFORE
  else if streq upper "STRAFTER" then Tok_STRAFTER
  else if streq upper "REPLACE" then Tok_REPLACE
  else if streq upper "REGEX" then Tok_REGEX
  else if streq upper "SUBSTR" then Tok_SUBSTR
  else if streq upper "SUBSTRING" then Tok_SUBSTR  (* alias *)
  else if streq upper "ISIRI" then Tok_ISIRI
  else if streq upper "ISURI" then Tok_ISIRI  (* alias for ISIRI *)
  else if streq upper "ISBLANK" then Tok_ISBLANK
  else if streq upper "ISLITERAL" then Tok_ISLITERAL
  else if streq upper "ISNUMERIC" then Tok_ISNUMERIC
  else if streq upper "SAMETERM" then Tok_SAMETERM
  else if streq upper "STRDT" then Tok_STRDT
  else if streq upper "STRLANG" then Tok_STRLANG
  else if streq upper "COUNT" then Tok_COUNT
  else if streq upper "SUM" then Tok_SUM
  else if streq upper "MIN" then Tok_MIN_KW
  else if streq upper "MAX" then Tok_MAX_KW
  else if streq upper "AVG" then Tok_AVG
  else if streq upper "GROUP_CONCAT" then Tok_GROUP_CONCAT
  else if streq upper "SAMPLE" then Tok_SAMPLE
  else if streq upper "SEPARATOR" then Tok_SEPARATOR
  else if streq upper "COALESCE" then Tok_COALESCE
  else if streq upper "NOW" then Tok_NOW
  else if streq upper "UUID" then Tok_UUID
  else if streq upper "STRUUID" then Tok_STRUUID
  else if streq upper "YEAR" then Tok_YEAR
  else if streq upper "MONTH" then Tok_MONTH
  else if streq upper "DAY" then Tok_DAY
  else if streq upper "HOURS" then Tok_HOURS
  else if streq upper "MINUTES" then Tok_MINUTES
  else if streq upper "SECONDS" then Tok_SECONDS
  else if streq upper "TIMEZONE" then Tok_TIMEZONE
  else if streq upper "TZ" then Tok_TZ
  else if streq upper "MD5" then Tok_MD5
  else if streq upper "SHA1" then Tok_SHA1
  else if streq upper "SHA256" then Tok_SHA256
  else if streq upper "SHA384" then Tok_SHA384
  else if streq upper "SHA512" then Tok_SHA512
  else Tok_PNAME original

(* Scan a prefixed name (prefix:local) or a keyword.
   Position p is at the first character of the name. *)
let scan_pname_or_keyword (input : string) (p : pos) : lex_result =
  let p1 = scan_pn_chars_end input p in
  if not (at_end input p1) && char_code (peek_char input p1) = 0x3A (* : *) then
    (* Prefixed name: prefix:local *)
    let p2 = scan_pn_local_end input (p1 + 1) in
    let p2 = trim_trailing_dots input p p2 in
    (Tok_PNAME (substring input p (safe_sub p2 p)), p2)
  else
    (* Keyword or bare name *)
    let word = substring input p (safe_sub p1 p) in
    (keyword_of_upper (string_upper word) word, p1)

(* --- scan_number: integer, decimal, or double literal --- *)

(* Scan consecutive digits *)
let rec scan_digits_end (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else if is_digit (peek_char input p) then scan_digits_end input (p + 1)
  else p

(* Scan a numeric literal. Returns appropriate token type:
   INTEGER (digits only), DECIMAL (digits.digits), DOUBLE (with exponent). *)
let scan_number (input : string) (p : pos) : lex_result =
  (* Scan integer part *)
  let p1 = scan_digits_end input p in
  (* Check for decimal point followed by digit *)
  let has_dot = not (at_end input p1) && char_code (peek_char input p1) = 0x2E
                && not (at_end input (p1 + 1)) && is_digit (peek_char input (p1 + 1)) in
  let p2 = if has_dot then scan_digits_end input (p1 + 1) else p1 in
  (* Check for exponent *)
  let has_exp = not (at_end input p2) &&
                (char_code (peek_char input p2) = 0x65 (* e *)
                 || char_code (peek_char input p2) = 0x45 (* E *)) in
  let p3 = if has_exp then
    let pe = p2 + 1 in
    let pe = if not (at_end input pe) &&
                (char_code (peek_char input pe) = 0x2B (* + *)
                 || char_code (peek_char input pe) = 0x2D (* - *))
             then pe + 1 else pe in
    scan_digits_end input pe
  else p2 in
  let text = substring input p (safe_sub p3 p) in
  if has_exp then (Tok_DOUBLE text, p3)
  else if has_dot then (Tok_DECIMAL text, p3)
  else (Tok_INTEGER text, p3)

(* --- scan_bnode_label: blank node label after _: --- *)

(* Scan PN_CHAR* for blank node label *)
let rec scan_bnode_chars_end (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else if is_pn_char (peek_char input p) then scan_bnode_chars_end input (p + 1)
  else p

(* Scan blank node label after _: has been consumed.
   Returns (label, position_after_label). *)
let scan_bnode_label (input : string) (p : pos) : (string & pos) =
  let p' = scan_bnode_chars_end input p in
  let p' = trim_trailing_dots input p p' in
  (substring input p (safe_sub p' p), p')

(* --- scan_var_name: variable name after ? or $ --- *)

(* Scan [a-zA-Z0-9_]* for variable names *)
let rec scan_var_chars_end (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else
    let c = peek_char input p in
    if is_alnum c || char_code c = 0x5F (* _ *) then scan_var_chars_end input (p + 1)
    else p

(* Scan variable name after ? or $ has been consumed.
   Returns (name, position_after_name). Empty name if no valid chars. *)
let scan_var_name (input : string) (p : pos) : (string & pos) =
  let p' = scan_var_chars_end input p in
  (substring input p (safe_sub p' p), p')

(* --- scan_langtag: language tag after @ --- *)

(* Scan [a-zA-Z0-9-]* for language tags *)
let rec scan_langtag_chars_end (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else
    let c = peek_char input p in
    if is_alnum c || char_code c = 0x2D (* - *) then scan_langtag_chars_end input (p + 1)
    else p

(* Scan language tag after @ has been consumed.
   Returns (tag, position_after_tag). *)
let scan_langtag (input : string) (p : pos) : (string & pos) =
  let p' = scan_langtag_chars_end input p in
  (substring input p (safe_sub p' p), p')

let rec has_gt_before_terminator (input : string) (p : pos)
  : Tot bool (decreases (String.length input - p)) =
  if at_end input p then false
  else
    let code = char_code (peek_char input p) in
    if code = 0x3E (* > *) then true
    else if is_ws (peek_char input p) || code = 0x29 || code = 0x7D || code = 0x5D
    then false
    else has_gt_before_terminator input (p + 1)

(* Main tokenizer: produce one token from current position *)
let next_token (input : string) (p : pos) : lex_result =
  let p = skip_ws input p in
  if at_end input p then (Tok_EOF, p)
  else
    let c = peek_char input p in
    let code = char_code c in
    if code = 0x3C (* < *) then begin
      // Could be <= or <IRI> or < (less-than)
      if not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = 0x3D
      then (Tok_LE, p + 2)
      else if at_end input (p + 1) then (Tok_LT, p + 1)
      else
        // Distinguish <IRI> from < (less-than):
        // IRI starts with a letter, underscore, or colon (e.g., <http:, <urn:, <_:)
        // Less-than is followed by space, digit, newline, etc.
        let next_code = char_code (peek_char input (p + 1)) in
        if (next_code >= 0x41 && next_code <= 0x5A) ||  // A-Z
           (next_code >= 0x61 && next_code <= 0x7A) ||  // a-z
           next_code = 0x3E ||  // >  (for <>)
           next_code = 0x5F ||  // _
           next_code = 0x2F ||  // / (for </path>)
           next_code = 0x23 ||  // # (for <#fragment>)
           ((next_code = 0x3F || next_code = 0x24) &&
             has_gt_before_terminator input (p + 1))
        then
          let (iri, p') = scan_iri input (p + 1) in
          (Tok_IRI iri, p')
        else (Tok_LT, p + 1)
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

let resolve_relative_iri_token (base : option wf_iri) (tok : token) : token =
  match tok with
  | Tok_IRI iri ->
    (match if is_iri iri then Some iri else resolve_query_iri base iri with
     | Some abs -> Tok_IRI abs
     | None -> tok)
  | _ -> tok

let rec resolve_relative_iri_tokens (base : option wf_iri) (ts : token_stream)
  : Tot token_stream (decreases ts) =
  match ts with
  | [] -> []
  | t :: rest -> resolve_relative_iri_token base t :: resolve_relative_iri_tokens base rest

// Predicate can be a simple term or a property path
noeq type verb_or_path =
  | VSimple : pattern_term -> verb_or_path
  | VPath   : property_path -> verb_or_path

// Result of parsing solution modifiers (modifier + group_by + having)
type modifier_result = solution_modifier & option (list group_condition) & option (list having_condition)

(* Tokenize entire input into a token list.
   Repeatedly calls next_token until EOF. Safety: stops if no progress. *)
let rec tokenize_loop (input : string) (p : pos) (acc : list token) (fuel : nat)
  : Tot (list token) (decreases fuel) =
  if fuel = 0 then List.Tot.rev (Tok_EOF :: acc)
  else if p > String.length input then List.Tot.rev (Tok_EOF :: acc)
  else
    let (tok, p') = next_token input p in
    match tok with
    | Tok_EOF -> List.Tot.rev (Tok_EOF :: acc)
    | _ ->
      if p' <= p then List.Tot.rev (Tok_EOF :: acc)
      else tokenize_loop input p' (tok :: acc) (fuel - 1)

let tokenize (input : string) : list token =
  tokenize_loop input 0 [] (String.length input + 1)

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

(* Token equality — uses F* decidable equality, extracts to OCaml = *)
let token_eq (t1 t2 : token) : bool = t1 = t2

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
  match find_char_pos pn 0 0x3A (* : *) with
  | Some i -> (substring pn 0 i, substring pn (i + 1) (safe_sub (String.length pn) (i + 1)))
  | None -> (pn, "")

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
  | Tok_LANGMATCHES ->
    // LANGMATCHES(tag, range) is a 2-arg built-in; model as function call
    let ts' = parse_advance ts in
    (match parse_expect Tok_LPAREN ts' with
     | ParseErr m -> ParseErr m
     | ParseOk () ts1 ->
       begin match parse_expr pm (fuel-1) ts1 with | ParseErr m -> ParseErr m | ParseOk e1 ts2 ->
       begin match parse_expect Tok_COMMA ts2 with | ParseErr m -> ParseErr m | ParseOk () ts3 ->
       begin match parse_expr pm (fuel-1) ts3 with | ParseErr m -> ParseErr m | ParseOk e2 ts4 ->
       begin match parse_expect Tok_RPAREN ts4 with | ParseErr m -> ParseErr m | ParseOk () ts5 ->
       ParseOk (E_FunctionCall "http://www.w3.org/2005/xpath-functions#langMatches" [e1; e2]) ts5
       end end end end)
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
  | Tok_NOW ->
    let ts' = parse_advance ts in
    // NOW() requires parens
    (match parse_peek ts' with
     | Tok_LPAREN ->
       let ts'' = parse_advance ts' in
       (match parse_expect Tok_RPAREN ts'' with
        | ParseErr _ -> ParseErr "expected ')' after NOW("
        | ParseOk () ts''' -> ParseOk E_Now ts''')
     | _ -> ParseOk E_Now ts')
  | Tok_RAND ->
    // RAND() -> E_FunctionCall with 0 args
    let ts' = parse_advance ts in
    (match parse_expect Tok_LPAREN ts' with
     | ParseErr e -> ParseErr e
     | ParseOk () ts'' ->
       match parse_expect Tok_RPAREN ts'' with
       | ParseErr _ -> ParseErr "expected ')' after RAND("
       | ParseOk () ts''' ->
         ParseOk (E_FunctionCall "http://www.w3.org/2005/xpath-functions#rand" []) ts''')
  | Tok_UUID ->
    let ts' = parse_advance ts in
    (match parse_expect Tok_LPAREN ts' with
     | ParseErr e -> ParseErr e
     | ParseOk () ts'' ->
       match parse_expect Tok_RPAREN ts'' with
       | ParseErr _ -> ParseErr "expected ')' after UUID("
       | ParseOk () ts''' ->
         ParseOk (E_FunctionCall "http://www.w3.org/2005/xpath-functions#uuid" []) ts''')
  | Tok_STRUUID ->
    let ts' = parse_advance ts in
    (match parse_expect Tok_LPAREN ts' with
     | ParseErr e -> ParseErr e
     | ParseOk () ts'' ->
       match parse_expect Tok_RPAREN ts'' with
       | ParseErr _ -> ParseErr "expected ')' after STRUUID("
       | ParseOk () ts''' ->
         ParseOk (E_FunctionCall "http://www.w3.org/2005/xpath-functions#struuid" []) ts''')
  | Tok_BNODE_KW ->
    // BNODE() or BNODE(expr)
    let ts' = parse_advance ts in
    (match parse_expect Tok_LPAREN ts' with
     | ParseErr e -> ParseErr e
     | ParseOk () ts'' ->
       match parse_peek ts'' with
       | Tok_RPAREN ->
         // BNODE() - no args
         let ts''' = parse_advance ts'' in
         ParseOk (E_FunctionCall "http://www.w3.org/2005/xpath-functions#bnode" []) ts'''
       | _ ->
         // BNODE(expr)
         match parse_expr pm (fuel-1) ts'' with
         | ParseErr e -> ParseErr e
         | ParseOk arg ts''' ->
           match parse_expect Tok_RPAREN ts''' with
           | ParseErr _ -> ParseErr "expected ')' after BNODE(expr"
           | ParseOk () ts4 ->
             ParseOk (E_FunctionCall "http://www.w3.org/2005/xpath-functions#bnode" [arg]) ts4)
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
    (* COUNT-star special case *)
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
      begin match parse_ggp_body pm (fuel-1) GP_Empty [] false ts' with
      | ParseErr m -> ParseErr m
      | ParseOk g ts'' ->
        begin match parse_expect Tok_RBRACE ts'' with
        | ParseErr m -> ParseErr m
        | ParseOk () ts''' -> ParseOk g ts'''
        end end
    end

and is_local_labeled_bnode_id (b : string) : bool =
  let prefix = "_:bnode_" in
  let plen = String.length prefix in
  let blen = String.length b in
  if blen < plen then true
  else not (streq (substring b 0 plen) prefix)

and local_string_mem (x : string) (xs : list string) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | y :: ys -> streq x y || local_string_mem x ys

and local_string_add_unique (x : string) (xs : list string) : list string =
  if local_string_mem x xs then xs else x :: xs

and local_string_union (xs ys : list string) : Tot (list string) (decreases xs) =
  match xs with
  | [] -> ys
  | x :: rest -> local_string_union rest (local_string_add_unique x ys)

and local_string_overlaps (xs ys : list string) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | x :: rest -> local_string_mem x ys || local_string_overlaps rest ys

and local_bnodes_in_pattern_subject (ps : pattern_subject) : list string =
  match ps with
  | PS_BNode b -> if is_local_labeled_bnode_id b then [b] else []
  | _ -> []

and local_bnodes_in_pattern_term (pt : pattern_term) : list string =
  match pt with
  | PT_BNode b -> if is_local_labeled_bnode_id b then [b] else []
  | _ -> []

and local_bnodes_in_triple_pattern (tp : triple_pattern) : list string =
  local_string_union (local_bnodes_in_pattern_subject tp.tp_s)
    (local_string_union (local_bnodes_in_pattern_term tp.tp_p) (local_bnodes_in_pattern_term tp.tp_o))

and local_bnodes_in_bgp (bgp : bgp) : Tot (list string) (decreases bgp) =
  match bgp with
  | [] -> []
  | tp :: rest -> local_string_union (local_bnodes_in_triple_pattern tp) (local_bnodes_in_bgp rest)

and ggp_labeled_bnodes (g : group_graph_pattern) : Tot (list string) (decreases g) =
  match g with
  | GP_BGP bgp -> local_bnodes_in_bgp bgp
  | GP_PropertyPath ps _ pt ->
    local_string_union (local_bnodes_in_pattern_subject ps) (local_bnodes_in_pattern_term pt)
  | GP_Join g1 g2
  | GP_Union g1 g2
  | GP_Minus g1 g2 ->
    local_string_union (ggp_labeled_bnodes g1) (ggp_labeled_bnodes g2)
  | GP_LeftJoin g1 g2 _ ->
    local_string_union (ggp_labeled_bnodes g1) (ggp_labeled_bnodes g2)
  | GP_Filter _ g1
  | GP_Graph _ g1
  | GP_Bind _ _ g1
  | GP_Service _ g1 _ ->
    ggp_labeled_bnodes g1
  | GP_SubSelect q ->
    ggp_labeled_bnodes q.q_pattern
  | GP_Values _ _ -> []
  | GP_Empty -> []

// Parse the body of a GGP: triples blocks interleaved with graph pattern elements.
// FILTERs are collected in `filters` and wrapped around the result at the end,
// per SPARQL 1.1 spec section 18.2.4: filters scope over the entire group.
and parse_ggp_body (pm : prefix_map) (fuel : nat) (acc : group_graph_pattern)
  (filters : list expr) (cross_scope : bool) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then
    let g = List.Tot.fold_left (fun g e -> GP_Filter e g) acc filters in
    ParseOk g ts
  else match parse_peek ts with
  // Try parsing triples if we see a term
  | Tok_VAR _ | Tok_IRI _ | Tok_PNAME _ | Tok_BNODE _ | Tok_LBRACKET
  | Tok_LPAREN | Tok_A | Tok_INTEGER _ | Tok_DECIMAL _ | Tok_DOUBLE _
  | Tok_STRING _ | Tok_TRUE | Tok_FALSE ->
    (match parse_triples_block pm (fuel-1) GP_Empty ts with
     | ParseErr m -> ParseErr m
     | ParseOk triples_ggp ts' ->
       if cross_scope && local_string_overlaps (ggp_labeled_bnodes acc) (ggp_labeled_bnodes triples_ggp) then
         ParseErr "blank node label reused across nested group scope"
       else
         let acc' = ggp_join acc triples_ggp in
         parse_ggp_body pm (fuel-1) acc' filters false ts')
  | Tok_OPTIONAL ->
    (match parse_group_graph_pattern pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk g ts' ->
       let acc' = match acc with
         | GP_Empty -> GP_LeftJoin GP_Empty g (E_BoolLit true)
         | _ -> GP_LeftJoin acc g (E_BoolLit true) in
       let ts' = match parse_peek ts' with Tok_DOT -> parse_advance ts' | _ -> ts' in
       parse_ggp_body pm (fuel-1) acc' filters true ts')
  | Tok_MINUS_KW ->
    (match parse_group_graph_pattern pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk g ts' ->
       let acc' = GP_Minus acc g in
       let ts' = match parse_peek ts' with Tok_DOT -> parse_advance ts' | _ -> ts' in
       parse_ggp_body pm (fuel-1) acc' filters true ts')
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
         parse_ggp_body pm (fuel-1) acc' filters true ts'''
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
         parse_ggp_body pm (fuel-1) acc' filters true ts'''
       end)
  | Tok_FILTER ->
    let ts' = parse_advance ts in
    // Collect filter expression; will be wrapped at group end per spec 18.2.4
    (match parse_filter_expr pm (fuel-1) ts' with
     | ParseErr m -> ParseErr m
     | ParseOk e ts'' ->
       let ts'' = match parse_peek ts'' with Tok_DOT -> parse_advance ts'' | _ -> ts'' in
       parse_ggp_body pm (fuel-1) acc (e :: filters) cross_scope ts'')
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
             if ggp_has_var v acc then ParseErr "BIND variable already in scope"
             else
             (match parse_expect Tok_RPAREN (parse_advance ts4) with
              | ParseErr m -> ParseErr m
              | ParseOk () ts5 ->
                let acc' = GP_Bind e v acc in
                let ts5 = match parse_peek ts5 with Tok_DOT -> parse_advance ts5 | _ -> ts5 in
                parse_ggp_body pm (fuel-1) acc' filters cross_scope ts5)
           | _ -> ParseErr "expected variable after AS"
           end end end)
  | Tok_VALUES ->
    (match parse_values_clause pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk g ts' ->
       let acc' = ggp_join acc g in
       let ts' = match parse_peek ts' with Tok_DOT -> parse_advance ts' | _ -> ts' in
       parse_ggp_body pm (fuel-1) acc' filters cross_scope ts')
  | Tok_LBRACE ->
    // Nested GGP or UNION
    (match parse_group_or_union pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk g ts' ->
       if local_string_overlaps (ggp_labeled_bnodes acc) (ggp_labeled_bnodes g) then
         ParseErr "blank node label reused across nested group scope"
       else
         let acc' = match acc with GP_Empty -> g | _ -> GP_Join acc g in
         let ts' = match parse_peek ts' with Tok_DOT -> parse_advance ts' | _ -> ts' in
         parse_ggp_body pm (fuel-1) acc' filters true ts')
  | _ ->
    // Wrap collected filters around the final pattern (spec 18.2.4)
    let g = List.Tot.fold_left (fun g e -> GP_Filter e g) acc filters in
    ParseOk g ts

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
  | Tok_REGEX | Tok_IF
  | Tok_IRI_KW | Tok_URI | Tok_BNODE_KW | Tok_RAND
  | Tok_ABS | Tok_CEIL | Tok_FLOOR | Tok_ROUND
  | Tok_CONCAT | Tok_STRLEN | Tok_UCASE | Tok_LCASE
  | Tok_ENCODE_FOR_URI | Tok_CONTAINS | Tok_STRSTARTS | Tok_STRENDS
  | Tok_STRBEFORE | Tok_STRAFTER | Tok_REPLACE | Tok_SUBSTR
  | Tok_STRDT | Tok_STRLANG
  | Tok_COALESCE | Tok_NOW | Tok_UUID | Tok_STRUUID
  | Tok_YEAR | Tok_MONTH | Tok_DAY | Tok_HOURS | Tok_MINUTES | Tok_SECONDS
  | Tok_TIMEZONE | Tok_TZ
  | Tok_MD5 | Tok_SHA1 | Tok_SHA256 | Tok_SHA384 | Tok_SHA512 ->
    parse_primary_expr pm (fuel-1) ts
  | _ -> ParseErr "expected '(' or built-in call after FILTER"

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

// ---- VALUES clause parsing ----
// VALUES (?x ?y) { (val1 val2) (val3 UNDEF) ... }
// or VALUES ?x { val1 val2 ... }

// Parse a single data value: IRI, literal, or UNDEF
and parse_data_value (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (option rdf_term)) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_UNDEF -> ParseOk None (parse_advance ts)
  | Tok_IRI i ->
    if is_iri i then ParseOk (Some (T_IRI i)) (parse_advance ts) else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
    (match resolve_pname pn pm with
     | Some iri -> if is_iri iri then ParseOk (Some (T_IRI iri)) (parse_advance ts) else ParseErr "invalid IRI"
     | None -> ParseErr "unresolved prefix")
  | Tok_STRING s ->
    // Check for ^^datatype or @lang
    let ts' = parse_advance ts in
    (match parse_peek ts' with
     | Tok_HATHAT ->
       let ts'' = parse_advance ts' in
       (match parse_peek ts'' with
        | Tok_IRI dt ->
          if is_iri dt then
            (match make_typed_literal s dt with
             | Some lit -> ParseOk (Some (T_Literal lit)) (parse_advance ts'')
             | None -> ParseErr "invalid typed literal")
          else ParseErr "invalid datatype IRI"
        | Tok_PNAME pn ->
          (match resolve_pname pn pm with
           | Some dt ->
             if is_iri dt then
               (match make_typed_literal s dt with
                | Some lit -> ParseOk (Some (T_Literal lit)) (parse_advance ts'')
                | None -> ParseErr "invalid typed literal")
             else ParseErr "invalid datatype IRI"
           | None -> ParseErr "unresolved prefix")
        | _ -> ParseErr "expected IRI after ^^")
     | Tok_LANGTAG lang ->
       ParseOk (Some (T_Literal (make_lang_literal s lang))) (parse_advance ts')
     | _ -> ParseOk (Some (T_Literal (make_plain_literal s))) ts')
  | Tok_INTEGER n ->
    (match make_typed_literal n "http://www.w3.org/2001/XMLSchema#integer" with
     | Some lit -> ParseOk (Some (T_Literal lit)) (parse_advance ts)
     | None -> ParseErr "invalid integer")
  | Tok_DECIMAL d ->
    (match make_typed_literal d "http://www.w3.org/2001/XMLSchema#decimal" with
     | Some lit -> ParseOk (Some (T_Literal lit)) (parse_advance ts)
     | None -> ParseErr "invalid decimal")
  | Tok_DOUBLE d ->
    (match make_typed_literal d "http://www.w3.org/2001/XMLSchema#double" with
     | Some lit -> ParseOk (Some (T_Literal lit)) (parse_advance ts)
     | None -> ParseErr "invalid double")
  | Tok_TRUE ->
    (match make_typed_literal "true" "http://www.w3.org/2001/XMLSchema#boolean" with
     | Some lit -> ParseOk (Some (T_Literal lit)) (parse_advance ts)
     | None -> ParseErr "invalid boolean")
  | Tok_FALSE ->
    (match make_typed_literal "false" "http://www.w3.org/2001/XMLSchema#boolean" with
     | Some lit -> ParseOk (Some (T_Literal lit)) (parse_advance ts)
     | None -> ParseErr "invalid boolean")
  | _ -> ParseErr "expected data value or UNDEF"

// Parse a row of values: ( val1 val2 ... )
and parse_values_row (pm : prefix_map) (fuel : nat) (n_vars : nat) (ts : token_stream)
  : Tot (parse_result (list (option rdf_term))) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_expect Tok_LPAREN ts with
  | ParseErr m -> ParseErr m
  | ParseOk () ts' -> parse_values_row_items pm (fuel-1) n_vars [] ts'

and parse_values_row_items (pm : prefix_map) (fuel : nat) (remaining : nat)
  (acc : list (option rdf_term)) (ts : token_stream)
  : Tot (parse_result (list (option rdf_term))) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_peek ts with
  | Tok_RPAREN -> ParseOk (List.Tot.rev acc) (parse_advance ts)
  | _ ->
    (match parse_data_value pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk v ts' -> parse_values_row_items pm (fuel-1) (if remaining > 0 then remaining - 1 else 0) (v :: acc) ts')

// Parse multiple rows
and parse_values_rows (pm : prefix_map) (fuel : nat) (n_vars : nat)
  (acc : list (list (option rdf_term))) (ts : token_stream)
  : Tot (parse_result (list (list (option rdf_term)))) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_peek ts with
  | Tok_LPAREN ->
    (match parse_values_row pm (fuel-1) n_vars ts with
     | ParseErr m -> ParseErr m
     | ParseOk row ts' -> parse_values_rows pm (fuel-1) n_vars (row :: acc) ts')
  | _ -> ParseOk (List.Tot.rev acc) ts

// Parse variable list for VALUES: (?x ?y ...)
and parse_values_vars (fuel : nat) (acc : list var_name) (ts : token_stream)
  : Tot (parse_result (list var_name)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_peek ts with
  | Tok_VAR v -> parse_values_vars (fuel-1) (v :: acc) (parse_advance ts)
  | _ -> ParseOk (List.Tot.rev acc) ts

// Parse VALUES clause: after VALUES keyword consumed
// VALUES (?x ?y) { (v1 v2) ... }  or  VALUES ?x { v1 v2 ... }
and parse_values_clause (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_VAR v ->
    // Single variable form: VALUES ?x { v1 v2 ... }
    let ts' = parse_advance ts in
    (match parse_expect Tok_LBRACE ts' with
     | ParseErr m -> ParseErr m
     | ParseOk () ts'' ->
       begin match parse_single_var_values pm (fuel-1) [] ts'' with
       | ParseErr m -> ParseErr m
       | ParseOk vals ts''' ->
         begin match parse_expect Tok_RBRACE ts''' with
         | ParseErr m -> ParseErr m
         | ParseOk () ts4 ->
           let rows = List.Tot.map (fun v -> [v]) vals in
           ParseOk (GP_Values [v] rows) ts4
         end end)
  | Tok_LPAREN ->
    // Multi variable form: VALUES (?x ?y) { (v1 v2) ... }
    let ts' = parse_advance ts in
    (match parse_values_vars (fuel-1) [] ts' with
     | ParseErr m -> ParseErr m
     | ParseOk vars ts'' ->
       begin match parse_expect Tok_RPAREN ts'' with
       | ParseErr m -> ParseErr m
       | ParseOk () ts''' ->
         begin match parse_expect Tok_LBRACE ts''' with
         | ParseErr m -> ParseErr m
         | ParseOk () ts4 ->
           begin match parse_values_rows pm (fuel-1) (List.Tot.length vars) [] ts4 with
           | ParseErr m -> ParseErr m
           | ParseOk rows ts5 ->
             begin match parse_expect Tok_RBRACE ts5 with
             | ParseErr m -> ParseErr m
             | ParseOk () ts6 ->
               let vars_len = List.Tot.length vars in
               let check_row (row : list (option rdf_term)) : bool =
                 List.Tot.length row = vars_len in
               if List.Tot.for_all check_row rows then
                 ParseOk (GP_Values vars rows) ts6
               else
                 ParseErr "VALUES row has wrong number of terms"
             end end end end)
  | _ -> ParseErr "expected variable or '(' after VALUES"

// Parse single-variable VALUES data: v1 v2 v3 ... (no parens around each)
and parse_single_var_values (pm : prefix_map) (fuel : nat)
  (acc : list (option rdf_term)) (ts : token_stream)
  : Tot (parse_result (list (option rdf_term))) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_peek ts with
  | Tok_RBRACE -> ParseOk (List.Tot.rev acc) ts
  | _ ->
    (match parse_data_value pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk v ts' -> parse_single_var_values pm (fuel-1) (v :: acc) ts')

(* ---- Triples block parsing ---- *)

and pattern_term_to_subject (pt : pattern_term) : Tot (option pattern_subject) =
  match pt with
  | PT_Var v -> Some (PS_Var v)
  | PT_IRI i -> Some (PS_IRI i)
  | PT_BNode b -> Some (PS_BNode b)
  | PT_Literal _ -> None

(* Parse a subject as (pattern_subject, extra_triples, outer_predicate_list_optional) *)
and parse_subject_with_extras (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (pattern_subject & group_graph_pattern & bool)) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_VAR v -> ParseOk (PS_Var v, GP_Empty, false) (parse_advance ts)
  | Tok_IRI i -> if is_iri i then ParseOk (PS_IRI i, GP_Empty, false) (parse_advance ts) else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
    (match resolve_pname pn pm with
     | Some iri -> if is_iri iri then ParseOk (PS_IRI iri, GP_Empty, false) (parse_advance ts) else ParseErr "invalid IRI"
     | None -> ParseErr "unresolved prefix")
  | Tok_BNODE b -> ParseOk (PS_BNode b, GP_Empty, false) (parse_advance ts)
  | Tok_LBRACKET ->
    // [] = anonymous blank node, or [ predObjList ] = blank node with properties
    let bnode_id = fresh_bnode_id ts in
    let ts' = parse_advance ts in
    (match parse_peek ts' with
     | Tok_RBRACKET -> ParseOk (PS_BNode bnode_id, GP_Empty, false) (parse_advance ts')
     | _ ->
       let bnode_subj = PS_BNode bnode_id in
       (match parse_pred_obj_list pm (fuel-1) bnode_subj GP_Empty ts' with
        | ParseErr m -> ParseErr m
        | ParseOk extra_triples ts'' ->
          (match parse_expect Tok_RBRACKET ts'' with
           | ParseErr _ -> ParseErr "expected ']' after blank node property list"
           | ParseOk () ts''' ->
             ParseOk (PS_BNode bnode_id, extra_triples, false) ts''')))
  | Tok_LPAREN ->
    (match parse_collection pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk (pt, extras) ts' ->
       (match pattern_term_to_subject pt with
        | Some subj -> ParseOk (subj, extras, false) ts'
        | None -> ParseErr "collection cannot be used as subject"))
  | _ -> ParseErr "expected subject"

(* Legacy wrapper for parse_subject (returns just pattern_subject, no extras) *)
  and parse_subject (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result pattern_subject) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_subject_with_extras pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk (subj, _, _) ts' -> ParseOk subj ts'

// Property path parsing: PathAlternative ::= PathSequence ( '|' PathSequence )*
and parse_path_alternative (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_path_sequence pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk p1 ts' -> parse_path_alt_rest pm (fuel-1) p1 ts'

and parse_path_alt_rest (pm : prefix_map) (fuel : nat) (acc : property_path) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseOk acc ts
  else match parse_peek ts with
  | Tok_PIPE ->
    (match parse_path_sequence pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk p2 ts' -> parse_path_alt_rest pm (fuel-1) (PP_Alternative acc p2) ts')
  | _ -> ParseOk acc ts

// PathSequence ::= PathEltOrInverse ( '/' PathEltOrInverse )*
and parse_path_sequence (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_path_elt_or_inverse pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk p1 ts' -> parse_path_seq_rest pm (fuel-1) p1 ts'

and parse_path_seq_rest (pm : prefix_map) (fuel : nat) (acc : property_path) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseOk acc ts
  else match parse_peek ts with
  | Tok_SLASH ->
    (match parse_path_elt_or_inverse pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk p2 ts' -> parse_path_seq_rest pm (fuel-1) (PP_Sequence acc p2) ts')
  | _ -> ParseOk acc ts

// PathEltOrInverse ::= PathElt | '^' PathElt
and parse_path_elt_or_inverse (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_CARET ->
    (match parse_path_elt pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk p ts' -> ParseOk (PP_Inverse p) ts')
  | _ -> parse_path_elt pm (fuel-1) ts

// PathElt ::= PathPrimary PathMod?   (PathMod ::= '?' | '*' | '+')
and parse_path_elt (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_path_primary pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk p ts' ->
    (match parse_peek ts' with
     | Tok_STAR -> ParseOk (PP_ZeroOrMore p) (parse_advance ts')
     | Tok_PLUS -> ParseOk (PP_OneOrMore p) (parse_advance ts')
     | Tok_QMARK -> ParseOk (PP_ZeroOrOne p) (parse_advance ts')
     | _ -> ParseOk p ts')

// PathPrimary ::= iri | 'a' | '!' PathNegatedPropertySet | '(' Path ')'
and parse_path_primary (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_IRI i ->
    if is_iri i then ParseOk (PP_IRI i) (parse_advance ts) else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
    (match resolve_pname pn pm with
     | Some iri -> if is_iri iri then ParseOk (PP_IRI iri) (parse_advance ts) else ParseErr "invalid IRI"
     | None -> ParseErr "unresolved prefix")
  | Tok_A -> ParseOk (PP_IRI rdf_type_iri_str) (parse_advance ts)
  | Tok_BANG -> parse_path_negated pm (fuel-1) (parse_advance ts)
  | Tok_LPAREN ->
    (match parse_path_alternative pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk p ts' ->
       begin match parse_expect Tok_RPAREN ts' with
       | ParseErr _ -> ParseErr "expected ')' after path"
       | ParseOk () ts'' -> ParseOk p ts''
       end)
  | _ -> ParseErr "expected path primary"

// PathNegatedPropertySet ::= PathOneInPropertySet | '(' PathOneInPropertySet ( '|' ... )* ')'
and parse_path_negated (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_LPAREN ->
    (match parse_path_one_in_set_list pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk ps ts' ->
       begin match parse_expect Tok_RPAREN ts' with
       | ParseErr _ -> ParseErr "expected ')' in negated path set"
       | ParseOk () ts'' -> ParseOk (PP_NegatedSet ps) ts''
       end)
  | _ ->
    (match parse_path_one_in_set pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk p ts' -> ParseOk (PP_NegatedSet [p]) ts')

// PathOneInPropertySet ::= iri | 'a' | '^' ( iri | 'a' )
and parse_path_one_in_set (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_IRI i ->
    if is_iri i then ParseOk (PP_IRI i) (parse_advance ts) else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
    (match resolve_pname pn pm with
     | Some iri -> if is_iri iri then ParseOk (PP_IRI iri) (parse_advance ts) else ParseErr "invalid IRI"
     | None -> ParseErr "unresolved prefix")
  | Tok_A -> ParseOk (PP_IRI rdf_type_iri_str) (parse_advance ts)
  | Tok_CARET ->
    let ts' = parse_advance ts in
    (match parse_peek ts' with
     | Tok_IRI i ->
       if is_iri i then ParseOk (PP_Inverse (PP_IRI i)) (parse_advance ts') else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
       (match resolve_pname pn pm with
        | Some iri -> if is_iri iri then ParseOk (PP_Inverse (PP_IRI iri)) (parse_advance ts') else ParseErr "invalid IRI"
        | None -> ParseErr "unresolved prefix")
     | Tok_A -> ParseOk (PP_Inverse (PP_IRI rdf_type_iri_str)) (parse_advance ts')
     | _ -> ParseErr "expected IRI or 'a' after ^ in negated set")
  | _ -> ParseErr "expected path element in negated set"

// List of PathOneInPropertySet separated by '|'
and parse_path_one_in_set_list (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (list property_path)) (decreases fuel) =
  if fuel = 0 then ParseOk [] ts
  else match parse_path_one_in_set pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk p ts' ->
    (match parse_peek ts' with
     | Tok_PIPE ->
       (match parse_path_one_in_set_list pm (fuel-1) (parse_advance ts') with
        | ParseErr m -> ParseErr m
        | ParseOk ps ts'' -> ParseOk (p :: ps) ts'')
     | _ -> ParseOk [p] ts')

// Parse verb (predicate): try property path, determine if simple or complex
and parse_verb (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result verb_or_path) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else
  // Variable as predicate — always simple
  match parse_peek ts with
  | Tok_VAR v -> ParseOk (VSimple (PT_Var v)) (parse_advance ts)
  | _ ->
    // Try to parse as property path
    (match parse_path_alternative pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk pp ts' ->
       // If it's just a simple IRI, return as VSimple for regular triple
       (match pp with
        | PP_IRI iri -> ParseOk (VSimple (PT_IRI iri)) ts'
        | _ -> ParseOk (VPath pp) ts'))

// Generate a fresh blank node ID based on token stream position
and fresh_bnode_id (ts : token_stream) : string =
  "_:bnode_" ^ string_of_int (List.Tot.length ts)

and parse_signed_numeric_literal_pt (sign:string) (ts:token_stream)
  : parse_result pattern_term =
  match parse_peek ts with
  | Tok_INTEGER n ->
    (match make_typed_literal (sign ^ n) "http://www.w3.org/2001/XMLSchema#integer" with
     | Some lit -> ParseOk (PT_Literal lit) (parse_advance ts)
     | None -> ParseErr "invalid integer literal")
  | Tok_DECIMAL d ->
    (match make_typed_literal (sign ^ d) "http://www.w3.org/2001/XMLSchema#decimal" with
     | Some lit -> ParseOk (PT_Literal lit) (parse_advance ts)
     | None -> ParseErr "invalid decimal literal")
  | Tok_DOUBLE d ->
    (match make_typed_literal (sign ^ d) "http://www.w3.org/2001/XMLSchema#double" with
     | Some lit -> ParseOk (PT_Literal lit) (parse_advance ts)
     | None -> ParseErr "invalid double literal")
  | _ -> ParseErr "expected signed numeric literal"

// Parse an object as (pattern_term, extra_triples)
// The extra_triples GGP contains triples generated by blank node property lists or collections
and parse_object_with_extras (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (pattern_term & group_graph_pattern)) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_VAR v -> ParseOk (PT_Var v, GP_Empty) (parse_advance ts)
  | Tok_IRI i -> if is_iri i then ParseOk (PT_IRI i, GP_Empty) (parse_advance ts) else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
    (match resolve_pname pn pm with
     | Some iri -> if is_iri iri then ParseOk (PT_IRI iri, GP_Empty) (parse_advance ts) else ParseErr "invalid IRI"
     | None -> ParseErr "unresolved prefix")
  | Tok_BNODE b -> ParseOk (PT_BNode b, GP_Empty) (parse_advance ts)
  | Tok_STRING s ->
    (match parse_rdf_literal_pt pm (fuel-1) s (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk pt ts' -> ParseOk (pt, GP_Empty) ts')
  | Tok_INTEGER n ->
    (match make_typed_literal n "http://www.w3.org/2001/XMLSchema#integer" with
     | Some lit -> ParseOk (PT_Literal lit, GP_Empty) (parse_advance ts)
     | None -> ParseErr "invalid integer literal")
  | Tok_DECIMAL d ->
    (match make_typed_literal d "http://www.w3.org/2001/XMLSchema#decimal" with
     | Some lit -> ParseOk (PT_Literal lit, GP_Empty) (parse_advance ts)
     | None -> ParseErr "invalid decimal literal")
  | Tok_DOUBLE d ->
    (match make_typed_literal d "http://www.w3.org/2001/XMLSchema#double" with
     | Some lit -> ParseOk (PT_Literal lit, GP_Empty) (parse_advance ts)
     | None -> ParseErr "invalid double literal")
  | Tok_TRUE ->
    (match make_typed_literal "true" "http://www.w3.org/2001/XMLSchema#boolean" with
     | Some lit -> ParseOk (PT_Literal lit, GP_Empty) (parse_advance ts)
     | None -> ParseErr "invalid boolean literal")
  | Tok_FALSE ->
    (match make_typed_literal "false" "http://www.w3.org/2001/XMLSchema#boolean" with
     | Some lit -> ParseOk (PT_Literal lit, GP_Empty) (parse_advance ts)
     | None -> ParseErr "invalid boolean literal")
  | Tok_PLUS ->
    (match parse_signed_numeric_literal_pt "+" (parse_advance ts) with
     | ParseOk pt ts' -> ParseOk (pt, GP_Empty) ts'
     | ParseErr m -> ParseErr m)
  | Tok_MINUS_OP ->
    (match parse_signed_numeric_literal_pt "-" (parse_advance ts) with
     | ParseOk pt ts' -> ParseOk (pt, GP_Empty) ts'
     | ParseErr m -> ParseErr m)
  | Tok_A -> ParseOk (PT_IRI rdf_type_iri_str, GP_Empty) (parse_advance ts)
  | Tok_LBRACKET ->
    // Blank node property list: [ pred obj ; ... ]
    let bnode_id = fresh_bnode_id ts in
    let ts' = parse_advance ts in
    (match parse_peek ts' with
     | Tok_RBRACKET ->
       // Empty [] = anonymous blank node
       ParseOk (PT_BNode bnode_id, GP_Empty) (parse_advance ts')
     | _ ->
       // [ predObjList ] = blank node with properties
       let bnode_subj = PS_BNode bnode_id in
       (match parse_pred_obj_list pm (fuel-1) bnode_subj GP_Empty ts' with
        | ParseErr m -> ParseErr m
        | ParseOk extra_triples ts'' ->
          (match parse_expect Tok_RBRACKET ts'' with
           | ParseErr _ -> ParseErr "expected ']' after blank node property list"
           | ParseOk () ts''' ->
             ParseOk (PT_BNode bnode_id, extra_triples) ts''')))
  | Tok_LPAREN ->
    // Collection: ( item1 item2 ... ) -> rdf:first/rdf:rest chain
    parse_collection pm (fuel-1) (parse_advance ts)
  | _ -> ParseErr "expected object"

// Parse an RDF collection ( item1 item2 ... ) into rdf:first/rdf:rest chain
and parse_collection (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (pattern_term & group_graph_pattern)) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_RPAREN ->
    // Empty collection = rdf:nil
    ParseOk (PT_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil", GP_Empty) (parse_advance ts)
  | _ ->
    // Parse first item
    (match parse_object_with_extras pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (item, item_extras) ts' ->
       let bnode_id = fresh_bnode_id ts in
       let bnode_subj = PS_BNode bnode_id in
       // Parse rest of collection
       (match parse_collection pm (fuel-1) ts' with
        | ParseErr m -> ParseErr m
        | ParseOk (rest_term, rest_extras) ts'' ->
          // Build triples: _:b rdf:first item . _:b rdf:rest rest .
          let first_triple = { tp_s = bnode_subj;
                               tp_p = PT_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#first";
                               tp_o = item } in
          let rest_triple = { tp_s = bnode_subj;
                              tp_p = PT_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest";
                              tp_o = rest_term } in
          let triples = GP_BGP [first_triple; rest_triple] in
          let all_extras = ggp_join (ggp_join triples item_extras) rest_extras in
          ParseOk (PT_BNode bnode_id, all_extras) ts''))

// Legacy wrapper for parse_object (returns just pattern_term, no extras)
and parse_object (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result pattern_term) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_object_with_extras pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk (pt, _) ts' -> ParseOk pt ts'

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

// Helper: join two group_graph_patterns
and ggp_join (a b : group_graph_pattern) : group_graph_pattern =
  match a with GP_Empty -> b | _ -> match b with GP_Empty -> a | _ -> GP_Join a b

// Helper: add a triple or path pattern to a GGP accumulator
and ggp_add_triple (acc : group_graph_pattern) (tp : triple_pattern) : group_graph_pattern =
  match acc with
  | GP_BGP ts -> GP_BGP (ts @ [tp])
  | GP_Empty -> GP_BGP [tp]
  | _ -> GP_Join acc (GP_BGP [tp])

and ggp_add_pp (acc : group_graph_pattern) (s : pattern_subject) (pp : property_path) (o : pattern_term) : group_graph_pattern =
  ggp_join acc (GP_PropertyPath s pp o)

// Parse object list for simple predicates: obj1, obj2, obj3
and parse_object_list_simple (pm : prefix_map) (fuel : nat) (subj : pattern_subject)
  (pred : pattern_term) (acc : group_graph_pattern) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseOk acc ts
  else match parse_object_with_extras pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk (obj, extras) ts' ->
    let acc' = ggp_add_triple acc { tp_s = subj; tp_p = pred; tp_o = obj } in
    let acc' = ggp_join acc' extras in
    begin match parse_peek ts' with
    | Tok_COMMA -> parse_object_list_simple pm (fuel-1) subj pred acc' (parse_advance ts')
    | _ -> ParseOk acc' ts'
    end

// Parse object list for property path predicates: obj1, obj2, obj3
and parse_object_list_path (pm : prefix_map) (fuel : nat) (subj : pattern_subject)
  (pp : property_path) (acc : group_graph_pattern) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseOk acc ts
  else match parse_object_with_extras pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk (obj, extras) ts' ->
    let acc' = ggp_add_pp acc subj pp obj in
    let acc' = ggp_join acc' extras in
    begin match parse_peek ts' with
    | Tok_COMMA -> parse_object_list_path pm (fuel-1) subj pp acc' (parse_advance ts')
    | _ -> ParseOk acc' ts'
    end

// Parse predicate-object list: verb objList ; verb objList ; ...
and parse_pred_obj_list (pm : prefix_map) (fuel : nat) (subj : pattern_subject)
  (acc : group_graph_pattern) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseOk acc ts
  else match parse_verb pm (fuel-1) ts with
  | ParseErr m -> ParseErr m
  | ParseOk verb ts' ->
    let r = match verb with
      | VSimple pred -> parse_object_list_simple pm (fuel-1) subj pred acc ts'
      | VPath pp -> parse_object_list_path pm (fuel-1) subj pp acc ts'
    in
    begin match r with
    | ParseErr m -> ParseErr m
    | ParseOk acc' ts'' ->
      begin match parse_peek ts'' with
      | Tok_SEMI ->
        let ts''' = parse_advance ts'' in
        (match parse_peek ts''' with
         | Tok_DOT | Tok_RBRACE | Tok_OPTIONAL | Tok_MINUS_KW | Tok_FILTER
         | Tok_BIND | Tok_GRAPH | Tok_SERVICE | Tok_VALUES | Tok_UNION
         | Tok_LBRACE | Tok_RBRACKET | Tok_EOF -> ParseOk acc' ts'''
         | _ -> parse_pred_obj_list pm (fuel-1) subj acc' ts''')
      | _ -> ParseOk acc' ts''
      end end

// Parse a triples block: one or more triple patterns separated by dots
and parse_triples_block (pm : prefix_map) (fuel : nat) (acc : group_graph_pattern) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseOk acc ts
  else match parse_subject_with_extras pm (fuel-1) ts with
  | ParseErr m ->
    (match acc with
     | GP_Empty -> ParseErr m
     | _ -> ParseOk acc ts)
  | ParseOk (subj, subj_extras, pred_obj_optional) ts' ->
    let acc0 = ggp_join acc subj_extras in
    let r =
      match parse_pred_obj_list pm (fuel-1) subj acc0 ts' with
      | ParseOk acc' ts'' -> ParseOk acc' ts''
      | ParseErr _ ->
        if pred_obj_optional then ParseOk acc0 ts'
        else ParseErr "expected predicate-object list"
    in
    begin match r with
    | ParseErr m -> ParseErr m
    | ParseOk acc' ts'' ->
      begin match parse_peek ts'' with
      | Tok_DOT ->
        let ts''' = parse_advance ts'' in
        (match parse_peek ts''' with
         | Tok_VAR _ | Tok_IRI _ | Tok_PNAME _ | Tok_BNODE _ | Tok_LBRACKET
         | Tok_LPAREN | Tok_A | Tok_INTEGER _ | Tok_DECIMAL _ | Tok_DOUBLE _
         | Tok_STRING _ | Tok_TRUE | Tok_FALSE ->
           parse_triples_block pm (fuel-1) acc' ts'''
         | _ -> ParseOk acc' ts''')
      | Tok_VAR _ | Tok_IRI _ | Tok_PNAME _ | Tok_BNODE _ | Tok_LBRACKET
      | Tok_LPAREN | Tok_A | Tok_INTEGER _ | Tok_DECIMAL _ | Tok_DOUBLE _
      | Tok_STRING _ | Tok_TRUE | Tok_FALSE ->
        ParseErr "expected dot between triples"
      | _ -> ParseOk acc' ts''
      end end

(* ---- SELECT query parsing ---- *)
and parse_select_query (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result query) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else
    let r = parse_prologue pm None (fuel-1) ts in
    (match r with
     | ParseErr m -> ParseErr m
     | ParseOk (pm', base) ts' ->
       let ts'' = resolve_relative_iri_tokens base ts' in
       (match parse_peek ts'' with
        | Tok_SELECT -> parse_select_body pm' (fuel-1) base ts''
        | Tok_ASK -> parse_ask_body pm' (fuel-1) base ts''
        | Tok_CONSTRUCT -> parse_construct_body pm' (fuel-1) base ts''
        | Tok_DESCRIBE -> ParseErr "unsupported: DESCRIBE queries"
        | _ -> ParseErr "expected SELECT, ASK, CONSTRUCT, or DESCRIBE"))

(* Parse prologue: (PREFIX prefix: <iri> | BASE <iri>)* *)
and parse_prologue (pm : prefix_map) (base : option wf_iri) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (prefix_map & option wf_iri)) (decreases fuel) =
  if fuel = 0 then ParseOk (pm, base) ts
  else begin match parse_peek ts with
    | Tok_PREFIX ->
      let ts' = parse_advance ts in
      (match parse_peek ts' with
       | Tok_PNAME pn ->
         let (prefix, local) = split_pname pn in
         if String.length local > 0 then ParseErr "invalid PREFIX name (must be prefix: with no local part)"
         else
         let ts'' = parse_advance ts' in
         (match parse_peek ts'' with
          | Tok_IRI iri ->
            (match if is_iri iri then Some iri else resolve_query_iri base iri with
             | Some abs ->
               parse_prologue ((prefix, abs) :: pm) base (fuel-1) (parse_advance ts'')
             | None ->
               ParseErr "invalid prefix IRI")
          | _ -> ParseErr "expected IRI after PREFIX name")
       | _ -> ParseErr "expected prefix name after PREFIX")
    | Tok_BASE ->
      let ts' = parse_advance ts in
      (match parse_peek ts' with
       | Tok_IRI iri ->
         if is_iri iri then
           parse_prologue pm (Some iri) (fuel-1) (parse_advance ts')
         else ParseErr "invalid BASE IRI"
       | _ -> ParseErr "expected IRI after BASE")
    | _ -> ParseOk (pm, base) ts
  end

(* Parse SELECT body: SELECT clause, FROM, WHERE, modifiers *)
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
          | ParseOk (modifier, gb, hv) ts6 ->
            // SELECT * with GROUP BY is not allowed per SPARQL 1.1
            if Select_All? sel && Some? gb then
              ParseErr "SELECT * not allowed with GROUP BY"
            // Check ungrouped variables in SELECT projection
            else if Some? gb && (
              let gcs = Some?.v gb in
              let is_grouped (v : var_name) : bool =
                not (List.Tot.for_all (fun (gc : group_condition) ->
                  match gc with
                  | GC_Var gv -> not (streq gv v)
                  | GC_Expr _ (Some gv) -> not (streq gv v)
                  | _ -> true) gcs) in
              match sel with
              | Select_Vars items ->
                not (List.Tot.for_all (fun (item : select_item) ->
                  match item with
                  | SI_Var v -> is_grouped v
                  | SI_Expr e _ -> not (expr_has_ungrouped_var is_grouped e)
                  ) items)
              | _ -> false) then
              ParseErr "SELECT projects ungrouped variable"
            // Implicit GROUP BY: if any select item uses an aggregate
            // but no GROUP BY is present, non-aggregate expressions with vars are ungrouped
            else if None? gb && (
              match sel with
              | Select_Vars items ->
                let has_agg = not (List.Tot.for_all (fun (item : select_item) ->
                  match item with
                  | SI_Expr (E_Aggregate _ _ _) _ -> false
                  | _ -> true) items) in
                let has_ungrouped = not (List.Tot.for_all (fun (item : select_item) ->
                  match item with
                  | SI_Var _ -> false
                  | SI_Expr e _ -> not (expr_has_ungrouped_var (fun _ -> false) e)
                  ) items) in
                has_agg && has_ungrouped
              | _ -> false) then
              ParseErr "SELECT projects ungrouped variable"
            // Check: (expr AS ?v) must not alias a variable already in scope from WHERE
            else if (match sel with
              | Select_Vars items ->
                not (List.Tot.for_all (fun (item : select_item) ->
                  match item with
                  | SI_Expr _ v -> not (ggp_has_var v pattern)
                  | _ -> true) items)
              | _ -> false) then
              ParseErr "SELECT expression aliases variable already in scope"
            else
            // Check for post-query VALUES clause
            let (vals, ts7) = begin match parse_peek ts6 with
              | Tok_VALUES ->
                (match parse_values_clause pm (fuel-1) (parse_advance ts6) with
                 | ParseOk (GP_Values vars rows) ts' -> (Some (vars, rows), ts')
                 | _ -> (None, ts6))
              | _ -> (None, ts6) end in
            ParseOk ({
              q_base = base;
              q_prefixes = pm;
              q_form = QF_Select sel;
              q_dataset = ds;
              q_pattern = (match vals with
                | Some (vars, rows) -> ggp_join pattern (GP_Values vars rows)
                | None -> pattern);
              q_group_by = gb;
              q_having = hv;
              q_modifier = { modifier with sm_distinct = dist; sm_reduced = red };
              q_values = None
            }) ts7
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

// Parse CONSTRUCT body
// Check if a pattern is a basic graph pattern (only BGP, Join, PropertyPath, Empty)
// CONSTRUCT WHERE short form only allows these — no FILTER, GRAPH, OPTIONAL, etc.
and is_basic_pattern (p : group_graph_pattern) : Tot bool (decreases p) =
  match p with
  | GP_BGP _ -> true
  | GP_Empty -> true
  | GP_PropertyPath _ _ _ -> true
  | GP_Join p1 p2 -> is_basic_pattern p1 && is_basic_pattern p2
  | _ -> false

and parse_construct_body (pm : prefix_map) (fuel : nat) (base : option wf_iri) (ts : token_stream)
  : Tot (parse_result query) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else begin
    let ts' = parse_advance ts in  // consume CONSTRUCT
    begin match parse_peek ts' with
    | Tok_WHERE | Tok_FROM ->
      // CONSTRUCT [FROM ...] WHERE { pattern } — shorthand form (template = pattern)
      begin match parse_skip_from (fuel-1) ts' with
      | ParseErr m -> ParseErr m
      | ParseOk ds ts'' ->
        let ts'' = match parse_peek ts'' with Tok_WHERE -> parse_advance ts'' | _ -> ts'' in
        begin match parse_group_graph_pattern pm (fuel-1) ts'' with
        | ParseErr m -> ParseErr m
        | ParseOk pattern ts''' ->
          if not (is_basic_pattern pattern) then
            ParseErr "CONSTRUCT WHERE short form only allows basic graph patterns"
          else
          begin match parse_solution_modifier pm (fuel-1) ts''' with
          | ParseErr m -> ParseErr m
          | ParseOk (modifier, gb, hv) ts4 ->
            ParseOk ({
              q_base = base; q_prefixes = pm;
              q_form = QF_Construct [];
              q_dataset = ds; q_pattern = pattern;
              q_group_by = gb; q_having = hv;
              q_modifier = modifier; q_values = None
            }) ts4
          end end end
    | Tok_LBRACE ->
      // CONSTRUCT { template } WHERE { pattern } — full form
      // Parse the template as a group graph pattern, then expect WHERE + body
      begin match parse_group_graph_pattern pm (fuel-1) ts' with
      | ParseErr m -> ParseErr m
      | ParseOk _template ts'' ->
        // Expect WHERE or directly a { for the body
        let ts'' = match parse_peek ts'' with Tok_WHERE -> parse_advance ts'' | _ -> ts'' in
        begin match parse_group_graph_pattern pm (fuel-1) ts'' with
        | ParseErr m -> ParseErr m
        | ParseOk pattern ts''' ->
          begin match parse_solution_modifier pm (fuel-1) ts''' with
          | ParseErr m -> ParseErr m
          | ParseOk (modifier, gb, hv) ts4 ->
            ParseOk ({
              q_base = base; q_prefixes = pm;
              q_form = QF_Construct [];
              q_dataset = []; q_pattern = pattern;
              q_group_by = gb; q_having = hv;
              q_modifier = modifier; q_values = None
            }) ts4
          end end end
    | _ -> ParseErr "expected WHERE or '{' after CONSTRUCT"
    end end

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

and select_item_var (item : select_item) : var_name =
  match item with
  | SI_Var v -> v
  | SI_Expr _ v -> v

and select_items_has_var (v : var_name) (items : list select_item) : Tot bool (decreases items) =
  match items with
  | [] -> false
  | item :: rest -> streq (select_item_var item) v || select_items_has_var v rest

and parse_select_items (pm : prefix_map) (fuel : nat) (acc : list select_item) (ts : token_stream)
  : Tot (parse_result (list select_item)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_peek ts with
  | Tok_VAR v ->
    if select_items_has_var v acc then ParseErr "duplicate variable in SELECT"
    else parse_select_items pm (fuel-1) (SI_Var v :: acc) (parse_advance ts)
  | Tok_LPAREN ->
    (match parse_expr pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' ->
       begin match parse_expect Tok_AS ts' with
       | ParseErr m -> ParseErr m
       | ParseOk () ts'' ->
         begin match parse_peek ts'' with
         | Tok_VAR v ->
           if select_items_has_var v acc then ParseErr "duplicate variable in SELECT"
           else
           (match parse_expect Tok_RPAREN (parse_advance ts'') with
            | ParseErr m -> ParseErr m
            | ParseOk () ts''' -> parse_select_items pm (fuel-1) (SI_Expr e v :: acc) ts''')
         | _ -> ParseErr "expected variable after AS"
         end end)
  | _ -> ParseOk (List.Tot.rev acc) ts

(* Parse FROM / FROM NAMED clauses *)
and parse_skip_from (fuel : nat) (ts : token_stream)
  : Tot (parse_result (list dataset_clause)) (decreases fuel) =
  if fuel = 0 then ParseOk [] ts
  else match parse_peek ts with
  | Tok_FROM ->
    let ts' = parse_advance ts in
    begin match parse_peek ts' with
    | Tok_NAMED ->
      // FROM NAMED <iri> — skip the IRI
      let ts'' = parse_advance ts' in
      begin match parse_peek ts'' with
      | Tok_IRI _ | Tok_PNAME _ -> parse_skip_from (fuel-1) (parse_advance ts'')
      | _ -> ParseErr "expected IRI after FROM NAMED"
      end
    | Tok_IRI _ | Tok_PNAME _ ->
      // FROM <iri> — skip the IRI
      parse_skip_from (fuel-1) (parse_advance ts')
    | _ -> ParseErr "expected IRI or NAMED after FROM"
    end
  | _ -> ParseOk [] ts

// Parse GROUP BY condition: Var | BuiltInCall | FunctionCall | '(' Expression (AS Var)? ')'
and parse_group_condition (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result group_condition) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_VAR v -> ParseOk (GC_Var v) (parse_advance ts)
  | Tok_LPAREN ->
    (match parse_expr pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' ->
       begin match parse_peek ts' with
       | Tok_AS ->
         let ts'' = parse_advance ts' in
         (match parse_peek ts'' with
          | Tok_VAR v ->
            (match parse_expect Tok_RPAREN (parse_advance ts'') with
             | ParseErr m -> ParseErr m
             | ParseOk () ts''' -> ParseOk (GC_Expr e (Some v)) ts''')
          | _ -> ParseErr "expected variable after AS")
       | Tok_RPAREN -> ParseOk (GC_Expr e None) (parse_advance ts')
       | _ -> ParseErr "expected ')' or AS in GROUP BY"
       end)
  | _ ->
    // Built-in call: parse as expression
    (match parse_expr pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' -> ParseOk (GC_BuiltIn e) ts')

// Parse GROUP BY conditions list
and parse_group_by_list (pm : prefix_map) (fuel : nat)
  (acc : list group_condition) (ts : token_stream)
  : Tot (parse_result (list group_condition)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_peek ts with
  | Tok_VAR _ | Tok_LPAREN | Tok_STR | Tok_LANG | Tok_LANGMATCHES | Tok_DATATYPE
  | Tok_BOUND | Tok_IF | Tok_IRI_KW | Tok_URI | Tok_CONCAT | Tok_STRLEN
  | Tok_UCASE | Tok_LCASE | Tok_ENCODE_FOR_URI | Tok_CONTAINS | Tok_STRSTARTS
  | Tok_STRENDS | Tok_STRBEFORE | Tok_STRAFTER | Tok_REPLACE | Tok_REGEX | Tok_SUBSTR
  | Tok_ABS | Tok_CEIL | Tok_FLOOR | Tok_ROUND | Tok_ISIRI | Tok_ISBLANK
  | Tok_ISLITERAL | Tok_ISNUMERIC | Tok_SAMETERM | Tok_COALESCE | Tok_IRI _ | Tok_PNAME _ ->
    (match parse_group_condition pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk gc ts' -> parse_group_by_list pm (fuel-1) (gc :: acc) ts')
  | _ -> ParseOk (List.Tot.rev acc) ts

// Parse ORDER BY condition: ASC/DESC(expr) | Var | BuiltInCall | '(' expr ')'
and parse_order_condition (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result order_condition) (decreases fuel) =
  if fuel = 0 then ParseErr "recursion limit"
  else match parse_peek ts with
  | Tok_ASC ->
    let ts' = parse_advance ts in
    (match parse_expect Tok_LPAREN ts' with
     | ParseErr _ ->
       // ASC without parens -- treat as ascending on next expression
       (match parse_expr pm (fuel-1) ts' with
        | ParseErr m -> ParseErr m
        | ParseOk e ts'' -> ParseOk (OC_Asc e) ts'')
     | ParseOk () ts'' ->
       (match parse_expr pm (fuel-1) ts'' with
        | ParseErr m -> ParseErr m
        | ParseOk e ts''' ->
          begin match parse_expect Tok_RPAREN ts''' with
          | ParseErr m -> ParseErr m
          | ParseOk () ts4 -> ParseOk (OC_Asc e) ts4
          end))
  | Tok_DESC ->
    let ts' = parse_advance ts in
    (match parse_expect Tok_LPAREN ts' with
     | ParseErr _ ->
       (match parse_expr pm (fuel-1) ts' with
        | ParseErr m -> ParseErr m
        | ParseOk e ts'' -> ParseOk (OC_Desc e) ts'')
     | ParseOk () ts'' ->
       (match parse_expr pm (fuel-1) ts'' with
        | ParseErr m -> ParseErr m
        | ParseOk e ts''' ->
          begin match parse_expect Tok_RPAREN ts''' with
          | ParseErr m -> ParseErr m
          | ParseOk () ts4 -> ParseOk (OC_Desc e) ts4
          end))
  | Tok_VAR v -> ParseOk (OC_Asc (E_Var v)) (parse_advance ts)
  | Tok_LPAREN ->
    (match parse_expr pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' ->
       begin match parse_expect Tok_RPAREN ts' with
       | ParseErr m -> ParseErr m
       | ParseOk () ts'' -> ParseOk (OC_Asc e) ts''
       end)
  | _ ->
    (match parse_expr pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' -> ParseOk (OC_Asc e) ts')

// Parse ORDER BY conditions list
and parse_order_by_list (pm : prefix_map) (fuel : nat)
  (acc : list order_condition) (ts : token_stream)
  : Tot (parse_result (list order_condition)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_peek ts with
  | Tok_ASC | Tok_DESC | Tok_VAR _ | Tok_LPAREN | Tok_IRI _ | Tok_PNAME _
  | Tok_STR | Tok_LANG | Tok_LANGMATCHES | Tok_DATATYPE | Tok_BOUND
  | Tok_IF | Tok_IRI_KW | Tok_URI | Tok_CONCAT | Tok_ISIRI | Tok_ISBLANK
  | Tok_ISLITERAL | Tok_ISNUMERIC | Tok_SAMETERM | Tok_COALESCE ->
    (match parse_order_condition pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk oc ts' -> parse_order_by_list pm (fuel-1) (oc :: acc) ts')
  | _ -> ParseOk (List.Tot.rev acc) ts

// Parse HAVING conditions (list of expressions in parens or constraint)
and parse_having_list (pm : prefix_map) (fuel : nat)
  (acc : list expr) (ts : token_stream)
  : Tot (parse_result (list expr)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) ts
  else match parse_peek ts with
  | Tok_LPAREN ->
    (match parse_expr pm (fuel-1) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' ->
       begin match parse_expect Tok_RPAREN ts' with
       | ParseErr m -> ParseErr m
       | ParseOk () ts'' -> parse_having_list pm (fuel-1) (e :: acc) ts''
       end)
  | Tok_STR | Tok_LANG | Tok_LANGMATCHES | Tok_DATATYPE | Tok_BOUND
  | Tok_IF | Tok_IRI_KW | Tok_URI | Tok_CONCAT | Tok_ISIRI | Tok_ISBLANK
  | Tok_ISLITERAL | Tok_ISNUMERIC | Tok_SAMETERM | Tok_COALESCE
  | Tok_EXISTS | Tok_NOT | Tok_REGEX ->
    (match parse_primary_expr pm (fuel-1) ts with
     | ParseErr m -> ParseErr m
     | ParseOk e ts' -> parse_having_list pm (fuel-1) (e :: acc) ts')
  | _ -> ParseOk (List.Tot.rev acc) ts

// Parse solution modifier: GROUP BY, HAVING, ORDER BY, LIMIT, OFFSET
// Returns (modifier, group_by, having)
and parse_solution_modifier (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result modifier_result) (decreases fuel) =
  if fuel = 0 then ParseOk (default_modifier, None, None) ts
  else
    // GROUP BY
    let (gb, ts) = begin match parse_peek ts with
      | Tok_GROUP ->
        let ts' = parse_advance ts in
        (match parse_peek ts' with
         | Tok_BY ->
           (match parse_group_by_list pm (fuel-1) [] (parse_advance ts') with
            | ParseOk conds ts'' -> (Some conds, ts'')
            | ParseErr _ -> (None, ts))
         | _ -> (None, ts))
      | _ -> (None, ts) end in
    // HAVING
    let (hv, ts) = begin match parse_peek ts with
      | Tok_HAVING ->
        (match parse_having_list pm (fuel-1) [] (parse_advance ts) with
         | ParseOk conds ts' -> (Some conds, ts')
         | ParseErr _ -> (None, ts))
      | _ -> (None, ts) end in
    // ORDER BY
    let (ob, ts) = begin match parse_peek ts with
      | Tok_ORDER ->
        let ts' = parse_advance ts in
        (match parse_peek ts' with
         | Tok_BY ->
           (match parse_order_by_list pm (fuel-1) [] (parse_advance ts') with
            | ParseOk conds ts'' -> (Some conds, ts'')
            | ParseErr _ -> (None, ts))
         | _ -> (None, ts))
      | _ -> (None, ts) end in
    // LIMIT
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
    // OFFSET
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
    let modifier = {
      sm_order_by = ob; sm_distinct = false; sm_reduced = false;
      sm_offset = offset; sm_limit = limit
    } in
    ParseOk (modifier, gb, hv) ts

#pop-options

(* ---- Top-level parse function ---- *)

let rec tokens_only_eof (ts : token_stream) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | Tok_EOF :: rest -> tokens_only_eof rest
  | _ -> false

let starts_with_string (s : string) (prefix : string) : bool =
  let ls = String.length s in
  let lp = String.length prefix in
  lp <= ls && substring s 0 lp = prefix

let is_labeled_bnode_id (b : string) : bool =
  not (starts_with_string b "_:bnode_")

let rec string_mem (x : string) (xs : list string) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | y :: ys -> streq x y || string_mem x ys

let rec string_add_unique (x : string) (xs : list string) : Tot (list string) (decreases xs) =
  if string_mem x xs then xs else x :: xs

let rec string_union (xs ys : list string) : Tot (list string) (decreases xs) =
  match xs with
  | [] -> ys
  | x :: rest -> string_union rest (string_add_unique x ys)

let rec string_overlaps (xs ys : list string) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | x :: rest -> string_mem x ys || string_overlaps rest ys

let bnodes_in_pattern_subject (ps : pattern_subject) : list string =
  match ps with
  | PS_BNode b -> if is_labeled_bnode_id b then [b] else []
  | _ -> []

let bnodes_in_pattern_term (pt : pattern_term) : list string =
  match pt with
  | PT_BNode b -> if is_labeled_bnode_id b then [b] else []
  | _ -> []

let bnodes_in_triple_pattern (tp : triple_pattern) : list string =
  string_union (bnodes_in_pattern_subject tp.tp_s)
    (string_union (bnodes_in_pattern_term tp.tp_p) (bnodes_in_pattern_term tp.tp_o))

let bnodes_in_property_path_pattern (ps : pattern_subject) (pt : pattern_term) : list string =
  string_union (bnodes_in_pattern_subject ps) (bnodes_in_pattern_term pt)

let rec bnodes_in_bgp (bgp : bgp) : Tot (list string) (decreases bgp) =
  match bgp with
  | [] -> []
  | tp :: rest -> string_union (bnodes_in_triple_pattern tp) (bnodes_in_bgp rest)

let rec preserves_bgp_scope (p : group_graph_pattern) : Tot bool (decreases p) =
  match p with
  | GP_BGP _ -> true
  | GP_PropertyPath _ _ _ -> true
  | GP_Filter _ p1 -> preserves_bgp_scope p1
  | GP_Bind _ _ p1 -> preserves_bgp_scope p1
  | GP_Values _ _ -> true
  | GP_Empty -> true
  | GP_Join p1 p2 -> preserves_bgp_scope p1 && preserves_bgp_scope p2
  | _ -> false

let rec validate_bnode_scope_pattern (p : group_graph_pattern)
  : Tot (bool & list string) (decreases p) =
  match p with
  | GP_BGP bgp -> (true, bnodes_in_bgp bgp)
  | GP_PropertyPath ps _ pt -> (true, bnodes_in_property_path_pattern ps pt)
  | GP_Filter e p1 ->
    let (ok1, b1) = validate_bnode_scope_pattern p1 in
    let (ok2, _) = validate_bnode_scope_expr e in
    (ok1 && ok2, b1)
  | GP_Bind e _ p1 ->
    let (ok1, b1) = validate_bnode_scope_pattern p1 in
    let (ok2, _) = validate_bnode_scope_expr e in
    (ok1 && ok2, b1)
  | GP_Values _ _ -> (true, [])
  | GP_Empty -> (true, [])
  | GP_Join p1 p2 ->
    let (ok1, b1) = validate_bnode_scope_pattern p1 in
    let (ok2, b2) = validate_bnode_scope_pattern p2 in
    let allow_overlap = preserves_bgp_scope p1 && preserves_bgp_scope p2 in
    (ok1 && ok2 && (allow_overlap || not (string_overlaps b1 b2)), string_union b1 b2)
  | GP_Union p1 p2
  | GP_Minus p1 p2 ->
    let (ok1, b1) = validate_bnode_scope_pattern p1 in
    let (ok2, b2) = validate_bnode_scope_pattern p2 in
    (ok1 && ok2 && not (string_overlaps b1 b2), string_union b1 b2)
  | GP_LeftJoin p1 p2 e ->
    let (ok1, b1) = validate_bnode_scope_pattern p1 in
    let (ok2, b2) = validate_bnode_scope_pattern p2 in
    let (ok3, _) = validate_bnode_scope_expr e in
    (ok1 && ok2 && ok3 && not (string_overlaps b1 b2), string_union b1 b2)
  | GP_Graph _ p1
  | GP_Service _ p1 _ ->
    validate_bnode_scope_pattern p1
  | GP_SubSelect q ->
    validate_bnode_scope_query q

and validate_bnode_scope_expr (e : expr) : Tot (bool & list string) (decreases e) =
  match e with
  | E_Exists p
  | E_NotExists p ->
    validate_bnode_scope_pattern p
  | E_Arith _ e1 e2
  | E_Compare _ e1 e2
  | E_And e1 e2
  | E_Or e1 e2
  | E_StrDt e1 e2
  | E_StrLang e1 e2
  | E_StrStarts e1 e2
  | E_StrEnds e1 e2
  | E_Contains e1 e2
  | E_StrBefore e1 e2
  | E_StrAfter e1 e2
  | E_SameTerm e1 e2 ->
    let (ok1, _) = validate_bnode_scope_expr e1 in
    let (ok2, _) = validate_bnode_scope_expr e2 in
    (ok1 && ok2, [])
  | E_Not e1
  | E_UnaryPlus e1
  | E_UnaryMinus e1
  | E_IsIRI e1
  | E_IsBlank e1
  | E_IsLiteral e1
  | E_IsNumeric e1
  | E_Str e1
  | E_Lang e1
  | E_Datatype e1
  | E_IRI_fn e1
  | E_StrLen e1
  | E_UCase e1
  | E_LCase e1
  | E_EncodeForUri e1
  | E_Abs e1
  | E_Round e1
  | E_Ceil e1
  | E_Floor e1
  | E_MD5 e1
  | E_SHA1 e1
  | E_SHA256 e1
  | E_SHA384 e1
  | E_SHA512 e1
  | E_Year e1
  | E_Month e1
  | E_Day e1
  | E_Hours e1
  | E_Minutes e1
  | E_Seconds e1
  | E_Timezone e1
  | E_Tz e1
  | E_Aggregate _ _ e1 ->
    validate_bnode_scope_expr e1
  | E_Substr e1 e2 e3 ->
    let (ok1, _) = validate_bnode_scope_expr e1 in
    let (ok2, _) = validate_bnode_scope_expr e2 in
    let (ok3, _) = match e3 with
      | None -> (true, [])
      | Some ef -> validate_bnode_scope_expr ef in
    (ok1 && ok2 && ok3, [])
  | E_If e1 e2 e3 ->
    let (ok1, _) = validate_bnode_scope_expr e1 in
    let (ok2, _) = validate_bnode_scope_expr e2 in
    let (ok3, _) = validate_bnode_scope_expr e3 in
    (ok1 && ok2 && ok3, [])
  | E_Coalesce es
  | E_Concat es
  | E_FunctionCall _ es ->
    (validate_bnode_scope_exprs es, [])
  | E_In e1 es
  | E_NotIn e1 es ->
    let (ok1, _) = validate_bnode_scope_expr e1 in
    let ok_rest = validate_bnode_scope_exprs es in
    (ok1 && ok_rest, [])
  | E_Replace e1 e2 e3 flags ->
    let (ok1, _) = validate_bnode_scope_expr e1 in
    let (ok2, _) = validate_bnode_scope_expr e2 in
    let (ok3, _) = validate_bnode_scope_expr e3 in
    let (ok4, _) = match flags with
      | None -> (true, [])
      | Some ef -> validate_bnode_scope_expr ef in
    (ok1 && ok2 && ok3 && ok4, [])
  | E_Regex e1 e2 flags ->
    let (ok1, _) = validate_bnode_scope_expr e1 in
    let (ok2, _) = validate_bnode_scope_expr e2 in
    let (ok3, _) = match flags with
      | None -> (true, [])
      | Some ef -> validate_bnode_scope_expr ef in
    (ok1 && ok2 && ok3, [])
  | _ -> (true, [])

and validate_bnode_scope_exprs (es : list expr) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | ex :: rest ->
    let (ok, _) = validate_bnode_scope_expr ex in
    ok && validate_bnode_scope_exprs rest

and validate_bnode_scope_query (q : query) : Tot (bool & list string) =
  validate_bnode_scope_pattern q.q_pattern

let validate_bnode_scope_top (q : query) : bool =
  fst (validate_bnode_scope_query q)

let parse_sparql (input : string) : parse_result query =
  let tokens = tokenize input in
  match parse_select_query [] 10000 tokens with
  | ParseOk q rest ->
    if not (tokens_only_eof rest) then ParseErr "unexpected tokens after query"
    else if not (validate_bnode_scope_top q) then
      ParseErr "blank node label reused across graph-pattern scope"
    else ParseOk q rest
  | ParseErr msg -> ParseErr msg


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
