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
assume val char_at : string -> pos -> FStar.Char.char

(* Check if position is at or past end of input *)
let at_end (input : string) (p : pos) : bool =
  p >= String.length input

(* Peek at character without advancing *)
let peek_char (input : string) (p : pos) : FStar.Char.char =
  if at_end input p then FStar.Char.char_of_int 0
  else char_at input p

(* Extract substring *)
assume val substring : string -> pos -> nat -> string

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

(* Upper-case a string for keyword matching *)
assume val string_upper : string -> string

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
   Used by blank node labels and prefixed names per SPARQL grammar. *)
let rec trim_trailing_dots (input : string) (start : pos) (end_pos : pos)
  : Tot pos (decreases end_pos) =
  if end_pos = 0 || end_pos <= start then start
  else if char_code (char_at input (end_pos - 1)) = 0x2E (* . *)
  then trim_trailing_dots input start (end_pos - 1)
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

(* Scan IRI content starting after <, returns (iri_string, pos_after_>) *)
let scan_iri (input : string) (p : pos) : (string & pos) =
  let end_p = scan_iri_end input p in
  let raw = substring input p (end_p - p) in
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
    let raw = substring input p_start (end_p - p_start) in
    (process_string_escapes raw, end_p + 3) (* skip closing """ or ''' *)
  else
    let p_start = p + 1 in
    let end_p = scan_short_string_end input p_start q_code in
    let raw = substring input p_start (end_p - p_start) in
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
    (Tok_PNAME (substring input p (p2 - p)), p2)
  else
    (* Keyword or bare name *)
    let word = substring input p (p1 - p) in
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
  let text = substring input p (p3 - p) in
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
  (substring input p (p' - p), p')

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
  (substring input p (p' - p), p')

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
  (substring input p (p' - p), p')

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

(* Tokenize entire input into a token list.
   Repeatedly calls next_token until EOF. Safety: stops if no progress. *)
let rec tokenize_loop (input : string) (p : pos) (acc : list token)
  : Tot (list token) (decreases (String.length input + 1 - p)) =
  if p > String.length input then List.Tot.rev (Tok_EOF :: acc)
  else
    let (tok, p') = next_token input p in
    match tok with
    | Tok_EOF -> List.Tot.rev (Tok_EOF :: acc)
    | _ ->
      if p' <= p then List.Tot.rev (Tok_EOF :: acc) (* no progress — stop *)
      else tokenize_loop input p' (tok :: acc)

let tokenize (input : string) : list token =
  tokenize_loop input 0 []

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

(* Split a prefixed name "prefix:local" into (prefix, local) *)
let split_pname (pn : string) : (string & string) =
  match find_char_pos pn 0 0x3A (* : *) with
  | Some i -> (substring pn 0 i, substring pn (i + 1) (String.length pn - i - 1))
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

(* Forward declarations for mutual recursion — these are the main parse functions.
   Each takes a prefix map and token stream, returns a parse result.
   Actual implementations use assume val to break the mutual recursion cycle
   for F* extraction; the OCaml stubs wire them together (same pattern as
   eval_expr_fwd / eval_exists_fwd in the algebra). *)

assume val parse_expr : prefix_map -> token_stream -> parse_result expr
assume val parse_group_graph_pattern : prefix_map -> nat -> token_stream -> parse_result group_graph_pattern
assume val parse_select_query : prefix_map -> nat -> token_stream -> parse_result query

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

(** ====================================================================== **)
(** Part 9: Parser Implementation                                           **)
(**                                                                          **)
(** Full recursive descent parser for SPARQL 1.1 queries.                    **)
(** Uses forward declarations (assume val parse_expr, parse_group_graph_     **)
(** pattern, parse_select_query) for mutual recursion. These are wired       **)
(** post-extraction by ocaml-patches.sh (same pattern as eval_expr_fwd).     **)
(** ====================================================================== **)

(* Default fuel for recursive descent *)
let default_fuel : nat = 100

(* Alias for rdf:type IRI (xsd_string, xsd_integer etc. come from RDF.Graph.Executable) *)
let rdf_type_iri : wf_iri = rdf_type

(* Check if a group_graph_pattern is empty.
   Can't use = on noeq types, so pattern match instead. *)
let is_gp_empty (g : group_graph_pattern) : bool =
  match g with
  | GP_Empty -> true
  | _ -> false

(* Join two patterns, skipping GP_Empty *)
let gp_join (left : group_graph_pattern) (right : group_graph_pattern)
  : group_graph_pattern =
  if is_gp_empty left then right
  else if is_gp_empty right then left
  else GP_Join left right

(* --- Prologue: PREFIX and BASE declarations --- *)

let rec parse_prologue (pm : prefix_map) (base : option string) (ts : token_stream)
  : (prefix_map & option string & token_stream) =
  match ts with
  | Tok_PREFIX :: rest ->
    (match rest with
     | (Tok_PNAME pn) :: (Tok_IRI iri) :: rest' ->
       (* pn should be "prefix:" — extract the prefix name without colon *)
       let prefix_name = match find_char_pos pn 0 0x3A with
         | Some i -> substring pn 0 i
         | None -> pn in
       parse_prologue ((prefix_name, iri) :: pm) base rest'
     | _ -> (pm, base, ts))  (* error recovery: return what we have *)
  | Tok_BASE :: rest ->
    (match rest with
     | (Tok_IRI iri) :: rest' -> parse_prologue pm (Some iri) rest'
     | _ -> (pm, base, ts))
  | _ -> (pm, base, ts)

(* --- Resolve an IRI or prefixed name from a token --- *)

let resolve_iri_token (tok : token) (pm : prefix_map) : option wf_iri =
  match tok with
  | Tok_IRI i -> if is_iri i then Some i else None
  | Tok_PNAME pn -> resolve_pname pn pm
  | Tok_A -> Some rdf_type_iri
  | _ -> None

(* Make a plain literal (xsd:string datatype, no lang tag) *)
let make_plain_literal (s : string) : literal =
  { lexical_form = s; datatype = xsd_string; lang_tag = None }

(* Make a typed literal *)
let make_typed_literal (lex : string) (dt : wf_iri) : literal =
  { lexical_form = lex; datatype = dt; lang_tag = None }

(* Make a language-tagged literal *)
let make_lang_literal (lex : string) (tag : string) : literal =
  { lexical_form = lex; datatype = rdf_lang_string; lang_tag = Some tag }

// --- Expression Parser: Precedence Climbing ---
// Precedence levels (tightest to loosest):
//   0: Primary (literals, variables, function calls, parenthesized)
//   1: Unary (!, -, +)
//   2: Multiplicative (*, /)
//   3: Additive (+, -)
//   4: Relational (=, !=, <, >, <=, >=, IN, NOT IN)
//   5: Conditional AND (&&)
//   6: Conditional OR (||)

(* Parse a string literal with optional language tag or datatype *)
let parse_literal_after_string (s : string) (ts : token_stream) (pm : prefix_map)
  : parse_result expr =
  match ts with
  | (Tok_LANGTAG tag) :: rest ->
    ParseOk (E_Literal (make_lang_literal s tag)) rest
  | Tok_HATHAT :: rest ->
    (match rest with
     | (Tok_IRI dt) :: rest' ->
       if is_iri dt then ParseOk (E_Literal (make_typed_literal s dt)) rest'
       else ParseErr "invalid datatype IRI"
     | (Tok_PNAME pn) :: rest' ->
       (match resolve_pname pn pm with
        | Some dt -> ParseOk (E_Literal (make_typed_literal s dt)) rest'
        | None -> ParseErr "undefined prefix in datatype")
     | _ -> ParseErr "expected datatype after ^^")
  | _ -> ParseOk (E_Literal (make_plain_literal s)) ts

(* Parse a single argument built-in: FUNC(expr) *)
let parse_one_arg_builtin (pm : prefix_map) (ts : token_stream) (mk : expr -> expr)
  : parse_result expr =
  match ts with
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk (mk e) rest''
        | _ -> ParseErr "expected ) after built-in argument")
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseErr "expected ( after built-in function"

(* Parse a two argument built-in: FUNC(expr, expr) *)
let parse_two_arg_builtin (pm : prefix_map) (ts : token_stream) (mk : expr -> expr -> expr)
  : parse_result expr =
  match ts with
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseOk e1 rest' ->
       (match rest' with
        | Tok_COMMA :: rest'' ->
          (match parse_expr pm rest'' with
           | ParseOk e2 rest''' ->
             (match rest''' with
              | Tok_RPAREN :: rest'''' -> ParseOk (mk e1 e2) rest''''
              | _ -> ParseErr "expected ) after built-in arguments")
           | ParseErr msg -> ParseErr msg)
        | _ -> ParseErr "expected , between built-in arguments")
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseErr "expected ( after built-in function"

(* Parse aggregate: AGG([DISTINCT] expr) *)
let parse_aggregate_expr (pm : prefix_map) (ts : token_stream) (agg_fn : aggregate_fn)
  : parse_result expr =
  match ts with
  | Tok_LPAREN :: rest ->
    let (distinct, rest') = match rest with
      | Tok_DISTINCT :: r -> (true, r)
      | _ -> (false, rest) in
    // COUNT( * ) special case
    (match rest' with
     | Tok_STAR :: Tok_RPAREN :: rest'' ->
       ParseOk (E_Aggregate agg_fn distinct (E_NumericLit 1)) rest''
     | _ ->
       (match parse_expr pm rest' with
        | ParseOk e rest'' ->
          (match rest'' with
           | Tok_RPAREN :: rest''' -> ParseOk (E_Aggregate agg_fn distinct e) rest'''
           | _ -> ParseErr "expected ) after aggregate")
        | ParseErr msg -> ParseErr msg))
  | _ -> ParseErr "expected ( after aggregate function"

(* Parse GROUP_CONCAT([DISTINCT] expr [; SEPARATOR = string]) *)
let parse_group_concat (pm : prefix_map) (ts : token_stream)
  : parse_result expr =
  match ts with
  | Tok_LPAREN :: rest ->
    let (distinct, rest') = match rest with
      | Tok_DISTINCT :: r -> (true, r)
      | _ -> (false, rest) in
    (match parse_expr pm rest' with
     | ParseOk e rest'' ->
       let (sep, rest''') = match rest'' with
         | Tok_SEMI :: Tok_SEPARATOR :: Tok_EQ :: (Tok_STRING s) :: r -> (Some s, r)
         | _ -> (None, rest'') in
       (match rest''' with
        | Tok_RPAREN :: rest'''' ->
          ParseOk (E_Aggregate (Agg_GroupConcat sep) distinct e) rest''''
        | _ -> ParseErr "expected ) after GROUP_CONCAT")
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseErr "expected ( after GROUP_CONCAT"

(* Parse comma-separated expression list *)
let rec parse_expr_list (pm : prefix_map) (ts : token_stream) (acc : list expr)
  : parse_result (list expr) =
  match parse_expr pm ts with
  | ParseOk e rest ->
    (match rest with
     | Tok_COMMA :: rest' -> parse_expr_list pm rest' (e :: acc)
     | _ -> ParseOk (List.Tot.rev (e :: acc)) rest)
  | ParseErr msg -> ParseErr msg

(* Parse primary expression (tightest binding) *)
let parse_primary_expr_impl (pm : prefix_map) (ts : token_stream) : parse_result expr =
  match ts with
  (* Variables *)
  | (Tok_VAR v) :: rest -> ParseOk (E_Var v) rest
  (* IRIs *)
  | (Tok_IRI i) :: rest ->
    (* Could be an IRI literal or a function call *)
    (match rest with
     | Tok_LPAREN :: _ ->
       (* Function call: <iri>(args) *)
       (match rest with
        | Tok_LPAREN :: Tok_RPAREN :: rest' -> ParseOk (E_FunctionCall i []) rest'
        | Tok_LPAREN :: rest' ->
          (match parse_expr_list pm rest' [] with
           | ParseOk args rest'' ->
             (match rest'' with
              | Tok_RPAREN :: rest''' -> ParseOk (E_FunctionCall i args) rest'''
              | _ -> ParseErr "expected ) after function call arguments")
           | ParseErr msg -> ParseErr msg)
        | _ -> ParseOk (E_IRI i) rest)
     | _ -> ParseOk (E_IRI i) rest)
  | (Tok_PNAME pn) :: rest ->
    (match resolve_pname pn pm with
     | Some iri ->
       (* Could be function call *)
       (match rest with
        | Tok_LPAREN :: Tok_RPAREN :: rest' -> ParseOk (E_FunctionCall iri []) rest'
        | Tok_LPAREN :: rest' ->
          (match parse_expr_list pm rest' [] with
           | ParseOk args rest'' ->
             (match rest'' with
              | Tok_RPAREN :: rest''' -> ParseOk (E_FunctionCall iri args) rest'''
              | _ -> ParseErr "expected ) after function call")
           | ParseErr msg -> ParseErr msg)
        | _ -> ParseOk (E_IRI iri) rest)
     | None -> ParseErr "undefined prefix in expression")
  (* String literals *)
  | (Tok_STRING s) :: rest -> parse_literal_after_string s rest pm
  (* Numeric literals *)
  | (Tok_INTEGER n) :: rest -> ParseOk (E_Literal (make_typed_literal n xsd_integer)) rest
  | (Tok_DECIMAL n) :: rest -> ParseOk (E_DecimalLit n) rest
  | (Tok_DOUBLE n) :: rest -> ParseOk (E_DoubleLit n) rest
  (* Boolean literals *)
  | Tok_TRUE :: rest -> ParseOk (E_BoolLit true) rest
  | Tok_FALSE :: rest -> ParseOk (E_BoolLit false) rest
  (* Parenthesized expression *)
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk e rest''
        | _ -> ParseErr "expected ) after parenthesized expression")
     | ParseErr msg -> ParseErr msg)
  (* Unary operators *)
  | Tok_BANG :: rest ->
    (match parse_expr pm rest with
     | ParseOk e rest' -> ParseOk (E_Not e) rest'
     | ParseErr msg -> ParseErr msg)
  | Tok_MINUS_OP :: rest ->
    (match parse_expr pm rest with
     | ParseOk e rest' -> ParseOk (E_UnaryMinus e) rest'
     | ParseErr msg -> ParseErr msg)
  | Tok_PLUS :: rest ->
    (match parse_expr pm rest with
     | ParseOk e rest' -> ParseOk (E_UnaryPlus e) rest'
     | ParseErr msg -> ParseErr msg)
  (* EXISTS / NOT EXISTS *)
  | Tok_EXISTS :: rest ->
    (match parse_group_graph_pattern pm default_fuel rest with
     | ParseOk ggp rest' -> ParseOk (E_Exists ggp) rest'
     | ParseErr msg -> ParseErr msg)
  | Tok_NOT :: Tok_EXISTS :: rest ->
    (match parse_group_graph_pattern pm default_fuel rest with
     | ParseOk ggp rest' -> ParseOk (E_NotExists ggp) rest'
     | ParseErr msg -> ParseErr msg)
  (* One-argument built-in functions *)
  | Tok_STR :: rest -> parse_one_arg_builtin pm rest E_Str
  | Tok_LANG :: rest -> parse_one_arg_builtin pm rest E_Lang
  | Tok_DATATYPE :: rest -> parse_one_arg_builtin pm rest E_Datatype
  | Tok_IRI_KW :: rest -> parse_one_arg_builtin pm rest E_IRI_fn
  | Tok_URI :: rest -> parse_one_arg_builtin pm rest E_IRI_fn
  | Tok_ABS :: rest -> parse_one_arg_builtin pm rest E_Abs
  | Tok_CEIL :: rest -> parse_one_arg_builtin pm rest E_Ceil
  | Tok_FLOOR :: rest -> parse_one_arg_builtin pm rest E_Floor
  | Tok_ROUND :: rest -> parse_one_arg_builtin pm rest E_Round
  | Tok_STRLEN :: rest -> parse_one_arg_builtin pm rest E_StrLen
  | Tok_UCASE :: rest -> parse_one_arg_builtin pm rest E_UCase
  | Tok_LCASE :: rest -> parse_one_arg_builtin pm rest E_LCase
  | Tok_ENCODE_FOR_URI :: rest -> parse_one_arg_builtin pm rest E_EncodeForUri
  | Tok_ISIRI :: rest -> parse_one_arg_builtin pm rest E_IsIRI
  | Tok_ISBLANK :: rest -> parse_one_arg_builtin pm rest E_IsBlank
  | Tok_ISLITERAL :: rest -> parse_one_arg_builtin pm rest E_IsLiteral
  | Tok_ISNUMERIC :: rest -> parse_one_arg_builtin pm rest E_IsNumeric
  | Tok_YEAR :: rest -> parse_one_arg_builtin pm rest E_Year
  | Tok_MONTH :: rest -> parse_one_arg_builtin pm rest E_Month
  | Tok_DAY :: rest -> parse_one_arg_builtin pm rest E_Day
  | Tok_HOURS :: rest -> parse_one_arg_builtin pm rest E_Hours
  | Tok_MINUTES :: rest -> parse_one_arg_builtin pm rest E_Minutes
  | Tok_SECONDS :: rest -> parse_one_arg_builtin pm rest E_Seconds
  | Tok_TIMEZONE :: rest -> parse_one_arg_builtin pm rest E_Timezone
  | Tok_TZ :: rest -> parse_one_arg_builtin pm rest E_Tz
  | Tok_MD5 :: rest -> parse_one_arg_builtin pm rest E_MD5
  | Tok_SHA1 :: rest -> parse_one_arg_builtin pm rest E_SHA1
  | Tok_SHA256 :: rest -> parse_one_arg_builtin pm rest E_SHA256
  | Tok_SHA384 :: rest -> parse_one_arg_builtin pm rest E_SHA384
  | Tok_SHA512 :: rest -> parse_one_arg_builtin pm rest E_SHA512
  (* Two-argument built-in functions *)
  | Tok_LANGMATCHES :: rest -> parse_two_arg_builtin pm rest (fun e1 e2 -> E_FunctionCall "http://www.w3.org/2005/xpath-functions#matches" [e1; e2])
  | Tok_SAMETERM :: rest -> parse_two_arg_builtin pm rest E_SameTerm
  | Tok_STRDT :: rest -> parse_two_arg_builtin pm rest E_StrDt
  | Tok_STRLANG :: rest -> parse_two_arg_builtin pm rest E_StrLang
  | Tok_STRSTARTS :: rest -> parse_two_arg_builtin pm rest E_StrStarts
  | Tok_STRENDS :: rest -> parse_two_arg_builtin pm rest E_StrEnds
  | Tok_CONTAINS :: rest -> parse_two_arg_builtin pm rest E_Contains
  | Tok_STRBEFORE :: rest -> parse_two_arg_builtin pm rest E_StrBefore
  | Tok_STRAFTER :: rest -> parse_two_arg_builtin pm rest E_StrAfter
  (* BOUND(?var) — special: argument is a variable name, not an expression *)
  | Tok_BOUND :: rest ->
    (match rest with
     | Tok_LPAREN :: (Tok_VAR v) :: Tok_RPAREN :: rest' -> ParseOk (E_Bound v) rest'
     | _ -> ParseErr "expected (variable) after BOUND")
  (* IF(cond, then, else) *)
  | Tok_IF :: rest ->
    (match rest with
     | Tok_LPAREN :: rest' ->
       (match parse_expr pm rest' with
        | ParseOk cond rest'' ->
          (match rest'' with
           | Tok_COMMA :: rest''' ->
             (match parse_expr pm rest''' with
              | ParseOk then_e rest'''' ->
                (match rest'''' with
                 | Tok_COMMA :: rest5 ->
                   (match parse_expr pm rest5 with
                    | ParseOk else_e rest6 ->
                      (match rest6 with
                       | Tok_RPAREN :: rest7 -> ParseOk (E_If cond then_e else_e) rest7
                       | _ -> ParseErr "expected ) after IF")
                    | ParseErr msg -> ParseErr msg)
                 | _ -> ParseErr "expected , in IF")
              | ParseErr msg -> ParseErr msg)
           | _ -> ParseErr "expected , in IF")
        | ParseErr msg -> ParseErr msg)
     | _ -> ParseErr "expected ( after IF")
  (* COALESCE(expr, ...) *)
  | Tok_COALESCE :: rest ->
    (match rest with
     | Tok_LPAREN :: rest' ->
       (match parse_expr_list pm rest' [] with
        | ParseOk args rest'' ->
          (match rest'' with
           | Tok_RPAREN :: rest''' -> ParseOk (E_Coalesce args) rest'''
           | _ -> ParseErr "expected ) after COALESCE")
        | ParseErr msg -> ParseErr msg)
     | _ -> ParseErr "expected ( after COALESCE")
  (* CONCAT(expr, ...) *)
  | Tok_CONCAT :: rest ->
    (match rest with
     | Tok_LPAREN :: rest' ->
       (match parse_expr_list pm rest' [] with
        | ParseOk args rest'' ->
          (match rest'' with
           | Tok_RPAREN :: rest''' -> ParseOk (E_Concat args) rest'''
           | _ -> ParseErr "expected ) after CONCAT")
        | ParseErr msg -> ParseErr msg)
     | _ -> ParseErr "expected ( after CONCAT")
  (* SUBSTR(expr, expr [, expr]) *)
  | Tok_SUBSTR :: rest ->
    (match rest with
     | Tok_LPAREN :: rest' ->
       (match parse_expr pm rest' with
        | ParseOk e1 rest'' ->
          (match rest'' with
           | Tok_COMMA :: rest''' ->
             (match parse_expr pm rest''' with
              | ParseOk e2 rest'''' ->
                (match rest'''' with
                 | Tok_COMMA :: rest5 ->
                   (match parse_expr pm rest5 with
                    | ParseOk e3 rest6 ->
                      (match rest6 with
                       | Tok_RPAREN :: rest7 -> ParseOk (E_Substr e1 e2 (Some e3)) rest7
                       | _ -> ParseErr "expected ) after SUBSTR")
                    | ParseErr msg -> ParseErr msg)
                 | Tok_RPAREN :: rest5 -> ParseOk (E_Substr e1 e2 None) rest5
                 | _ -> ParseErr "expected , or ) in SUBSTR")
              | ParseErr msg -> ParseErr msg)
           | _ -> ParseErr "expected , in SUBSTR")
        | ParseErr msg -> ParseErr msg)
     | _ -> ParseErr "expected ( after SUBSTR")
  (* REGEX(expr, expr [, expr]) *)
  | Tok_REGEX :: rest ->
    (match rest with
     | Tok_LPAREN :: rest' ->
       (match parse_expr pm rest' with
        | ParseOk e1 rest'' ->
          (match rest'' with
           | Tok_COMMA :: rest''' ->
             (match parse_expr pm rest''' with
              | ParseOk e2 rest'''' ->
                (match rest'''' with
                 | Tok_COMMA :: rest5 ->
                   (match parse_expr pm rest5 with
                    | ParseOk e3 rest6 ->
                      (match rest6 with
                       | Tok_RPAREN :: rest7 -> ParseOk (E_Regex e1 e2 (Some e3)) rest7
                       | _ -> ParseErr "expected ) after REGEX")
                    | ParseErr msg -> ParseErr msg)
                 | Tok_RPAREN :: rest5 -> ParseOk (E_Regex e1 e2 None) rest5
                 | _ -> ParseErr "expected , or ) in REGEX")
              | ParseErr msg -> ParseErr msg)
           | _ -> ParseErr "expected , in REGEX")
        | ParseErr msg -> ParseErr msg)
     | _ -> ParseErr "expected ( after REGEX")
  (* REPLACE(expr, expr, expr [, expr]) *)
  | Tok_REPLACE :: rest ->
    (match rest with
     | Tok_LPAREN :: rest' ->
       (match parse_expr pm rest' with
        | ParseOk e1 rest'' ->
          (match rest'' with
           | Tok_COMMA :: rest''' ->
             (match parse_expr pm rest''' with
              | ParseOk e2 rest'''' ->
                (match rest'''' with
                 | Tok_COMMA :: rest5 ->
                   (match parse_expr pm rest5 with
                    | ParseOk e3 rest6 ->
                      (match rest6 with
                       | Tok_COMMA :: rest7 ->
                         (match parse_expr pm rest7 with
                          | ParseOk e4 rest8 ->
                            (match rest8 with
                             | Tok_RPAREN :: rest9 -> ParseOk (E_Replace e1 e2 e3 (Some e4)) rest9
                             | _ -> ParseErr "expected ) after REPLACE")
                          | ParseErr msg -> ParseErr msg)
                       | Tok_RPAREN :: rest7 -> ParseOk (E_Replace e1 e2 e3 None) rest7
                       | _ -> ParseErr "expected , or ) in REPLACE")
                    | ParseErr msg -> ParseErr msg)
                 | _ -> ParseErr "expected , in REPLACE")
              | ParseErr msg -> ParseErr msg)
           | _ -> ParseErr "expected , in REPLACE")
        | ParseErr msg -> ParseErr msg)
     | _ -> ParseErr "expected ( after REPLACE")
  (* NOW() — no arguments *)
  | Tok_NOW :: rest ->
    (match rest with
     | Tok_LPAREN :: Tok_RPAREN :: rest' -> ParseOk E_Now rest'
     | _ -> ParseErr "expected () after NOW")
  | Tok_RAND :: rest ->
    (match rest with
     | Tok_LPAREN :: Tok_RPAREN :: rest' -> ParseOk (E_FunctionCall "RAND" []) rest'
     | _ -> ParseErr "expected () after RAND")
  | Tok_UUID :: rest ->
    (match rest with
     | Tok_LPAREN :: Tok_RPAREN :: rest' -> ParseOk (E_FunctionCall "UUID" []) rest'
     | _ -> ParseErr "expected () after UUID")
  | Tok_STRUUID :: rest ->
    (match rest with
     | Tok_LPAREN :: Tok_RPAREN :: rest' -> ParseOk (E_FunctionCall "STRUUID" []) rest'
     | _ -> ParseErr "expected () after STRUUID")
  | Tok_BNODE_KW :: rest ->
    (match rest with
     | Tok_LPAREN :: Tok_RPAREN :: rest' -> ParseOk (E_FunctionCall "BNODE" []) rest'
     | Tok_LPAREN :: rest' -> parse_one_arg_builtin pm rest (fun e -> E_FunctionCall "BNODE" [e])
     | _ -> ParseErr "expected ( after BNODE")
  (* Aggregate functions *)
  | Tok_COUNT :: rest -> parse_aggregate_expr pm rest Agg_Count
  | Tok_SUM :: rest -> parse_aggregate_expr pm rest Agg_Sum
  | Tok_MIN_KW :: rest -> parse_aggregate_expr pm rest Agg_Min
  | Tok_MAX_KW :: rest -> parse_aggregate_expr pm rest Agg_Max
  | Tok_AVG :: rest -> parse_aggregate_expr pm rest Agg_Avg
  | Tok_SAMPLE :: rest -> parse_aggregate_expr pm rest Agg_Sample
  | Tok_GROUP_CONCAT :: rest -> parse_group_concat pm rest
  (* IN list: handled at relational level *)
  | _ -> ParseErr "unexpected token in expression"

(* Parse multiplicative expression: e1 * e2 / e3 *)
let rec parse_mult_tail (pm : prefix_map) (left : expr) (ts : token_stream)
  : parse_result expr =
  match ts with
  | Tok_STAR :: rest ->
    (match parse_primary_expr_impl pm rest with
     | ParseOk right rest' -> parse_mult_tail pm (E_Arith Mul left right) rest'
     | ParseErr msg -> ParseErr msg)
  | Tok_SLASH :: rest ->
    (match parse_primary_expr_impl pm rest with
     | ParseOk right rest' -> parse_mult_tail pm (E_Arith Div left right) rest'
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseOk left ts

let parse_multiplicative_expr (pm : prefix_map) (ts : token_stream)
  : parse_result expr =
  match parse_primary_expr_impl pm ts with
  | ParseOk left rest -> parse_mult_tail pm left rest
  | ParseErr msg -> ParseErr msg

(* Parse additive expression: e1 + e2 - e3 *)
let rec parse_add_tail (pm : prefix_map) (left : expr) (ts : token_stream)
  : parse_result expr =
  match ts with
  | Tok_PLUS :: rest ->
    (match parse_multiplicative_expr pm rest with
     | ParseOk right rest' -> parse_add_tail pm (E_Arith Add left right) rest'
     | ParseErr msg -> ParseErr msg)
  | Tok_MINUS_OP :: rest ->
    (match parse_multiplicative_expr pm rest with
     | ParseOk right rest' -> parse_add_tail pm (E_Arith Sub left right) rest'
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseOk left ts

let parse_additive_expr (pm : prefix_map) (ts : token_stream)
  : parse_result expr =
  match parse_multiplicative_expr pm ts with
  | ParseOk left rest -> parse_add_tail pm left rest
  | ParseErr msg -> ParseErr msg

(* Parse IN/NOT IN list: (expr, expr, ...) *)
let parse_in_list (pm : prefix_map) (ts : token_stream)
  : parse_result (list expr) =
  match ts with
  | Tok_LPAREN :: Tok_RPAREN :: rest -> ParseOk [] rest
  | Tok_LPAREN :: rest ->
    (match parse_expr_list pm rest [] with
     | ParseOk args rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk args rest''
        | _ -> ParseErr "expected ) after IN list")
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseErr "expected ( for IN list"

(* Parse relational expression: comparisons, IN, NOT IN *)
let parse_relational_expr (pm : prefix_map) (ts : token_stream)
  : parse_result expr =
  match parse_additive_expr pm ts with
  | ParseOk left rest ->
    (match rest with
     | Tok_EQ :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseOk right rest'' -> ParseOk (E_Compare CmpEq left right) rest''
        | ParseErr msg -> ParseErr msg)
     | Tok_NE :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseOk right rest'' -> ParseOk (E_Compare CmpNe left right) rest''
        | ParseErr msg -> ParseErr msg)
     | Tok_LT :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseOk right rest'' -> ParseOk (E_Compare CmpLt left right) rest''
        | ParseErr msg -> ParseErr msg)
     | Tok_GT :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseOk right rest'' -> ParseOk (E_Compare CmpGt left right) rest''
        | ParseErr msg -> ParseErr msg)
     | Tok_LE :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseOk right rest'' -> ParseOk (E_Compare CmpLe left right) rest''
        | ParseErr msg -> ParseErr msg)
     | Tok_GE :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseOk right rest'' -> ParseOk (E_Compare CmpGe left right) rest''
        | ParseErr msg -> ParseErr msg)
     | Tok_IN :: rest' ->
       (match parse_in_list pm rest' with
        | ParseOk exprs rest'' -> ParseOk (E_In left exprs) rest''
        | ParseErr msg -> ParseErr msg)
     | Tok_NOT :: Tok_IN :: rest' ->
       (match parse_in_list pm rest' with
        | ParseOk exprs rest'' -> ParseOk (E_NotIn left exprs) rest''
        | ParseErr msg -> ParseErr msg)
     | _ -> ParseOk left rest)
  | ParseErr msg -> ParseErr msg

(* Parse AND expression: e1 && e2 && e3 *)
let rec parse_and_tail (pm : prefix_map) (left : expr) (ts : token_stream)
  : parse_result expr =
  match ts with
  | Tok_AND :: rest ->
    (match parse_relational_expr pm rest with
     | ParseOk right rest' -> parse_and_tail pm (E_And left right) rest'
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseOk left ts

let parse_and_expr (pm : prefix_map) (ts : token_stream) : parse_result expr =
  match parse_relational_expr pm ts with
  | ParseOk left rest -> parse_and_tail pm left rest
  | ParseErr msg -> ParseErr msg

(* Parse OR expression (top level): e1 || e2 || e3 *)
let rec parse_or_tail (pm : prefix_map) (left : expr) (ts : token_stream)
  : parse_result expr =
  match ts with
  | Tok_OR :: rest ->
    (match parse_and_expr pm rest with
     | ParseOk right rest' -> parse_or_tail pm (E_Or left right) rest'
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseOk left ts

(* Top-level expression parser implementation *)
let parse_expr_impl (pm : prefix_map) (ts : token_stream) : parse_result expr =
  match parse_and_expr pm ts with
  | ParseOk left rest -> parse_or_tail pm left rest
  | ParseErr msg -> ParseErr msg

(* --- Pattern Term and Triple Pattern Parsing --- *)

(* Parse a pattern term (object position): variable, IRI, bnode, or literal *)
let parse_pattern_term (pm : prefix_map) (ts : token_stream)
  : parse_result pattern_term =
  match ts with
  | (Tok_VAR v) :: rest -> ParseOk (PT_Var v) rest
  | (Tok_IRI i) :: rest -> ParseOk (PT_IRI i) rest
  | (Tok_PNAME pn) :: rest ->
    (match resolve_pname pn pm with
     | Some iri -> ParseOk (PT_IRI iri) rest
     | None -> ParseErr "undefined prefix in pattern term")
  | Tok_A :: rest -> ParseOk (PT_IRI rdf_type_iri) rest
  | (Tok_BNODE b) :: rest -> ParseOk (PT_BNode b) rest
  | Tok_ANON :: rest -> ParseOk (PT_BNode "_:anon") rest
  | (Tok_STRING s) :: rest ->
    (match rest with
     | (Tok_LANGTAG tag) :: rest' ->
       ParseOk (PT_Literal (make_lang_literal s tag)) rest'
     | Tok_HATHAT :: (Tok_IRI dt) :: rest' ->
       ParseOk (PT_Literal (make_typed_literal s dt)) rest'
     | Tok_HATHAT :: (Tok_PNAME pn) :: rest' ->
       (match resolve_pname pn pm with
        | Some dt -> ParseOk (PT_Literal (make_typed_literal s dt)) rest'
        | None -> ParseErr "undefined prefix in datatype")
     | _ -> ParseOk (PT_Literal (make_plain_literal s)) rest)
  | (Tok_INTEGER n) :: rest -> ParseOk (PT_Literal (make_typed_literal n xsd_integer)) rest
  | (Tok_DECIMAL n) :: rest -> ParseOk (PT_Literal (make_typed_literal n xsd_decimal)) rest
  | (Tok_DOUBLE n) :: rest -> ParseOk (PT_Literal (make_typed_literal n xsd_double)) rest
  | Tok_TRUE :: rest -> ParseOk (PT_Literal (make_typed_literal "true" xsd_boolean)) rest
  | Tok_FALSE :: rest -> ParseOk (PT_Literal (make_typed_literal "false" xsd_boolean)) rest
  | _ -> ParseErr "unexpected token in pattern term"

(* Parse a pattern subject: variable, IRI, or bnode *)
let parse_pattern_subject (pm : prefix_map) (ts : token_stream)
  : parse_result pattern_subject =
  match ts with
  | (Tok_VAR v) :: rest -> ParseOk (PS_Var v) rest
  | (Tok_IRI i) :: rest -> ParseOk (PS_IRI i) rest
  | (Tok_PNAME pn) :: rest ->
    (match resolve_pname pn pm with
     | Some iri -> ParseOk (PS_IRI iri) rest
     | None -> ParseErr "undefined prefix in subject")
  | (Tok_BNODE b) :: rest -> ParseOk (PS_BNode b) rest
  | Tok_ANON :: rest -> ParseOk (PS_BNode "_:anon") rest
  | _ -> ParseErr "unexpected token in subject position"

(* --- Property Path Parser --- *)

let parse_path_primary (pm : prefix_map) (ts : token_stream)
  : parse_result property_path =
  match ts with
  | (Tok_IRI i) :: rest -> ParseOk (PP_IRI i) rest
  | (Tok_PNAME pn) :: rest ->
    (match resolve_pname pn pm with
     | Some iri -> ParseOk (PP_IRI iri) rest
     | None -> ParseErr "undefined prefix in property path")
  | Tok_A :: rest -> ParseOk (PP_IRI rdf_type_iri) rest
  | _ -> ParseErr "unexpected token in property path"

(* Apply postfix modifiers: *, +, ? *)
let parse_path_postfix (pp : property_path) (ts : token_stream)
  : (property_path & token_stream) =
  match ts with
  | Tok_STAR :: rest -> (PP_ZeroOrMore pp, rest)
  | Tok_PLUS :: rest -> (PP_OneOrMore pp, rest)
  | Tok_QMARK :: rest -> (PP_ZeroOrOne pp, rest)
  | _ -> (pp, ts)

(* Parse a path element with optional inverse *)
let parse_path_elt (pm : prefix_map) (ts : token_stream)
  : parse_result property_path =
  match ts with
  | Tok_CARET :: rest ->
    (match parse_path_primary pm rest with
     | ParseOk pp rest' ->
       let (pp', rest'') = parse_path_postfix pp rest' in
       ParseOk (PP_Inverse pp') rest''
     | ParseErr msg -> ParseErr msg)
  | _ ->
    (match parse_path_primary pm ts with
     | ParseOk pp rest ->
       let (pp', rest') = parse_path_postfix pp rest in
       ParseOk pp' rest'
     | ParseErr msg -> ParseErr msg)

(* Parse path sequence: p1 / p2 / p3 *)
let rec parse_path_seq_tail (pm : prefix_map) (left : property_path) (ts : token_stream)
  : parse_result property_path =
  match ts with
  | Tok_SLASH :: rest ->
    (match parse_path_elt pm rest with
     | ParseOk right rest' -> parse_path_seq_tail pm (PP_Sequence left right) rest'
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseOk left ts

let parse_path_sequence (pm : prefix_map) (ts : token_stream)
  : parse_result property_path =
  match parse_path_elt pm ts with
  | ParseOk left rest -> parse_path_seq_tail pm left rest
  | ParseErr msg -> ParseErr msg

(* Parse path alternative: p1 | p2 | p3 *)
let rec parse_path_alt_tail (pm : prefix_map) (left : property_path) (ts : token_stream)
  : parse_result property_path =
  match ts with
  | Tok_PIPE :: rest ->
    (match parse_path_sequence pm rest with
     | ParseOk right rest' -> parse_path_alt_tail pm (PP_Alternative left right) rest'
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseOk left ts

let parse_path (pm : prefix_map) (ts : token_stream) : parse_result property_path =
  match parse_path_sequence pm ts with
  | ParseOk left rest -> parse_path_alt_tail pm left rest
  | ParseErr msg -> ParseErr msg

(* --- Verb / Predicate Parsing --- *)

(* A verb in a triple pattern is either a simple IRI/var or a property path.
   We try to parse as a path; if it's just a simple IRI, we'll use it directly. *)
let is_path_token (t : token) : bool =
  match t with
  | Tok_STAR | Tok_SLASH | Tok_PIPE | Tok_CARET | Tok_PLUS | Tok_QMARK -> true
  | _ -> false

(* --- Property List / Triple Pattern Parsing --- *)

(* Parse object list: comma-separated pattern terms *)
let rec parse_object_list (pm : prefix_map) (ts : token_stream) (subj : pattern_subject)
  (pred : pattern_term) (acc : list triple_pattern) (paths : list group_graph_pattern)
  : (list triple_pattern & list group_graph_pattern & token_stream) =
  match parse_pattern_term pm ts with
  | ParseOk obj rest ->
    let tp : triple_pattern = { tp_s = subj; tp_p = pred; tp_o = obj } in
    (match rest with
     | Tok_COMMA :: rest' ->
       parse_object_list pm rest' subj pred (tp :: acc) paths
     | _ -> (List.Tot.rev (tp :: acc), paths, rest))
  | ParseErr _ -> (List.Tot.rev acc, paths, ts)

(* Parse predicate-object list for a given subject *)
let rec parse_property_list (pm : prefix_map) (ts : token_stream) (subj : pattern_subject)
  (triples : list triple_pattern) (paths : list group_graph_pattern)
  : (list triple_pattern & list group_graph_pattern & token_stream) =
  (* Try to parse a verb *)
  match ts with
  | (Tok_VAR v) :: rest ->
    (* Simple predicate: variable *)
    let (objs, paths', rest') = parse_object_list pm rest subj (PT_Var v) [] paths in
    let all_triples = List.Tot.append triples objs in
    (match rest' with
     | Tok_SEMI :: rest'' -> parse_property_list pm rest'' subj all_triples paths'
     | _ -> (all_triples, paths', rest'))
  | Tok_A :: rest ->
    let (objs, paths', rest') = parse_object_list pm rest subj (PT_IRI rdf_type_iri) [] paths in
    let all_triples = List.Tot.append triples objs in
    (match rest' with
     | Tok_SEMI :: rest'' -> parse_property_list pm rest'' subj all_triples paths'
     | _ -> (all_triples, paths', rest'))
  | (Tok_IRI i) :: rest ->
    (* Check if this is a property path or simple predicate *)
    if is_path_token (parse_peek rest) then
      (* Try property path starting with this IRI *)
      (match parse_path pm ts with
       | ParseOk pp rest' ->
         (* Parse object *)
         (match parse_pattern_term pm rest' with
          | ParseOk obj rest'' ->
            let pp_ggp = GP_PropertyPath subj pp obj in
            let paths' = pp_ggp :: paths in
            (match rest'' with
             | Tok_SEMI :: rest''' -> parse_property_list pm rest''' subj triples paths'
             | _ -> (triples, paths', rest''))
          | ParseErr _ -> (triples, paths, rest'))
       | ParseErr _ -> (triples, paths, ts))
    else
      let (objs, paths', rest') = parse_object_list pm rest subj (PT_IRI i) [] paths in
      let all_triples = List.Tot.append triples objs in
      (match rest' with
       | Tok_SEMI :: rest'' -> parse_property_list pm rest'' subj all_triples paths'
       | _ -> (all_triples, paths', rest'))
  | (Tok_PNAME pn) :: rest ->
    (match resolve_pname pn pm with
     | Some iri ->
       if is_path_token (parse_peek rest) then
         (match parse_path pm ts with
          | ParseOk pp rest' ->
            (match parse_pattern_term pm rest' with
             | ParseOk obj rest'' ->
               let pp_ggp = GP_PropertyPath subj pp obj in
               (match rest'' with
                | Tok_SEMI :: rest''' -> parse_property_list pm rest''' subj triples (pp_ggp :: paths)
                | _ -> (triples, pp_ggp :: paths, rest''))
             | ParseErr _ -> (triples, paths, rest'))
          | ParseErr _ -> (triples, paths, ts))
       else
         let (objs, paths', rest') = parse_object_list pm rest subj (PT_IRI iri) [] paths in
         let all_triples = List.Tot.append triples objs in
         (match rest' with
          | Tok_SEMI :: rest'' -> parse_property_list pm rest'' subj all_triples paths'
          | _ -> (all_triples, paths', rest'))
     | None -> (triples, paths, ts))
  | _ -> (triples, paths, ts)

(* --- Inline Data (VALUES) Parsing --- *)

(* Parse a single RDF term in a VALUES binding *)
let parse_values_term (pm : prefix_map) (ts : token_stream)
  : parse_result (option rdf_term) =
  match ts with
  | Tok_UNDEF :: rest -> ParseOk None rest
  | (Tok_IRI i) :: rest -> ParseOk (Some (T_IRI i)) rest
  | (Tok_PNAME pn) :: rest ->
    (match resolve_pname pn pm with
     | Some iri -> ParseOk (Some (T_IRI iri)) rest
     | None -> ParseErr "undefined prefix in VALUES")
  | (Tok_BNODE b) :: rest -> ParseOk (Some (T_BNode b)) rest
  | (Tok_STRING s) :: rest ->
    let lit = match rest with
      | (Tok_LANGTAG tag) :: rest' ->
        ParseOk (Some (T_Literal (make_lang_literal s tag))) rest'
      | Tok_HATHAT :: (Tok_IRI dt) :: rest' ->
        ParseOk (Some (T_Literal (make_typed_literal s dt))) rest'
      | Tok_HATHAT :: (Tok_PNAME pn) :: rest' ->
        (match resolve_pname pn pm with
         | Some dt -> ParseOk (Some (T_Literal (make_typed_literal s dt))) rest'
         | None -> ParseErr "undefined prefix in VALUES literal")
      | _ -> ParseOk (Some (T_Literal (make_plain_literal s))) rest
    in lit
  | (Tok_INTEGER n) :: rest ->
    ParseOk (Some (T_Literal (make_typed_literal n xsd_integer))) rest
  | _ -> ParseErr "unexpected token in VALUES data"

(* Parse a row of VALUES data: (term term ...) or just term for single-var *)
let rec parse_values_row_multi (pm : prefix_map) (ts : token_stream)
  (vars : list var_name) (acc : list (option rdf_term))
  : parse_result (list (option rdf_term)) =
  match ts with
  | Tok_RPAREN :: rest -> ParseOk (List.Tot.rev acc) rest
  | _ ->
    (match parse_values_term pm ts with
     | ParseOk term rest -> parse_values_row_multi pm rest vars (term :: acc)
     | ParseErr msg -> ParseErr msg)

(* Parse VALUES clause: VALUES ?var { val1 val2 } or VALUES (?v1 ?v2) { (v1 v2) ... } *)
let parse_inline_data (pm : prefix_map) (ts : token_stream)
  : parse_result (list var_name & list (list (option rdf_term))) =
  match ts with
  (* Single variable form: VALUES ?x { v1 v2 ... } *)
  | (Tok_VAR v) :: Tok_LBRACE :: rest ->
    let rec parse_single_vals (ts : token_stream) (acc : list (list (option rdf_term)))
      : parse_result (list var_name & list (list (option rdf_term))) =
      match ts with
      | Tok_RBRACE :: rest -> ParseOk ([v], List.Tot.rev acc) rest
      | _ ->
        (match parse_values_term pm ts with
         | ParseOk term rest -> parse_single_vals rest ([term] :: acc)
         | ParseErr msg -> ParseErr msg)
    in parse_single_vals rest []
  (* Multi-variable form: VALUES (?x ?y) { (v1 v2) ... } *)
  | Tok_LPAREN :: rest ->
    let rec parse_var_list (ts : token_stream) (acc : list var_name)
      : parse_result (list var_name) =
      match ts with
      | Tok_RPAREN :: rest -> ParseOk (List.Tot.rev acc) rest
      | (Tok_VAR v) :: rest -> parse_var_list rest (v :: acc)
      | _ -> ParseErr "expected variable or ) in VALUES variable list"
    in
    (match parse_var_list rest [] with
     | ParseOk vars rest' ->
       (match rest' with
        | Tok_LBRACE :: rest'' ->
          let rec parse_multi_rows (ts : token_stream) (acc : list (list (option rdf_term)))
            : parse_result (list var_name & list (list (option rdf_term))) =
            match ts with
            | Tok_RBRACE :: rest -> ParseOk (vars, List.Tot.rev acc) rest
            | Tok_LPAREN :: rest ->
              (match parse_values_row_multi pm rest vars [] with
               | ParseOk row rest' -> parse_multi_rows rest' (row :: acc)
               | ParseErr msg -> ParseErr msg)
            | _ -> ParseErr "expected ( or } in VALUES data"
          in parse_multi_rows rest'' []
        | _ -> ParseErr "expected { after VALUES variables")
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseErr "expected variable or ( after VALUES"

(* --- Group Graph Pattern Implementation --- *)

(* Parse the contents of a GroupGraphPattern: TriplesBlock interleaved with
   GraphPatternNotTriples (OPTIONAL, UNION, FILTER, BIND, VALUES, etc.) *)
let rec parse_ggp_contents (pm : prefix_map) (fuel : nat) (ts : token_stream)
  (current : group_graph_pattern) (filters : list expr)
  : parse_result group_graph_pattern =
  if fuel = 0 then ParseErr "recursion depth exceeded"
  else
  match ts with
  | Tok_RBRACE :: _ -> (* Don't consume } — let caller handle it *)
    let result = List.Tot.fold_left (fun g f -> GP_Filter f g) current filters in
    ParseOk result ts
  | Tok_EOF :: _ ->
    let result = List.Tot.fold_left (fun g f -> GP_Filter f g) current filters in
    ParseOk result ts
  | [] ->
    let result = List.Tot.fold_left (fun g f -> GP_Filter f g) current filters in
    ParseOk result ts

  (* OPTIONAL { ... } *)
  | Tok_OPTIONAL :: rest ->
    (match parse_group_graph_pattern pm (fuel - 1) rest with
     | ParseOk opt_ggp rest' ->
       let joined = GP_LeftJoin current opt_ggp (E_BoolLit true) in
       parse_ggp_contents pm (fuel - 1) rest' joined filters
     | ParseErr msg -> ParseErr msg)

  (* UNION — parse right side and combine *)
  | Tok_UNION :: rest ->
    (match parse_group_graph_pattern pm (fuel - 1) rest with
     | ParseOk union_ggp rest' ->
       let joined = GP_Union current union_ggp in
       parse_ggp_contents pm (fuel - 1) rest' joined filters
     | ParseErr msg -> ParseErr msg)

  (* MINUS { ... } *)
  | Tok_MINUS_KW :: rest ->
    (match parse_group_graph_pattern pm (fuel - 1) rest with
     | ParseOk minus_ggp rest' ->
       let joined = GP_Minus current minus_ggp in
       parse_ggp_contents pm (fuel - 1) rest' joined filters
     | ParseErr msg -> ParseErr msg)

  (* FILTER (expr) or FILTER expr *)
  | Tok_FILTER :: rest ->
    let rest' = match rest with
      | Tok_LPAREN :: _ -> rest
      | _ -> rest in
    (match parse_expr pm rest' with
     | ParseOk e rest'' ->
       parse_ggp_contents pm (fuel - 1) rest'' current (e :: filters)
     | ParseErr msg -> ParseErr msg)

  (* BIND (expr AS ?var) *)
  | Tok_BIND :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseOk e rest' ->
       (match rest' with
        | Tok_AS :: (Tok_VAR v) :: Tok_RPAREN :: rest'' ->
          let bound = GP_Bind e v current in
          parse_ggp_contents pm (fuel - 1) rest'' bound filters
        | _ -> ParseErr "expected AS ?var ) after BIND expression")
     | ParseErr msg -> ParseErr msg)

  (* VALUES *)
  | Tok_VALUES :: rest ->
    (match parse_inline_data pm rest with
     | ParseOk (vars, rows) rest' ->
       let vals = GP_Values vars rows in
       let joined = if is_gp_empty current then vals else GP_Join current vals in
       parse_ggp_contents pm (fuel - 1) rest' joined filters
     | ParseErr msg -> ParseErr msg)

  (* GRAPH term { ... } *)
  | Tok_GRAPH :: rest ->
    (match parse_pattern_term pm rest with
     | ParseOk gt rest' ->
       (match parse_group_graph_pattern pm (fuel - 1) rest' with
        | ParseOk graph_ggp rest'' ->
          let g = GP_Graph gt graph_ggp in
          let joined = if is_gp_empty current then g else GP_Join current g in
          parse_ggp_contents pm (fuel - 1) rest'' joined filters
        | ParseErr msg -> ParseErr msg)
     | ParseErr msg -> ParseErr msg)

  (* SERVICE [SILENT] <iri> { ... } *)
  | Tok_SERVICE :: rest ->
    let (silent, rest') = match rest with
      | Tok_SILENT :: r -> (true, r)
      | _ -> (false, rest) in
    (match rest' with
     | (Tok_IRI iri) :: rest'' ->
       (match parse_group_graph_pattern pm (fuel - 1) rest'' with
        | ParseOk svc_ggp rest''' ->
          let s = GP_Service iri svc_ggp silent in
          let joined = if is_gp_empty current then s else GP_Join current s in
          parse_ggp_contents pm (fuel - 1) rest''' joined filters
        | ParseErr msg -> ParseErr msg)
     | (Tok_PNAME pn) :: rest'' ->
       (match resolve_pname pn pm with
        | Some iri ->
          (match parse_group_graph_pattern pm (fuel - 1) rest'' with
           | ParseOk svc_ggp rest''' ->
             let s = GP_Service iri svc_ggp silent in
             let joined = if is_gp_empty current then s else GP_Join current s in
             parse_ggp_contents pm (fuel - 1) rest''' joined filters
           | ParseErr msg -> ParseErr msg)
        | None -> ParseErr "undefined prefix in SERVICE")
     | (Tok_VAR _) :: rest'' ->
       (* SERVICE with variable endpoint *)
       (match parse_group_graph_pattern pm (fuel - 1) rest'' with
        | ParseOk svc_ggp rest''' ->
          let joined = if is_gp_empty current then svc_ggp else GP_Join current svc_ggp in
          parse_ggp_contents pm (fuel - 1) rest''' joined filters
        | ParseErr msg -> ParseErr msg)
     | _ -> ParseErr "expected IRI after SERVICE")

  (* Sub-SELECT: { SELECT ... } *)
  | Tok_SELECT :: _ ->
    (match parse_select_query pm (fuel - 1) ts with
     | ParseOk sub_q rest' ->
       let sub = GP_SubSelect sub_q in
       let joined = if is_gp_empty current then sub else GP_Join current sub in
       parse_ggp_contents pm (fuel - 1) rest' joined filters
     | ParseErr msg -> ParseErr msg)

  (* Nested { ... } *)
  | Tok_LBRACE :: _ ->
    (match parse_group_graph_pattern pm (fuel - 1) ts with
     | ParseOk nested rest' ->
       let joined = if is_gp_empty current then nested else GP_Join current nested in
       parse_ggp_contents pm (fuel - 1) rest' joined filters
     | ParseErr msg -> ParseErr msg)

  (* DOT separator — skip and continue *)
  | Tok_DOT :: rest ->
    parse_ggp_contents pm (fuel - 1) rest current filters

  (* Triple patterns: subject predicate object . *)
  | _ ->
    (match parse_pattern_subject pm ts with
     | ParseOk subj rest ->
       let (triples, paths, rest') = parse_property_list pm rest subj [] [] in
       let bgp = if List.Tot.length triples > 0 then GP_BGP triples else GP_Empty in
       let pattern = List.Tot.fold_left (fun g p -> GP_Join g p) bgp paths in
       let joined = gp_join current pattern in
       (* Skip optional trailing dot *)
       let rest'' = match rest' with | Tok_DOT :: r -> r | _ -> rest' in
       parse_ggp_contents pm (fuel - 1) rest'' joined filters
     | ParseErr _ ->
       (* Not a triple pattern — we're done with this group *)
       let result = List.Tot.fold_left (fun g f -> GP_Filter f g) current filters in
       ParseOk result ts)

(* Parse GroupGraphPattern: { contents } *)
let parse_ggp_impl (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : parse_result group_graph_pattern =
  match ts with
  | Tok_LBRACE :: rest ->
    (match parse_ggp_contents pm fuel rest GP_Empty [] with
     | ParseOk ggp rest' ->
       (match rest' with
        | Tok_RBRACE :: rest'' -> ParseOk ggp rest''
        | _ -> ParseErr "expected } to close group graph pattern")
     | ParseErr msg -> ParseErr msg)
  | _ -> ParseErr "expected { to open group graph pattern"

(* --- Query-Level Parsing --- *)

// Parse SELECT clause: SELECT [DISTINCT|REDUCED] (*/vars/exprs)
let rec parse_select_items (pm : prefix_map) (ts : token_stream) (acc : list select_item)
  : parse_result select_clause =
  match ts with
  | (Tok_VAR v) :: rest -> parse_select_items pm rest (SI_Var v :: acc)
  | Tok_LPAREN :: rest ->
    (* (expr AS ?var) *)
    (match parse_expr pm rest with
     | ParseOk e rest' ->
       (match rest' with
        | Tok_AS :: (Tok_VAR v) :: Tok_RPAREN :: rest'' ->
          parse_select_items pm rest'' (SI_Expr e v :: acc)
        | _ -> ParseErr "expected AS ?var ) in SELECT expression")
     | ParseErr msg -> ParseErr msg)
  | _ ->
    if List.Tot.length acc = 0 then ParseErr "expected variable or expression in SELECT"
    else ParseOk (Select_Vars (List.Tot.rev acc)) ts

let parse_select_clause (pm : prefix_map) (ts : token_stream)
  : parse_result (select_clause & bool & bool) =
  let (distinct, reduced, rest) = match ts with
    | Tok_DISTINCT :: r -> (true, false, r)
    | Tok_REDUCED :: r -> (false, true, r)
    | _ -> (false, false, ts) in
  match rest with
  | Tok_STAR :: rest' -> ParseOk (Select_All, distinct, reduced) rest'
  | _ ->
    (match parse_select_items pm rest [] with
     | ParseOk sc rest' -> ParseOk (sc, distinct, reduced) rest'
     | ParseErr msg -> ParseErr msg)

(* Parse ORDER BY clause *)
let rec parse_order_conditions (pm : prefix_map) (ts : token_stream) (acc : list order_condition)
  : (list order_condition & token_stream) =
  match ts with
  | Tok_ASC :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> parse_order_conditions pm rest'' (OC_Asc e :: acc)
        | _ -> (List.Tot.rev acc, ts))
     | _ -> (List.Tot.rev acc, ts))
  | Tok_DESC :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> parse_order_conditions pm rest'' (OC_Desc e :: acc)
        | _ -> (List.Tot.rev acc, ts))
     | _ -> (List.Tot.rev acc, ts))
  | (Tok_VAR v) :: rest ->
    parse_order_conditions pm rest (OC_Asc (E_Var v) :: acc)
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> parse_order_conditions pm rest'' (OC_Asc e :: acc)
        | _ -> (List.Tot.rev acc, ts))
     | _ -> (List.Tot.rev acc, ts))
  | _ ->
    (* Try parsing a bare expression *)
    if List.Tot.length acc = 0 then
      (match parse_expr pm ts with
       | ParseOk e rest -> parse_order_conditions pm rest (OC_Asc e :: acc)
       | _ -> (List.Tot.rev acc, ts))
    else (List.Tot.rev acc, ts)

(* Parse GROUP BY clause *)
let rec parse_group_conditions (pm : prefix_map) (ts : token_stream) (acc : list group_condition)
  : (list group_condition & token_stream) =
  match ts with
  | (Tok_VAR v) :: rest ->
    parse_group_conditions pm rest (GC_Var v :: acc)
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseOk e rest' ->
       (match rest' with
        | Tok_AS :: (Tok_VAR v) :: Tok_RPAREN :: rest'' ->
          parse_group_conditions pm rest'' (GC_Expr e (Some v) :: acc)
        | Tok_RPAREN :: rest'' ->
          parse_group_conditions pm rest'' (GC_Expr e None :: acc)
        | _ -> (List.Tot.rev acc, ts))
     | _ -> (List.Tot.rev acc, ts))
  | _ ->
    if List.Tot.length acc = 0 then
      (* Try built-in call or expression *)
      (match parse_expr pm ts with
       | ParseOk e rest -> parse_group_conditions pm rest (GC_Expr e None :: acc)
       | _ -> (List.Tot.rev acc, ts))
    else (List.Tot.rev acc, ts)

(* Parse HAVING clause: list of constraint expressions *)
let rec parse_having_conditions (pm : prefix_map) (ts : token_stream) (acc : list expr)
  : (list expr & token_stream) =
  match ts with
  | Tok_LPAREN :: _ ->
    (match parse_expr pm ts with
     | ParseOk e rest -> parse_having_conditions pm rest (e :: acc)
     | _ -> (List.Tot.rev acc, ts))
  | _ ->
    if List.Tot.length acc = 0 then
      (match parse_expr pm ts with
       | ParseOk e rest -> parse_having_conditions pm rest (e :: acc)
       | _ -> (List.Tot.rev acc, ts))
    else (List.Tot.rev acc, ts)

(* Parse a CONSTRUCT template: list of triple patterns *)
let rec parse_construct_template (pm : prefix_map) (ts : token_stream)
  (acc : list triple_pattern) : parse_result (list triple_pattern) =
  match ts with
  | Tok_RBRACE :: rest -> ParseOk (List.Tot.rev acc) rest
  | _ ->
    (match parse_pattern_subject pm ts with
     | ParseOk subj rest ->
       let (triples, _, rest') = parse_property_list pm rest subj [] [] in
       let rest'' = match rest' with | Tok_DOT :: r -> r | _ -> rest' in
       parse_construct_template pm rest'' (List.Tot.append (List.Tot.rev triples) acc)
     | ParseErr msg -> ParseErr msg)

(* Parse a complete SELECT/ASK/CONSTRUCT/DESCRIBE query *)
let parse_query_impl (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : parse_result query =
  if fuel = 0 then ParseErr "recursion depth exceeded"
  else
  let default_modifier : solution_modifier = {
    sm_order_by = None; sm_distinct = false; sm_reduced = false;
    sm_offset = None; sm_limit = None
  } in
  match ts with
  | Tok_SELECT :: rest ->
    (* SELECT query *)
    (match parse_select_clause pm rest with
     | ParseOk (sc, distinct, reduced) rest' ->
       (* Optional WHERE keyword *)
       let rest'' = match rest' with | Tok_WHERE :: r -> r | _ -> rest' in
       (match parse_group_graph_pattern pm (fuel - 1) rest'' with
        | ParseOk ggp rest''' ->
          (* Solution modifiers *)
          let (group_by, rest4) = match rest''' with
            | Tok_GROUP :: Tok_BY :: r ->
              let (gc, r') = parse_group_conditions pm r [] in
              (Some gc, r')
            | _ -> (None, rest''') in
          let (having, rest5) = match rest4 with
            | Tok_HAVING :: r ->
              let (hc, r') = parse_having_conditions pm r [] in
              (Some hc, r')
            | _ -> (None, rest4) in
          let (order_by, rest6) = match rest5 with
            | Tok_ORDER :: Tok_BY :: r ->
              let (oc, r') = parse_order_conditions pm r [] in
              (Some oc, r')
            | _ -> (None, rest5) in
          let (limit, rest7) = match rest6 with
            | Tok_LIMIT :: (Tok_INTEGER n) :: r ->
              (match parse_int_string n with
               | Some i -> (Some i, r)
               | None -> (None, r))
            | _ -> (None, rest6) in
          let (offset, rest8) = match rest7 with
            | Tok_OFFSET :: (Tok_INTEGER n) :: r ->
              (match parse_int_string n with
               | Some i -> (Some i, r)
               | None -> (None, r))
            | _ -> (None, rest7) in
          (* Check for LIMIT after OFFSET (either order is valid) *)
          let (limit, rest9) = match rest8 with
            | Tok_LIMIT :: (Tok_INTEGER n) :: r ->
              if limit = None then
                (match parse_int_string n with
                 | Some i -> (Some i, r)
                 | None -> (None, r))
              else (limit, rest8)
            | _ -> (limit, rest8) in
          (* Post-query VALUES *)
          let (values, rest10) = match rest9 with
            | Tok_VALUES :: rest_v ->
              (match parse_inline_data pm rest_v with
               | ParseOk (vars, rows) rest' -> (Some [], rest')  (* TODO: convert to solution_sequence *)
               | ParseErr _ -> (None, rest9))
            | _ -> (None, rest9) in
          let modifier : solution_modifier = {
            sm_order_by = order_by;
            sm_distinct = distinct;
            sm_reduced = reduced;
            sm_offset = offset;
            sm_limit = limit;
          } in
          let q : query = {
            q_base = None;
            q_prefixes = pm;
            q_form = QF_Select sc;
            q_dataset = [];
            q_pattern = ggp;
            q_group_by = group_by;
            q_having = having;
            q_modifier = modifier;
            q_values = values;
          } in
          ParseOk q rest10
        | ParseErr msg -> ParseErr msg)
     | ParseErr msg -> ParseErr msg)

  | Tok_ASK :: rest ->
    let rest' = match rest with | Tok_WHERE :: r -> r | _ -> rest in
    (match parse_group_graph_pattern pm (fuel - 1) rest' with
     | ParseOk ggp rest'' ->
       let q : query = {
         q_base = None; q_prefixes = pm;
         q_form = QF_Ask; q_dataset = [];
         q_pattern = ggp; q_group_by = None; q_having = None;
         q_modifier = default_modifier; q_values = None;
       } in
       ParseOk q rest''
     | ParseErr msg -> ParseErr msg)

  | Tok_CONSTRUCT :: rest ->
    (match rest with
     | Tok_LBRACE :: rest' ->
       (match parse_construct_template pm rest' [] with
        | ParseOk template rest'' ->
          let rest''' = match rest'' with | Tok_WHERE :: r -> r | _ -> rest'' in
          (match parse_group_graph_pattern pm (fuel - 1) rest''' with
           | ParseOk ggp rest'''' ->
             let q : query = {
               q_base = None; q_prefixes = pm;
               q_form = QF_Construct template; q_dataset = [];
               q_pattern = ggp; q_group_by = None; q_having = None;
               q_modifier = default_modifier; q_values = None;
             } in
             ParseOk q rest''''
           | ParseErr msg -> ParseErr msg)
        | ParseErr msg -> ParseErr msg)
     | Tok_WHERE :: rest' ->
       (* CONSTRUCT WHERE { ... } shorthand *)
       (match parse_group_graph_pattern pm (fuel - 1) rest' with
        | ParseOk ggp rest'' ->
          let q : query = {
            q_base = None; q_prefixes = pm;
            q_form = QF_Construct []; q_dataset = [];
            q_pattern = ggp; q_group_by = None; q_having = None;
            q_modifier = default_modifier; q_values = None;
          } in
          ParseOk q rest''
        | ParseErr msg -> ParseErr msg)
     | _ -> ParseErr "expected { or WHERE after CONSTRUCT")

  | _ -> ParseErr "expected SELECT, ASK, or CONSTRUCT"

(* Integer parsing — reuse the function from SPARQL11.Algebra *)
let parse_int_string (s : string) : option int = parse_int_string s

(* --- Public Entry Point --- *)

(* Parse a SPARQL query string into a query AST.
   This is the main function that replaces sparql_parser.ml. *)
let parse_sparql (input : string) : parse_result query =
  let tokens = tokenize input in
  let (pm, base, tokens') = parse_prologue [] None tokens in
  parse_query_impl pm default_fuel tokens'

#pop-options
