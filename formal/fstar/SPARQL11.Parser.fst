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

(* Scan an IRI: input positioned after <, read chars until > *)
let rec scan_iri_loop (input : string) (p : pos) (acc : string)
  : Tot (string & pos) (decreases (String.length input - p)) =
  if at_end input p then (acc, p)
  else
    let c = peek_char input p in
    if char_code c = 0x3E (* > *) then (acc, p + 1)
    else scan_iri_loop input (p + 1) (acc ^ substring input p 1)

let scan_iri (input : string) (p : pos) : (string & pos) =
  scan_iri_loop input p ""

(* Scan a short string literal: input positioned at the opening quote *)
let rec scan_short_string_loop (input : string) (p : pos) (q_code : nat) (acc : string)
  : Tot (string & pos) (decreases (String.length input - p)) =
  if at_end input p then (acc, p)
  else
    let c = peek_char input p in
    if char_code c = q_code then (acc, p + 1)
    else if char_code c = 0x5C (* backslash *) then
      if at_end input (p + 1) then (acc, p + 1)
      else
        let esc = peek_char input (p + 1) in
        let esc_code = char_code esc in
        let (replacement, skip) =
          if esc_code = 0x74 (* t *) then ("\t", 2)
          else if esc_code = 0x6E (* n *) then ("\n", 2)
          else if esc_code = 0x72 (* r *) then ("\r", 2)
          else if esc_code = q_code then (substring input (p + 1) 1, 2)
          else if esc_code = 0x5C (* backslash *) then ("\\", 2)
          else (substring input (p + 1) 1, 2) in
        scan_short_string_loop input (p + skip) q_code (acc ^ replacement)
    else scan_short_string_loop input (p + 1) q_code (acc ^ substring input p 1)

(* Scan a long string literal: input positioned after the triple quote *)
let rec scan_long_string_loop (input : string) (p : pos) (q_code : nat) (acc : string)
  : Tot (string & pos) (decreases (String.length input - p)) =
  if at_end input p then (acc, p)
  else
    let c = peek_char input p in
    if char_code c = q_code
       && not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = q_code
       && not (at_end input (p + 2)) && char_code (peek_char input (p + 2)) = q_code
    then (acc, p + 3)
    else if char_code c = 0x5C (* backslash *) then
      if at_end input (p + 1) then (acc, p + 1)
      else
        let esc = peek_char input (p + 1) in
        let esc_code = char_code esc in
        let (replacement, skip) =
          if esc_code = 0x74 then ("\t", 2)
          else if esc_code = 0x6E then ("\n", 2)
          else if esc_code = 0x72 then ("\r", 2)
          else if esc_code = q_code then (substring input (p + 1) 1, 2)
          else if esc_code = 0x5C then ("\\", 2)
          else (substring input (p + 1) 1, 2) in
        scan_long_string_loop input (p + skip) q_code (acc ^ replacement)
    else scan_long_string_loop input (p + 1) q_code (acc ^ substring input p 1)

(* Scan a string literal starting at opening quote char *)
let scan_string (input : string) (p : pos) : (string & pos) =
  if at_end input p then ("", p)
  else
    let q = peek_char input p in
    let q_code = char_code q in
    (* Check for long string: three of the same quote *)
    if not (at_end input (p + 1)) && char_code (peek_char input (p + 1)) = q_code
       && not (at_end input (p + 2)) && char_code (peek_char input (p + 2)) = q_code
    then scan_long_string_loop input (p + 3) q_code ""
    else scan_short_string_loop input (p + 1) q_code ""

(* Scan a variable name: [a-zA-Z0-9_]+ *)
let rec scan_var_name_loop (input : string) (p : pos) (start : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else
    let c = peek_char input p in
    if is_alnum c || char_code c = 0x5F (* _ *)
    then scan_var_name_loop input (p + 1) start
    else p

let scan_var_name (input : string) (p : pos) : (string & pos) =
  let end_pos = scan_var_name_loop input p p in
  if end_pos > p then (substring input p (end_pos - p), end_pos)
  else ("", p)

(* Scan a blank node label: [a-zA-Z0-9_.-]+ with no trailing dots *)
let rec scan_bnode_loop (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else if is_pn_char (peek_char input p)
  then scan_bnode_loop input (p + 1)
  else p

let rec strip_trailing_dots (input : string) (p : pos) (start : pos)
  : Tot pos (decreases (p - start)) =
  if p <= start then start
  else if char_code (peek_char input (p - 1)) = 0x2E (* . *)
  then strip_trailing_dots input (p - 1) start
  else p

let scan_bnode_label (input : string) (p : pos) : (string & pos) =
  let end_pos = scan_bnode_loop input p in
  let end_pos = strip_trailing_dots input end_pos p in
  (substring input p (end_pos - p), end_pos)

(* Scan a language tag: [a-zA-Z0-9-]+ *)
let rec scan_langtag_loop (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else
    let c = peek_char input p in
    if is_alnum c || char_code c = 0x2D (* - *)
    then scan_langtag_loop input (p + 1)
    else p

let scan_langtag (input : string) (p : pos) : (string & pos) =
  let end_pos = scan_langtag_loop input p in
  (substring input p (end_pos - p), end_pos)

(* Scan a prefixed name local part: [a-zA-Z0-9_:.-]+ with PN_LOCAL_ESC handling *)
let rec scan_pname_local_loop (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else
    let c = peek_char input p in
    if is_pn_char c || char_code c = 0x3A (* : *) || char_code c = 0x25 (* % *)
    then scan_pname_local_loop input (p + 1)
    else if char_code c = 0x5C (* backslash *) then
      if at_end input (p + 1) then p
      else if is_pn_local_esc (peek_char input (p + 1))
      then scan_pname_local_loop input (p + 2)
      else p
    else p

(* Scan prefix part: letters/digits/dots *)
let rec scan_prefix_part (input : string) (p : pos)
  : Tot pos (decreases (String.length input - p)) =
  if at_end input p then p
  else if is_pn_char (peek_char input p)
  then scan_prefix_part input (p + 1)
  else p

(* Match a keyword string against known SPARQL keywords *)
let keyword_to_token (word : string) : token =
  let upper = string_upper word in
  if upper = "SELECT" then Tok_SELECT
  else if upper = "ASK" then Tok_ASK
  else if upper = "CONSTRUCT" then Tok_CONSTRUCT
  else if upper = "DESCRIBE" then Tok_DESCRIBE
  else if upper = "WHERE" then Tok_WHERE
  else if upper = "PREFIX" then Tok_PREFIX
  else if upper = "BASE" then Tok_BASE
  else if upper = "OPTIONAL" then Tok_OPTIONAL
  else if upper = "UNION" then Tok_UNION
  else if upper = "MINUS" then Tok_MINUS_KW
  else if upper = "FILTER" then Tok_FILTER
  else if upper = "BIND" then Tok_BIND
  else if upper = "VALUES" then Tok_VALUES
  else if upper = "GRAPH" then Tok_GRAPH
  else if upper = "SERVICE" then Tok_SERVICE
  else if upper = "SILENT" then Tok_SILENT
  else if upper = "EXISTS" then Tok_EXISTS
  else if upper = "NOT" then Tok_NOT
  else if upper = "AS" then Tok_AS
  else if upper = "DISTINCT" then Tok_DISTINCT
  else if upper = "REDUCED" then Tok_REDUCED
  else if upper = "ORDER" then Tok_ORDER
  else if upper = "BY" then Tok_BY
  else if upper = "ASC" then Tok_ASC
  else if upper = "DESC" then Tok_DESC
  else if upper = "GROUP" then Tok_GROUP
  else if upper = "HAVING" then Tok_HAVING
  else if upper = "LIMIT" then Tok_LIMIT
  else if upper = "OFFSET" then Tok_OFFSET
  else if upper = "IN" then Tok_IN
  else if upper = "TRUE" then Tok_TRUE
  else if upper = "FALSE" then Tok_FALSE
  else if upper = "UNDEF" then Tok_UNDEF
  else if upper = "A" then Tok_A
  else if upper = "STR" then Tok_STR
  else if upper = "LANG" then Tok_LANG
  else if upper = "LANGMATCHES" then Tok_LANGMATCHES
  else if upper = "DATATYPE" then Tok_DATATYPE
  else if upper = "BOUND" then Tok_BOUND
  else if upper = "IF" then Tok_IF
  else if upper = "IRI" then Tok_IRI_KW
  else if upper = "URI" then Tok_IRI_KW
  else if upper = "BNODE" then Tok_BNODE_KW
  else if upper = "RAND" then Tok_RAND
  else if upper = "ABS" then Tok_ABS
  else if upper = "CEIL" then Tok_CEIL
  else if upper = "FLOOR" then Tok_FLOOR
  else if upper = "ROUND" then Tok_ROUND
  else if upper = "CONCAT" then Tok_CONCAT
  else if upper = "STRLEN" then Tok_STRLEN
  else if upper = "UCASE" then Tok_UCASE
  else if upper = "LCASE" then Tok_LCASE
  else if upper = "ENCODE_FOR_URI" then Tok_ENCODE_FOR_URI
  else if upper = "CONTAINS" then Tok_CONTAINS
  else if upper = "STRSTARTS" then Tok_STRSTARTS
  else if upper = "STRENDS" then Tok_STRENDS
  else if upper = "STRBEFORE" then Tok_STRBEFORE
  else if upper = "STRAFTER" then Tok_STRAFTER
  else if upper = "REPLACE" then Tok_REPLACE
  else if upper = "REGEX" then Tok_REGEX
  else if upper = "SUBSTR" then Tok_SUBSTR
  else if upper = "ISIRI" then Tok_ISIRI
  else if upper = "ISURI" then Tok_ISIRI
  else if upper = "ISBLANK" then Tok_ISBLANK
  else if upper = "ISLITERAL" then Tok_ISLITERAL
  else if upper = "ISNUMERIC" then Tok_ISNUMERIC
  else if upper = "SAMETERM" then Tok_SAMETERM
  else if upper = "STRDT" then Tok_STRDT
  else if upper = "STRLANG" then Tok_STRLANG
  else if upper = "COUNT" then Tok_COUNT
  else if upper = "SUM" then Tok_SUM
  else if upper = "MIN" then Tok_MIN_KW
  else if upper = "MAX" then Tok_MAX_KW
  else if upper = "AVG" then Tok_AVG
  else if upper = "GROUP_CONCAT" then Tok_GROUP_CONCAT
  else if upper = "SAMPLE" then Tok_SAMPLE
  else if upper = "SEPARATOR" then Tok_SEPARATOR
  else if upper = "COALESCE" then Tok_COALESCE
  else if upper = "NOW" then Tok_NOW
  else if upper = "UUID" then Tok_UUID
  else if upper = "STRUUID" then Tok_STRUUID
  else if upper = "YEAR" then Tok_YEAR
  else if upper = "MONTH" then Tok_MONTH
  else if upper = "DAY" then Tok_DAY
  else if upper = "HOURS" then Tok_HOURS
  else if upper = "MINUTES" then Tok_MINUTES
  else if upper = "SECONDS" then Tok_SECONDS
  else if upper = "TIMEZONE" then Tok_TIMEZONE
  else if upper = "TZ" then Tok_TZ
  else if upper = "MD5" then Tok_MD5
  else if upper = "SHA1" then Tok_SHA1
  else if upper = "SHA256" then Tok_SHA256
  else if upper = "SHA384" then Tok_SHA384
  else if upper = "SHA512" then Tok_SHA512
  else Tok_PNAME word

(* Scan a prefixed name or keyword starting at p *)
let scan_pname_or_keyword (input : string) (p : pos) : lex_result =
  let end_prefix = scan_prefix_part input p in
  if not (at_end input end_prefix) && char_code (peek_char input end_prefix) = 0x3A (* : *)
  then
    (* It's a prefixed name: prefix:local *)
    let local_start = end_prefix + 1 in
    let end_local = scan_pname_local_loop input local_start in
    let end_local = strip_trailing_dots input end_local local_start in
    let pname = substring input p (end_local - p) in
    (Tok_PNAME pname, end_local)
  else
    (* It's a keyword or bare name *)
    let word = substring input p (end_prefix - p) in
    (keyword_to_token word, end_prefix)

(* Scan a number: integer, decimal, or double *)
let scan_number (input : string) (p : pos) : lex_result =
  let start = p in
  (* Skip optional sign *)
  let p1 = if not (at_end input p)
            && (char_code (peek_char input p) = 0x2B || char_code (peek_char input p) = 0x2D)
           then p + 1 else p in
  (* Scan integer digits *)
  let rec scan_digits (p : pos) : Tot pos (decreases (String.length input - p)) =
    if at_end input p then p
    else if is_digit (peek_char input p) then scan_digits (p + 1)
    else p in
  let p2 = scan_digits p1 in
  (* Check for decimal point followed by digit *)
  let (has_dot, p3) =
    if not (at_end input p2) && char_code (peek_char input p2) = 0x2E
       && not (at_end input (p2 + 1)) && is_digit (peek_char input (p2 + 1))
    then (true, scan_digits (p2 + 1))
    else (false, p2) in
  (* Check for exponent *)
  let (has_exp, p4) =
    if not (at_end input p3)
       && (char_code (peek_char input p3) = 0x65 || char_code (peek_char input p3) = 0x45)
    then
      let pe = p3 + 1 in
      let pe2 = if not (at_end input pe)
                   && (char_code (peek_char input pe) = 0x2B || char_code (peek_char input pe) = 0x2D)
                then pe + 1 else pe in
      (true, scan_digits pe2)
    else (false, p3) in
  let text = substring input start (p4 - start) in
  if has_exp then (Tok_DOUBLE text, p4)
  else if has_dot then (Tok_DECIMAL text, p4)
  else (Tok_INTEGER text, p4)

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

(* Tokenize entire input into a token list *)
let rec tokenize_loop (input : string) (p : pos) (acc : list token)
  : Tot (list token) (decreases (String.length input - p + 1)) =
  let (tok, p') = next_token input p in
  if Tok_EOF? tok then List.Tot.rev (Tok_EOF :: acc)
  else if p' > p then tokenize_loop input p' (tok :: acc)
  else List.Tot.rev (Tok_EOF :: acc)  (* safety: avoid infinite loop *)

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

(* Token equality — decidable *)
assume val token_eq : token -> token -> bool

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
(* Find position of first colon in string *)
let rec find_colon (input : string) (p : pos)
  : Tot (option pos) (decreases (String.length input - p)) =
  if at_end input p then None
  else if char_code (peek_char input p) = 0x3A (* : *) then Some p
  else find_colon input (p + 1)

let split_pname (pn : string) : (string & string) =
  match find_colon pn 0 with
  | Some i ->
    let prefix = substring pn 0 i in
    let local = substring pn (i + 1) (String.length pn - i - 1) in
    (prefix, local)
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

(* ================================================================== *)
(* Helper: resolve an IRI or prefixed name token to a wf_iri string  *)
(* ================================================================== *)

let resolve_iri_token (tok : token) (pm : prefix_map) : option string =
  match tok with
  | Tok_IRI i -> Some i
  | Tok_PNAME pn -> resolve_pname pn pm
  | Tok_A -> Some "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
  | _ -> None

(* Helper: parse an IRI from the token stream *)
let parse_iri_from_stream (pm : prefix_map) (ts : token_stream)
  : parse_result string =
  match ts with
  | Tok_IRI i :: rest -> ParseOk i rest
  | Tok_PNAME pn :: rest ->
    (match resolve_pname pn pm with
     | Some iri -> ParseOk iri rest
     | None -> ParseErr "undefined prefix")
  | Tok_A :: rest -> ParseOk "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" rest
  | _ -> ParseErr "expected IRI"

(* bnode counter — use assume val for mutable state *)
assume val fresh_bnode_id : unit -> string

(* ================================================================== *)
(* Mutually recursive parser functions                                 *)
(*                                                                     *)
(* parse_expr            — SPARQL expression with operator precedence  *)
(* parse_group_graph_pattern — { ... } graph pattern blocks            *)
(* parse_select_query    — SELECT query with modifiers                 *)
(*                                                                     *)
(* Termination: fuel parameter decreases on recursive calls.           *)
(* Each function also consumes tokens, but fuel provides the           *)
(* structural termination argument F* needs.                           *)
(* ================================================================== *)

(* Result type for verb parsing — defined before mutual recursion block *)
noeq type verb_result =
  | VR_Simple : pattern_term -> verb_result
  | VR_Path   : property_path -> verb_result

(* Parse integer/nat from string — delegated to OCaml extraction *)
assume val parse_int_value : string -> int
assume val parse_nat_value : string -> nat

(* zip two lists together *)
let rec list_zip (#a #b : Type) (l1 : list a) (l2 : list b) : Tot (list (a & b)) (decreases l1) =
  match l1, l2 with
  | [], _ -> []
  | _, [] -> []
  | x :: xs, y :: ys -> (x, y) :: list_zip xs ys

let rec parse_expr (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  parse_or_expr pm ts

and parse_or_expr (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match parse_and_expr pm ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk left rest ->
    parse_or_expr_loop pm left rest

and parse_or_expr_loop (pm : prefix_map) (left : expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_OR :: rest ->
    (match parse_and_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk right rest' -> parse_or_expr_loop pm (E_Or left right) rest')
  | _ -> ParseOk left ts

and parse_and_expr (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match parse_compare_expr pm ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk left rest ->
    parse_and_expr_loop pm left rest

and parse_and_expr_loop (pm : prefix_map) (left : expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_AND :: rest ->
    (match parse_compare_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk right rest' -> parse_and_expr_loop pm (E_And left right) rest')
  | _ -> ParseOk left ts

and parse_compare_expr (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match parse_additive_expr pm ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk left rest ->
    (match rest with
     | Tok_EQ :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk right rest'' -> ParseOk (E_Compare CmpEq left right) rest'')
     | Tok_NE :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk right rest'' -> ParseOk (E_Compare CmpNe left right) rest'')
     | Tok_LT :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk right rest'' -> ParseOk (E_Compare CmpLt left right) rest'')
     | Tok_GT :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk right rest'' -> ParseOk (E_Compare CmpGt left right) rest'')
     | Tok_LE :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk right rest'' -> ParseOk (E_Compare CmpLe left right) rest'')
     | Tok_GE :: rest' ->
       (match parse_additive_expr pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk right rest'' -> ParseOk (E_Compare CmpGe left right) rest'')
     | Tok_IN :: Tok_LPAREN :: rest' ->
       (match parse_expr_list pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk args rest'' ->
          (match rest'' with
           | Tok_RPAREN :: rest''' -> ParseOk (E_In left args) rest'''
           | _ -> ParseErr "expected ) after IN list"))
     | Tok_NOT :: Tok_IN :: Tok_LPAREN :: rest' ->
       (match parse_expr_list pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk args rest'' ->
          (match rest'' with
           | Tok_RPAREN :: rest''' -> ParseOk (E_NotIn left args) rest'''
           | _ -> ParseErr "expected ) after NOT IN list"))
     | _ -> ParseOk left rest)

and parse_additive_expr (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match parse_multiplicative_expr pm ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk left rest -> parse_additive_expr_loop pm left rest

and parse_additive_expr_loop (pm : prefix_map) (left : expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_PLUS :: rest ->
    (match parse_multiplicative_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk right rest' -> parse_additive_expr_loop pm (E_Arith Add left right) rest')
  | Tok_MINUS_OP :: rest ->
    (match parse_multiplicative_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk right rest' -> parse_additive_expr_loop pm (E_Arith Sub left right) rest')
  | _ -> ParseOk left ts

and parse_multiplicative_expr (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match parse_unary_expr pm ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk left rest -> parse_multiplicative_expr_loop pm left rest

and parse_multiplicative_expr_loop (pm : prefix_map) (left : expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_STAR :: rest ->
    (match parse_unary_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk right rest' -> parse_multiplicative_expr_loop pm (E_Arith Mul left right) rest')
  | Tok_SLASH :: rest ->
    (match parse_unary_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk right rest' -> parse_multiplicative_expr_loop pm (E_Arith Div left right) rest')
  | _ -> ParseOk left ts

and parse_unary_expr (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_BANG :: rest ->
    (match parse_primary_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' -> ParseOk (E_Not e) rest')
  | Tok_MINUS_OP :: rest ->
    (match parse_primary_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' -> ParseOk (E_UnaryMinus e) rest')
  | Tok_PLUS :: rest ->
    (match parse_primary_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' -> ParseOk (E_UnaryPlus e) rest')
  | _ -> parse_primary_expr pm ts

and parse_primary_expr (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_VAR v :: rest -> ParseOk (E_Var v) rest
  | Tok_TRUE :: rest -> ParseOk (E_BoolLit true) rest
  | Tok_FALSE :: rest -> ParseOk (E_BoolLit false) rest
  | Tok_INTEGER s :: rest ->
    (* parse integer — use assume val for string_to_int *)
    ParseOk (E_NumericLit (parse_int_value s)) rest
  | Tok_DECIMAL s :: rest -> ParseOk (E_DecimalLit s) rest
  | Tok_DOUBLE s :: rest -> ParseOk (E_DoubleLit s) rest
  | Tok_STRING s :: rest -> parse_string_expr pm s rest
  | Tok_IRI i :: rest -> parse_iri_expr pm i rest
  | Tok_PNAME pn :: rest ->
    (match resolve_pname pn pm with
     | Some iri -> parse_iri_expr pm iri rest
     | None -> ParseErr "undefined prefix in expression")
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk e rest''
        | _ -> ParseErr "expected ) after expression"))
  (* Aggregates *)
  | Tok_COUNT :: rest -> parse_aggregate pm Agg_Count rest
  | Tok_SUM :: rest -> parse_aggregate pm Agg_Sum rest
  | Tok_MIN_KW :: rest -> parse_aggregate pm Agg_Min rest
  | Tok_MAX_KW :: rest -> parse_aggregate pm Agg_Max rest
  | Tok_AVG :: rest -> parse_aggregate pm Agg_Avg rest
  | Tok_SAMPLE :: rest -> parse_aggregate pm Agg_Sample rest
  | Tok_GROUP_CONCAT :: rest -> parse_group_concat pm rest
  (* Built-in functions: zero-arg *)
  | Tok_NOW :: Tok_LPAREN :: Tok_RPAREN :: rest -> ParseOk E_Now rest
  (* Built-in functions: BOUND *)
  | Tok_BOUND :: Tok_LPAREN :: Tok_VAR v :: Tok_RPAREN :: rest ->
    ParseOk (E_Bound v) rest
  (* Built-in functions: IF *)
  | Tok_IF :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk c rest1 ->
       (match rest1 with
        | Tok_COMMA :: rest2 ->
          (match parse_expr pm rest2 with
           | ParseErr msg -> ParseErr msg
           | ParseOk t rest3 ->
             (match rest3 with
              | Tok_COMMA :: rest4 ->
                (match parse_expr pm rest4 with
                 | ParseErr msg -> ParseErr msg
                 | ParseOk f rest5 ->
                   (match rest5 with
                    | Tok_RPAREN :: rest6 -> ParseOk (E_If c t f) rest6
                    | _ -> ParseErr "expected ) after IF"))
              | _ -> ParseErr "expected , in IF"))
        | _ -> ParseErr "expected , in IF"))
  (* COALESCE *)
  | Tok_COALESCE :: Tok_LPAREN :: rest ->
    (match parse_expr_list_or_empty pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk args rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk (E_Coalesce args) rest''
        | _ -> ParseErr "expected ) after COALESCE"))
  (* CONCAT *)
  | Tok_CONCAT :: Tok_LPAREN :: rest ->
    (match parse_expr_list_or_empty pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk args rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk (E_Concat args) rest''
        | _ -> ParseErr "expected ) after CONCAT"))
  (* EXISTS / NOT EXISTS *)
  | Tok_EXISTS :: rest ->
    (match parse_group_graph_pattern pm 100 rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk ggp rest' -> ParseOk (E_Exists ggp) rest')
  | Tok_NOT :: Tok_EXISTS :: rest ->
    (match parse_group_graph_pattern pm 100 rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk ggp rest' -> ParseOk (E_NotExists ggp) rest')
  (* One-arg built-in functions *)
  | Tok_STR :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Str rest
  | Tok_LANG :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Lang rest
  | Tok_DATATYPE :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Datatype rest
  | Tok_IRI_KW :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_IRI_fn rest
  | Tok_ISIRI :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_IsIRI rest
  | Tok_ISBLANK :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_IsBlank rest
  | Tok_ISLITERAL :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_IsLiteral rest
  | Tok_ISNUMERIC :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_IsNumeric rest
  | Tok_ABS :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Abs rest
  | Tok_CEIL :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Ceil rest
  | Tok_FLOOR :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Floor rest
  | Tok_ROUND :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Round rest
  | Tok_STRLEN :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_StrLen rest
  | Tok_UCASE :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_UCase rest
  | Tok_LCASE :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_LCase rest
  | Tok_ENCODE_FOR_URI :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_EncodeForUri rest
  | Tok_MD5 :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_MD5 rest
  | Tok_SHA1 :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_SHA1 rest
  | Tok_SHA256 :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_SHA256 rest
  | Tok_SHA384 :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_SHA384 rest
  | Tok_SHA512 :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_SHA512 rest
  | Tok_YEAR :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Year rest
  | Tok_MONTH :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Month rest
  | Tok_DAY :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Day rest
  | Tok_HOURS :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Hours rest
  | Tok_MINUTES :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Minutes rest
  | Tok_SECONDS :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Seconds rest
  | Tok_TIMEZONE :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Timezone rest
  | Tok_TZ :: Tok_LPAREN :: rest -> parse_one_arg_builtin pm E_Tz rest
  (* Two-arg built-in functions *)
  | Tok_SAMETERM :: Tok_LPAREN :: rest -> parse_two_arg_builtin pm E_SameTerm rest
  | Tok_STRDT :: Tok_LPAREN :: rest -> parse_two_arg_builtin pm E_StrDt rest
  | Tok_STRLANG :: Tok_LPAREN :: rest -> parse_two_arg_builtin pm E_StrLang rest
  | Tok_CONTAINS :: Tok_LPAREN :: rest -> parse_two_arg_builtin pm E_Contains rest
  | Tok_STRSTARTS :: Tok_LPAREN :: rest -> parse_two_arg_builtin pm E_StrStarts rest
  | Tok_STRENDS :: Tok_LPAREN :: rest -> parse_two_arg_builtin pm E_StrEnds rest
  | Tok_STRBEFORE :: Tok_LPAREN :: rest -> parse_two_arg_builtin pm E_StrBefore rest
  | Tok_STRAFTER :: Tok_LPAREN :: rest -> parse_two_arg_builtin pm E_StrAfter rest
  | Tok_LANGMATCHES :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk a rest1 ->
       (match rest1 with
        | Tok_COMMA :: rest2 ->
          (match parse_expr pm rest2 with
           | ParseErr msg -> ParseErr msg
           | ParseOk b rest3 ->
             (match rest3 with
              | Tok_RPAREN :: rest4 ->
                let iri = "http://www.w3.org/2005/xpath-functions#langMatches" in
                if is_iri iri then ParseOk (E_FunctionCall iri [a; b]) rest4
                else ParseErr "internal: langMatches IRI"
              | _ -> ParseErr "expected ) after LANGMATCHES"))
        | _ -> ParseErr "expected , in LANGMATCHES"))
  (* SUBSTR *)
  | Tok_SUBSTR :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk s rest1 ->
       (match rest1 with
        | Tok_COMMA :: rest2 ->
          (match parse_expr pm rest2 with
           | ParseErr msg -> ParseErr msg
           | ParseOk start rest3 ->
             (match rest3 with
              | Tok_COMMA :: rest4 ->
                (match parse_expr pm rest4 with
                 | ParseErr msg -> ParseErr msg
                 | ParseOk len rest5 ->
                   (match rest5 with
                    | Tok_RPAREN :: rest6 -> ParseOk (E_Substr s start (Some len)) rest6
                    | _ -> ParseErr "expected ) after SUBSTR"))
              | Tok_RPAREN :: rest4 -> ParseOk (E_Substr s start None) rest4
              | _ -> ParseErr "expected , or ) in SUBSTR"))
        | _ -> ParseErr "expected , in SUBSTR"))
  (* REPLACE *)
  | Tok_REPLACE :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk s rest1 ->
       (match rest1 with
        | Tok_COMMA :: rest2 ->
          (match parse_expr pm rest2 with
           | ParseErr msg -> ParseErr msg
           | ParseOk pat rest3 ->
             (match rest3 with
              | Tok_COMMA :: rest4 ->
                (match parse_expr pm rest4 with
                 | ParseErr msg -> ParseErr msg
                 | ParseOk rep rest5 ->
                   (match rest5 with
                    | Tok_COMMA :: rest6 ->
                      (match parse_expr pm rest6 with
                       | ParseErr msg -> ParseErr msg
                       | ParseOk flags rest7 ->
                         (match rest7 with
                          | Tok_RPAREN :: rest8 -> ParseOk (E_Replace s pat rep (Some flags)) rest8
                          | _ -> ParseErr "expected ) after REPLACE"))
                    | Tok_RPAREN :: rest6 -> ParseOk (E_Replace s pat rep None) rest6
                    | _ -> ParseErr "expected , or ) in REPLACE"))
              | _ -> ParseErr "expected , in REPLACE"))
        | _ -> ParseErr "expected , in REPLACE"))
  (* REGEX *)
  | Tok_REGEX :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk s rest1 ->
       (match rest1 with
        | Tok_COMMA :: rest2 ->
          (match parse_expr pm rest2 with
           | ParseErr msg -> ParseErr msg
           | ParseOk pat rest3 ->
             (match rest3 with
              | Tok_COMMA :: rest4 ->
                (match parse_expr pm rest4 with
                 | ParseErr msg -> ParseErr msg
                 | ParseOk flags rest5 ->
                   (match rest5 with
                    | Tok_RPAREN :: rest6 -> ParseOk (E_Regex s pat (Some flags)) rest6
                    | _ -> ParseErr "expected ) after REGEX"))
              | Tok_RPAREN :: rest4 -> ParseOk (E_Regex s pat None) rest4
              | _ -> ParseErr "expected , or ) in REGEX"))
        | _ -> ParseErr "expected , in REGEX"))
  | _ -> ParseErr "unexpected token in expression"

(* Parse a string literal followed by optional langtag or ^^ datatype *)
and parse_string_expr (pm : prefix_map) (s : string) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_LANGTAG lang :: rest ->
    ParseOk (E_Literal { lexical_form = s;
                          datatype = rdf_lang_string;
                          lang_tag = Some lang }) rest
  | Tok_HATHAT :: rest ->
    (match parse_iri_from_stream pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk dt rest' ->
       ParseOk (E_Literal { lexical_form = s;
                             datatype = dt;
                             lang_tag = None }) rest')
  | _ ->
    ParseOk (E_Literal { lexical_form = s;
                          datatype = xsd_string;
                          lang_tag = None }) ts

(* Parse IRI possibly followed by ( args ) for function call *)
and parse_iri_expr (pm : prefix_map) (iri : string) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_LPAREN :: rest ->
    (match parse_expr_list_or_empty pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk args rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' ->
          if is_iri iri then ParseOk (E_FunctionCall iri args) rest''
          else ParseErr "invalid IRI in function call"
        | _ -> ParseErr "expected ) after function args"))
  | _ ->
    if is_iri iri then ParseOk (E_IRI iri) ts
    else ParseErr "invalid IRI in expression"

(* Parse one-arg built-in: ( expr ) *)
and parse_one_arg_builtin (pm : prefix_map) (f : expr -> expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match parse_expr pm ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk e rest ->
    (match rest with
     | Tok_RPAREN :: rest' -> ParseOk (f e) rest'
     | _ -> ParseErr "expected ) after built-in function arg")

(* Parse two-arg built-in: expr , expr ) *)
and parse_two_arg_builtin (pm : prefix_map) (f : expr -> expr -> expr) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match parse_expr pm ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk a rest ->
    (match rest with
     | Tok_COMMA :: rest' ->
       (match parse_expr pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk b rest'' ->
          (match rest'' with
           | Tok_RPAREN :: rest''' -> ParseOk (f a b) rest'''
           | _ -> ParseErr "expected ) after two-arg built-in"))
     | _ -> ParseErr "expected , in two-arg built-in")

(* Parse aggregate: ( [DISTINCT] expr ) *)
and parse_aggregate (pm : prefix_map) (agg : aggregate_fn) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_LPAREN :: Tok_DISTINCT :: Tok_STAR :: Tok_RPAREN :: rest ->
    ParseOk (E_Aggregate Agg_Count true (E_NumericLit 1)) rest
  | Tok_LPAREN :: Tok_STAR :: Tok_RPAREN :: rest ->
    ParseOk (E_Aggregate Agg_Count false (E_NumericLit 1)) rest
  | Tok_LPAREN :: Tok_DISTINCT :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk (E_Aggregate agg true e) rest''
        | _ -> ParseErr "expected ) after aggregate"))
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk (E_Aggregate agg false e) rest''
        | _ -> ParseErr "expected ) after aggregate"))
  | _ -> ParseErr "expected ( after aggregate keyword"

(* Parse GROUP_CONCAT: ( [DISTINCT] expr [; SEPARATOR = "sep"] ) *)
and parse_group_concat (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_LPAREN :: Tok_DISTINCT :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_SEMI :: Tok_SEPARATOR :: Tok_EQ :: Tok_STRING sep :: Tok_RPAREN :: rest'' ->
          ParseOk (E_Aggregate (Agg_GroupConcat (Some sep)) true e) rest''
        | Tok_RPAREN :: rest'' ->
          ParseOk (E_Aggregate (Agg_GroupConcat None) true e) rest''
        | _ -> ParseErr "expected ; SEPARATOR = or ) in GROUP_CONCAT"))
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_SEMI :: Tok_SEPARATOR :: Tok_EQ :: Tok_STRING sep :: Tok_RPAREN :: rest'' ->
          ParseOk (E_Aggregate (Agg_GroupConcat (Some sep)) false e) rest''
        | Tok_RPAREN :: rest'' ->
          ParseOk (E_Aggregate (Agg_GroupConcat None) false e) rest''
        | _ -> ParseErr "expected ; SEPARATOR = or ) in GROUP_CONCAT"))
  | _ -> ParseErr "expected ( after GROUP_CONCAT"

(* Parse comma-separated expression list (non-empty) *)
and parse_expr_list (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result (list expr)) (decreases (List.length ts)) =
  match parse_expr pm ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk e rest ->
    (match rest with
     | Tok_COMMA :: rest' ->
       (match parse_expr_list pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk es rest'' -> ParseOk (e :: es) rest'')
     | _ -> ParseOk [e] rest)

(* Parse expr list or empty (for COALESCE(), CONCAT(), etc.) *)
and parse_expr_list_or_empty (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result (list expr)) (decreases (List.length ts)) =
  match ts with
  | Tok_RPAREN :: _ -> ParseOk [] ts  (* don't consume the ) *)
  | _ -> parse_expr_list pm ts

(* ================================================================== *)
(* Pattern term parsing — for triple pattern positions                *)
(* ================================================================== *)

and parse_pattern_term (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result pattern_term) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted in pattern term"
  else match ts with
  | Tok_VAR v :: rest -> ParseOk (PT_Var v) rest
  | Tok_IRI i :: rest -> ParseOk (PT_IRI i) rest
  | Tok_PNAME pn :: rest ->
    (match resolve_pname pn pm with
     | Some iri -> ParseOk (PT_IRI iri) rest
     | None -> ParseErr "undefined prefix in pattern term")
  | Tok_A :: rest -> ParseOk (PT_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#type") rest
  | Tok_BNODE b :: rest -> ParseOk (PT_BNode b) rest
  | Tok_ANON :: rest -> ParseOk (PT_BNode (fresh_bnode_id ())) rest
  | Tok_TRUE :: rest -> ParseOk (PT_Literal { lexical_form = "true"; datatype = xsd_boolean; lang_tag = None }) rest
  | Tok_FALSE :: rest -> ParseOk (PT_Literal { lexical_form = "false"; datatype = xsd_boolean; lang_tag = None }) rest
  | Tok_INTEGER s :: rest -> ParseOk (PT_Literal { lexical_form = s; datatype = xsd_integer; lang_tag = None }) rest
  | Tok_DECIMAL s :: rest -> ParseOk (PT_Literal { lexical_form = s; datatype = xsd_decimal; lang_tag = None }) rest
  | Tok_DOUBLE s :: rest -> ParseOk (PT_Literal { lexical_form = s; datatype = xsd_double; lang_tag = None }) rest
  | Tok_STRING s :: rest ->
    (match rest with
     | Tok_LANGTAG lang :: rest' ->
       ParseOk (PT_Literal { lexical_form = s; datatype = rdf_lang_string; lang_tag = Some lang }) rest'
     | Tok_HATHAT :: rest' ->
       (match parse_iri_from_stream pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk dt rest'' ->
          ParseOk (PT_Literal { lexical_form = s; datatype = dt; lang_tag = None }) rest'')
     | _ -> ParseOk (PT_Literal { lexical_form = s; datatype = xsd_string; lang_tag = None }) rest)
  | _ -> ParseErr "expected pattern term"

(* Parse pattern subject *)
and parse_pattern_subject (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result pattern_subject) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted in pattern subject"
  else match ts with
  | Tok_VAR v :: rest -> ParseOk (PS_Var v) rest
  | Tok_IRI i :: rest -> ParseOk (PS_IRI i) rest
  | Tok_PNAME pn :: rest ->
    (match resolve_pname pn pm with
     | Some iri -> ParseOk (PS_IRI iri) rest
     | None -> ParseErr "undefined prefix in pattern subject")
  | Tok_BNODE b :: rest -> ParseOk (PS_BNode b) rest
  | Tok_ANON :: rest -> ParseOk (PS_BNode (fresh_bnode_id ())) rest
  | _ -> ParseErr "expected pattern subject"

(* ================================================================== *)
(* Property path parsing                                               *)
(* ================================================================== *)

and parse_property_path (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted in property path"
  else parse_path_alternative pm (fuel - 1) ts

and parse_path_alternative (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match parse_path_sequence pm (fuel - 1) ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk left rest -> parse_path_alt_loop pm (fuel - 1) left rest

and parse_path_alt_loop (pm : prefix_map) (fuel : nat) (left : property_path) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseOk left ts
  else match ts with
  | Tok_PIPE :: rest ->
    (match parse_path_sequence pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk right rest' -> parse_path_alt_loop pm (fuel - 1) (PP_Alternative left right) rest')
  | _ -> ParseOk left ts

and parse_path_sequence (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match parse_path_elt_or_inverse pm (fuel - 1) ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk left rest -> parse_path_seq_loop pm (fuel - 1) left rest

and parse_path_seq_loop (pm : prefix_map) (fuel : nat) (left : property_path) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseOk left ts
  else match ts with
  | Tok_SLASH :: rest ->
    (match parse_path_elt_or_inverse pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk right rest' -> parse_path_seq_loop pm (fuel - 1) (PP_Sequence left right) rest')
  | _ -> ParseOk left ts

and parse_path_elt_or_inverse (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match ts with
  | Tok_CARET :: rest ->
    (match parse_path_primary pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk p rest' -> ParseOk (PP_Inverse p) rest')
  | _ -> parse_path_elt pm (fuel - 1) ts

and parse_path_elt (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match parse_path_primary pm (fuel - 1) ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk p rest ->
    (match rest with
     | Tok_STAR :: rest' -> ParseOk (PP_ZeroOrMore p) rest'
     | Tok_PLUS :: rest' -> ParseOk (PP_OneOrMore p) rest'
     | Tok_QMARK :: rest' -> ParseOk (PP_ZeroOrOne p) rest'
     | _ -> ParseOk p rest)

and parse_path_primary (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result property_path) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match ts with
  | Tok_IRI i :: rest -> ParseOk (PP_IRI i) rest
  | Tok_PNAME pn :: rest ->
    (match resolve_pname pn pm with
     | Some iri -> ParseOk (PP_IRI iri) rest
     | None -> ParseErr "undefined prefix in path")
  | Tok_A :: rest -> ParseOk (PP_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#type") rest
  | Tok_LPAREN :: rest ->
    (match parse_property_path pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk p rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk p rest''
        | _ -> ParseErr "expected ) after path"))
  | Tok_BANG :: Tok_LPAREN :: rest ->
    (match parse_negated_path_list pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk paths rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk (PP_NegatedSet paths) rest''
        | _ -> ParseErr "expected ) after negated path set"))
  | Tok_BANG :: rest ->
    (match parse_path_elt_or_inverse pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk p rest' -> ParseOk (PP_NegatedSet [p]) rest')
  | _ -> ParseErr "expected path primary"

and parse_negated_path_list (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (list property_path)) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match parse_path_elt_or_inverse pm (fuel - 1) ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk p rest ->
    (match rest with
     | Tok_PIPE :: rest' ->
       (match parse_negated_path_list pm (fuel - 1) rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk ps rest'' -> ParseOk (p :: ps) rest'')
     | _ -> ParseOk [p] rest)

(* ================================================================== *)
(* Verb parsing: simple predicate or property path                    *)
(* Returns either a pattern_term (simple) or property_path            *)
(* ================================================================== *)

and parse_verb (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result verb_result) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match ts with
  | Tok_A :: rest -> ParseOk (VR_Simple (PT_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#type")) rest
  | Tok_VAR v :: rest -> ParseOk (VR_Simple (PT_Var v)) rest
  | _ ->
    (match parse_property_path pm (fuel - 1) ts with
     | ParseErr msg -> ParseErr msg
     | ParseOk (PP_IRI i) rest -> ParseOk (VR_Simple (PT_IRI i)) rest
     | ParseOk path rest -> ParseOk (VR_Path path) rest)

(* ================================================================== *)
(* Triple pattern parsing: subject predicate-object-list              *)
(* ================================================================== *)

(* Parse object list: obj [, obj]* *)
and parse_object_list (pm : prefix_map) (fuel : nat) (subj : pattern_subject)
    (verb : verb_result) (ts : token_stream)
  : Tot (parse_result (list group_graph_pattern)) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match parse_pattern_term pm (fuel - 1) ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk obj rest ->
    let pat = match verb with
      | VR_Simple p -> GP_BGP [{ tp_s = subj; tp_p = p; tp_o = obj }]
      | VR_Path path -> GP_PropertyPath subj path obj in
    (match rest with
     | Tok_COMMA :: rest' ->
       (match parse_object_list pm (fuel - 1) subj verb rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk pats rest'' -> ParseOk (pat :: pats) rest'')
     | _ -> ParseOk [pat] rest)

(* Parse predicate-object list: verb objList [; verb objList]* *)
and parse_predicate_object_list (pm : prefix_map) (fuel : nat) (subj : pattern_subject) (ts : token_stream)
  : Tot (parse_result (list group_graph_pattern)) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match parse_verb pm (fuel - 1) ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk verb rest ->
    (match parse_object_list pm (fuel - 1) subj verb rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk pats rest' ->
       (match rest' with
        | Tok_SEMI :: rest'' ->
          (* After semicolon, check if there's another predicate or just trailing ; *)
          (match rest'' with
           | Tok_RBRACE :: _ | Tok_DOT :: _ | Tok_RBRACKET :: _ | [] ->
             ParseOk pats rest''
           | _ ->
             (match parse_predicate_object_list pm (fuel - 1) subj rest'' with
              | ParseErr _ -> ParseOk pats rest''  (* trailing ; is OK *)
              | ParseOk more_pats rest''' -> ParseOk (pats @ more_pats) rest'''))
        | _ -> ParseOk pats rest'))

(* ================================================================== *)
(* Group graph pattern parsing                                         *)
(* ================================================================== *)

and parse_group_graph_pattern (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted in group graph pattern"
  else match ts with
  | Tok_LBRACE :: rest ->
    (* Check for sub-select *)
    (match rest with
     | Tok_SELECT :: _ ->
       (match parse_select_query pm (fuel - 1) rest with
        | ParseErr msg -> ParseErr msg
        | ParseOk q rest' ->
          (match rest' with
           | Tok_RBRACE :: rest'' -> ParseOk (GP_SubSelect q) rest''
           | _ -> ParseErr "expected } after sub-select"))
     | _ ->
       (match parse_group_pattern_contents pm (fuel - 1) rest with
        | ParseErr msg -> ParseErr msg
        | ParseOk pat rest' ->
          (match rest' with
           | Tok_RBRACE :: rest'' -> ParseOk pat rest''
           | _ -> ParseErr "expected } after group pattern")))
  | _ -> ParseErr "expected { to start group graph pattern"

(* Parse the contents inside { ... } *)
and parse_group_pattern_contents (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else parse_group_elements pm (fuel - 1) GP_Empty [] ts

(* Parse group elements accumulating patterns and filters *)
and parse_group_elements (pm : prefix_map) (fuel : nat) (acc : group_graph_pattern)
    (filters : list expr) (ts : token_stream)
  : Tot (parse_result group_graph_pattern) (decreases fuel) =
  if fuel = 0 then ParseOk (apply_filters acc filters) ts
  else match ts with
  | Tok_RBRACE :: _ | [] -> ParseOk (apply_filters acc filters) ts
  | Tok_DOT :: rest -> parse_group_elements pm (fuel - 1) acc filters rest
  | Tok_OPTIONAL :: rest ->
    (match parse_group_graph_pattern pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk opt rest' ->
       let acc' = GP_LeftJoin acc opt (E_BoolLit true) in
       parse_group_elements pm (fuel - 1) acc' filters rest')
  | Tok_MINUS_KW :: rest ->
    (match parse_group_graph_pattern pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk right rest' ->
       let acc' = GP_Minus acc right in
       parse_group_elements pm (fuel - 1) acc' filters rest')
  | Tok_UNION :: rest ->
    (match parse_group_graph_pattern pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk right rest' ->
       let acc' = GP_Union acc right in
       parse_group_elements pm (fuel - 1) acc' filters rest')
  | Tok_FILTER :: rest ->
    (match parse_filter_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       parse_group_elements pm (fuel - 1) acc (e :: filters) rest')
  | Tok_BIND :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_AS :: Tok_VAR v :: Tok_RPAREN :: rest'' ->
          let acc' = GP_Bind e v acc in
          parse_group_elements pm (fuel - 1) acc' filters rest''
        | _ -> ParseErr "expected AS ?var) in BIND"))
  | Tok_VALUES :: rest ->
    (match parse_inline_data pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk (vars, rows) rest' ->
       let acc' = join_patterns acc (GP_Values vars rows) in
       parse_group_elements pm (fuel - 1) acc' filters rest')
  | Tok_GRAPH :: rest ->
    (match parse_pattern_term pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk g rest' ->
       (match parse_group_graph_pattern pm (fuel - 1) rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk p rest'' ->
          let acc' = join_patterns acc (GP_Graph g p) in
          parse_group_elements pm (fuel - 1) acc' filters rest''))
  | Tok_SERVICE :: Tok_SILENT :: rest1 ->
    (match parse_iri_from_stream pm rest1 with
     | ParseErr msg -> ParseErr msg
     | ParseOk iri rest2 ->
       (match parse_group_graph_pattern pm (fuel - 1) rest2 with
        | ParseErr msg -> ParseErr msg
        | ParseOk p rest3 ->
          let acc' = join_patterns acc (GP_Service iri p true) in
          parse_group_elements pm (fuel - 1) acc' filters rest3))
  | Tok_SERVICE :: rest ->
    (match parse_iri_from_stream pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk iri rest2 ->
       (match parse_group_graph_pattern pm (fuel - 1) rest2 with
        | ParseErr msg -> ParseErr msg
        | ParseOk p rest3 ->
          let acc' = join_patterns acc (GP_Service iri p false) in
          parse_group_elements pm (fuel - 1) acc' filters rest3))
  | Tok_LBRACE :: _ ->
    (* Nested group or sub-select *)
    (match parse_group_graph_pattern pm (fuel - 1) ts with
     | ParseErr msg -> ParseErr msg
     | ParseOk sub rest' ->
       (* Check for UNION after nested group *)
       (match rest' with
        | Tok_UNION :: rest'' ->
          (match parse_group_graph_pattern pm (fuel - 1) rest'' with
           | ParseErr msg -> ParseErr msg
           | ParseOk right rest''' ->
             let acc' = join_patterns acc (GP_Union sub right) in
             parse_group_elements pm (fuel - 1) acc' filters rest''')
        | _ ->
          let acc' = join_patterns acc sub in
          parse_group_elements pm (fuel - 1) acc' filters rest'))
  | _ ->
    (* Try to parse triple patterns *)
    (match parse_pattern_subject pm (fuel - 1) ts with
     | ParseErr _ -> ParseOk (apply_filters acc filters) ts  (* no more triples *)
     | ParseOk subj rest ->
       (match parse_predicate_object_list pm (fuel - 1) subj rest with
        | ParseErr msg -> ParseErr msg
        | ParseOk pats rest' ->
          let bgp = combine_patterns pats in
          let acc' = join_patterns acc bgp in
          (* Skip optional dot *)
          let rest'' = match rest' with Tok_DOT :: r -> r | _ -> rest' in
          parse_group_elements pm (fuel - 1) acc' filters rest''))

(* Parse FILTER expression: either (expr) or bare expr for EXISTS etc *)
and parse_filter_expr (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result expr) (decreases (List.length ts)) =
  match ts with
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' -> ParseOk e rest''
        | _ -> ParseErr "expected ) after FILTER expression"))
  | _ -> parse_expr pm ts  (* for FILTER EXISTS, FILTER NOT EXISTS *)

(* Parse inline data for VALUES clause *)
and parse_inline_data (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (list var_name & list (list (option rdf_term)))) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match ts with
  | Tok_VAR v :: Tok_LBRACE :: rest ->
    (* Single variable: VALUES ?x { val1 val2 ... } *)
    (match parse_values_single pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk rows rest' -> ParseOk ([v], rows) rest')
  | Tok_LPAREN :: rest ->
    (* Multi variable: VALUES (?x ?y) { (...) (...) } *)
    (match parse_var_list rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk vars rest' ->
       (match rest' with
        | Tok_LBRACE :: rest'' ->
          (match parse_values_multi pm (fuel - 1) (List.length vars) rest'' with
           | ParseErr msg -> ParseErr msg
           | ParseOk rows rest''' -> ParseOk (vars, rows) rest''')
        | _ -> ParseErr "expected { after variable list in VALUES"))
  | _ -> ParseErr "expected variable or ( in VALUES"

(* Parse single-variable VALUES rows: val1 val2 ... } *)
and parse_values_single (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (list (list (option rdf_term)))) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match ts with
  | Tok_RBRACE :: rest -> ParseOk [] rest
  | Tok_UNDEF :: rest ->
    (match parse_values_single pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk rows rest' -> ParseOk ([None] :: rows) rest')
  | _ ->
    (match parse_rdf_term_for_values pm ts with
     | ParseErr msg -> ParseErr msg
     | ParseOk t rest ->
       (match parse_values_single pm (fuel - 1) rest with
        | ParseErr msg -> ParseErr msg
        | ParseOk rows rest' -> ParseOk ([Some t] :: rows) rest'))

(* Parse multi-variable VALUES rows: (v1 v2) (v3 v4) ... } *)
and parse_values_multi (pm : prefix_map) (fuel : nat) (nvars : nat) (ts : token_stream)
  : Tot (parse_result (list (list (option rdf_term)))) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match ts with
  | Tok_RBRACE :: rest -> ParseOk [] rest
  | Tok_LPAREN :: rest ->
    (match parse_values_row pm (fuel - 1) nvars rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk row rest' ->
       (match parse_values_multi pm (fuel - 1) nvars rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk rows rest'' -> ParseOk (row :: rows) rest''))
  | _ -> ParseErr "expected ( or } in VALUES data"

(* Parse one row of VALUES: term1 term2 ... ) *)
and parse_values_row (pm : prefix_map) (fuel : nat) (remaining : nat) (ts : token_stream)
  : Tot (parse_result (list (option rdf_term))) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else if remaining = 0 then
    (match ts with
     | Tok_RPAREN :: rest -> ParseOk [] rest
     | _ -> ParseErr "expected ) after VALUES row")
  else match ts with
  | Tok_UNDEF :: rest ->
    (match parse_values_row pm (fuel - 1) (remaining - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk vals rest' -> ParseOk (None :: vals) rest')
  | _ ->
    (match parse_rdf_term_for_values pm ts with
     | ParseErr msg -> ParseErr msg
     | ParseOk t rest ->
       (match parse_values_row pm (fuel - 1) (remaining - 1) rest with
        | ParseErr msg -> ParseErr msg
        | ParseOk vals rest' -> ParseOk (Some t :: vals) rest'))

(* Parse an RDF term in VALUES context *)
and parse_rdf_term_for_values (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result rdf_term) (decreases (List.length ts)) =
  match ts with
  | Tok_IRI i :: rest -> ParseOk (T_IRI i) rest
  | Tok_PNAME pn :: rest ->
    (match resolve_pname pn pm with
     | Some iri -> ParseOk (T_IRI iri) rest
     | None -> ParseErr "undefined prefix in VALUES term")
  | Tok_BNODE b :: rest -> ParseOk (T_BNode b) rest
  | Tok_TRUE :: rest -> ParseOk (T_Literal { lexical_form = "true"; datatype = xsd_boolean; lang_tag = None }) rest
  | Tok_FALSE :: rest -> ParseOk (T_Literal { lexical_form = "false"; datatype = xsd_boolean; lang_tag = None }) rest
  | Tok_INTEGER s :: rest -> ParseOk (T_Literal { lexical_form = s; datatype = xsd_integer; lang_tag = None }) rest
  | Tok_DECIMAL s :: rest -> ParseOk (T_Literal { lexical_form = s; datatype = xsd_decimal; lang_tag = None }) rest
  | Tok_DOUBLE s :: rest -> ParseOk (T_Literal { lexical_form = s; datatype = xsd_double; lang_tag = None }) rest
  | Tok_STRING s :: rest ->
    (match rest with
     | Tok_LANGTAG lang :: rest' ->
       ParseOk (T_Literal { lexical_form = s; datatype = rdf_lang_string; lang_tag = Some lang }) rest'
     | Tok_HATHAT :: rest' ->
       (match parse_iri_from_stream pm rest' with
        | ParseErr msg -> ParseErr msg
        | ParseOk dt rest'' ->
          ParseOk (T_Literal { lexical_form = s; datatype = dt; lang_tag = None }) rest'')
     | _ -> ParseOk (T_Literal { lexical_form = s; datatype = xsd_string; lang_tag = None }) rest)
  | _ -> ParseErr "expected RDF term in VALUES"

(* Parse variable list: ?x ?y ... ) *)
and parse_var_list (ts : token_stream)
  : Tot (parse_result (list var_name)) (decreases (List.length ts)) =
  match ts with
  | Tok_RPAREN :: rest -> ParseOk [] rest
  | Tok_VAR v :: rest ->
    (match parse_var_list rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk vs rest' -> ParseOk (v :: vs) rest')
  | _ -> ParseErr "expected variable or ) in variable list"

(* ================================================================== *)
(* SELECT query parsing                                                *)
(* ================================================================== *)

and parse_select_query (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result query) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted in select query"
  else match ts with
  | Tok_SELECT :: Tok_DISTINCT :: rest ->
    parse_select_query_body pm fuel true false rest
  | Tok_SELECT :: Tok_REDUCED :: rest ->
    parse_select_query_body pm fuel false true rest
  | Tok_SELECT :: rest ->
    parse_select_query_body pm fuel false false rest
  | _ -> ParseErr "expected SELECT"

and parse_select_query_body (pm : prefix_map) (fuel : nat) (distinct : bool)
    (reduced : bool) (ts : token_stream)
  : Tot (parse_result query) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match parse_select_clause pm ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk select_cl rest ->
    (* Skip optional WHERE keyword *)
    let rest' = skip_where rest in
    (match parse_group_graph_pattern pm (fuel - 1) rest' with
     | ParseErr msg -> ParseErr msg
     | ParseOk pattern rest'' ->
       parse_select_modifiers pm (fuel - 1) select_cl distinct reduced pattern rest'')

(* Skip optional WHERE keyword *)
and skip_where (ts : token_stream) : Tot token_stream (decreases 0) =
  match ts with
  | Tok_WHERE :: rest -> rest
  | _ -> ts

(* Parse all solution modifiers after the WHERE pattern *)
and parse_select_modifiers (pm : prefix_map) (fuel : nat) (select_cl : select_clause)
    (distinct : bool) (reduced : bool) (pattern : group_graph_pattern) (ts : token_stream)
  : Tot (parse_result query) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else
    let gb_result = parse_group_by pm ts in
    let group_by = fst gb_result in
    let ts1 = snd gb_result in
    let h_result = parse_having pm ts1 in
    let having = fst h_result in
    let ts2 = snd h_result in
    let ob_result = parse_order_by pm ts2 in
    let order_by = fst ob_result in
    let ts3 = snd ob_result in
    let l_result = parse_limit ts3 in
    let limit0 = fst l_result in
    let ts4 = snd l_result in
    let o_result = parse_offset ts4 in
    let offset = fst o_result in
    let ts5 = snd o_result in
    (* LIMIT can also come after OFFSET *)
    let l2_result = if None? limit0 then parse_limit ts5 else (limit0, ts5) in
    let limit = fst l2_result in
    let ts6 = snd l2_result in
    let v_result = parse_post_values pm (fuel - 1) ts6 in
    let values = fst v_result in
    let ts7 = snd v_result in
    ParseOk ({
      q_base = None;
      q_prefixes = pm;
      q_form = QF_Select select_cl;
      q_dataset = [];
      q_pattern = pattern;
      q_group_by = group_by;
      q_having = having;
      q_modifier = {
        sm_order_by = order_by;
        sm_distinct = distinct;
        sm_reduced = reduced;
        sm_offset = offset;
        sm_limit = limit;
      };
      q_values = values;
    }) ts7

(* Parse SELECT clause: * | var+ | (expr AS ?var)+ *)
and parse_select_clause (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result select_clause) (decreases (List.length ts)) =
  match ts with
  | Tok_STAR :: rest -> ParseOk Select_All rest
  | _ -> match parse_select_items pm ts with
    | ParseErr msg -> ParseErr msg
    | ParseOk items rest -> ParseOk (Select_Vars items) rest

and parse_select_items (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result (list select_item)) (decreases (List.length ts)) =
  match ts with
  | Tok_VAR v :: rest ->
    (match parse_select_items pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk items rest' -> ParseOk (SI_Var v :: items) rest')
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_AS :: Tok_VAR v :: Tok_RPAREN :: rest'' ->
          (match parse_select_items pm rest'' with
           | ParseErr msg -> ParseErr msg
           | ParseOk items rest''' -> ParseOk (SI_Expr e v :: items) rest''')
        | _ -> ParseErr "expected AS ?var) in SELECT expression"))
  | _ -> ParseOk [] ts  (* end of select items *)

(* Parse GROUP BY clause *)
and parse_group_by (pm : prefix_map) (ts : token_stream)
  : Tot (option (list group_condition) & token_stream) (decreases (List.length ts)) =
  match ts with
  | Tok_GROUP :: Tok_BY :: rest ->
    (match parse_group_conditions pm rest with
     | ParseErr _ -> (None, ts)
     | ParseOk conds rest' -> (Some conds, rest'))
  | _ -> (None, ts)

and parse_group_conditions (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result (list group_condition)) (decreases (List.length ts)) =
  match ts with
  | Tok_VAR v :: rest ->
    (match parse_group_conditions pm rest with
     | ParseErr _ -> ParseOk [GC_Var v] rest
     | ParseOk conds rest' -> ParseOk (GC_Var v :: conds) rest')
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_AS :: Tok_VAR v :: Tok_RPAREN :: rest'' ->
          (match parse_group_conditions pm rest'' with
           | ParseErr _ -> ParseOk [GC_Expr e (Some v)] rest''
           | ParseOk conds rest''' -> ParseOk (GC_Expr e (Some v) :: conds) rest''')
        | Tok_RPAREN :: rest'' ->
          (match parse_group_conditions pm rest'' with
           | ParseErr _ -> ParseOk [GC_Expr e None] rest''
           | ParseOk conds rest''' -> ParseOk (GC_Expr e None :: conds) rest''')
        | _ -> ParseErr "expected ) in GROUP BY"))
  | _ -> ParseOk [] ts

(* Parse HAVING clause *)
and parse_having (pm : prefix_map) (ts : token_stream)
  : Tot (option (list having_condition) & token_stream) (decreases (List.length ts)) =
  match ts with
  | Tok_HAVING :: rest ->
    (match parse_having_conditions pm rest with
     | ParseErr _ -> (None, ts)
     | ParseOk conds rest' -> (Some conds, rest'))
  | _ -> (None, ts)

and parse_having_conditions (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result (list having_condition)) (decreases (List.length ts)) =
  match ts with
  | Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' ->
          (match parse_having_conditions pm rest'' with
           | ParseErr _ -> ParseOk [e] rest''
           | ParseOk conds rest''' -> ParseOk (e :: conds) rest''')
        | _ -> ParseErr "expected ) in HAVING"))
  | _ ->
    (match parse_expr pm ts with
     | ParseErr _ -> ParseOk [] ts
     | ParseOk e rest -> ParseOk [e] rest)

(* Parse ORDER BY clause *)
and parse_order_by (pm : prefix_map) (ts : token_stream)
  : Tot (option (list order_condition) & token_stream) (decreases (List.length ts)) =
  match ts with
  | Tok_ORDER :: Tok_BY :: rest ->
    (match parse_order_conditions pm rest with
     | ParseErr _ -> (None, ts)
     | ParseOk conds rest' -> (Some conds, rest'))
  | _ -> (None, ts)

and parse_order_conditions (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result (list order_condition)) (decreases (List.length ts)) =
  match ts with
  | Tok_ASC :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' ->
          (match parse_order_conditions pm rest'' with
           | ParseErr _ -> ParseOk [OC_Asc e] rest''
           | ParseOk conds rest''' -> ParseOk (OC_Asc e :: conds) rest''')
        | _ -> ParseErr "expected ) after ASC"))
  | Tok_DESC :: Tok_LPAREN :: rest ->
    (match parse_expr pm rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk e rest' ->
       (match rest' with
        | Tok_RPAREN :: rest'' ->
          (match parse_order_conditions pm rest'' with
           | ParseErr _ -> ParseOk [OC_Desc e] rest''
           | ParseOk conds rest''' -> ParseOk (OC_Desc e :: conds) rest''')
        | _ -> ParseErr "expected ) after DESC"))
  | Tok_VAR _ :: _ | Tok_LPAREN :: _ | Tok_IRI _ :: _ | Tok_PNAME _ :: _ ->
    (match parse_expr pm ts with
     | ParseErr _ -> ParseOk [] ts
     | ParseOk e rest ->
       (match parse_order_conditions pm rest with
        | ParseErr _ -> ParseOk [OC_Asc e] rest
        | ParseOk conds rest' -> ParseOk (OC_Asc e :: conds) rest'))
  | _ -> ParseOk [] ts

(* Parse LIMIT *)
and parse_limit (ts : token_stream)
  : Tot (option nat & token_stream) (decreases (List.length ts)) =
  match ts with
  | Tok_LIMIT :: Tok_INTEGER s :: rest ->
    (Some (parse_nat_value s), rest)
  | _ -> (None, ts)

(* Parse OFFSET *)
and parse_offset (ts : token_stream)
  : Tot (option nat & token_stream) (decreases (List.length ts)) =
  match ts with
  | Tok_OFFSET :: Tok_INTEGER s :: rest ->
    (Some (parse_nat_value s), rest)
  | _ -> (None, ts)

(* Parse post-query VALUES *)
and parse_post_values (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (option (list (list (var_name & rdf_term))) & token_stream) (decreases fuel) =
  if fuel = 0 then (None, ts)
  else match ts with
  | Tok_VALUES :: rest ->
    (match parse_inline_data pm (fuel - 1) rest with
     | ParseErr _ -> (None, ts)
     | ParseOk (vars, rows) rest' ->
       let mappings = List.Tot.map (fun row ->
         list_filter_map (fun (pair : (var_name & option rdf_term)) ->
           let (v, t_opt) = pair in
           match t_opt with
           | Some t -> Some (v, t)
           | None -> None
         ) (list_zip vars row)
       ) rows in
       (Some mappings, rest'))
  | _ -> (None, ts)

(* ================================================================== *)
(* Top-level query parsing with prologue                              *)
(* ================================================================== *)

(* Parse PREFIX and BASE declarations *)
and parse_prologue (pm : prefix_map) (ts : token_stream)
  : Tot (parse_result (prefix_map & option string)) (decreases (List.length ts)) =
  match ts with
  | Tok_PREFIX :: rest ->
    (match rest with
     | Tok_PNAME pn :: rest' ->
       (* Extract prefix name from "prefix:" format *)
       let prefix = extract_prefix_name pn in
       (match rest' with
        | Tok_IRI iri :: rest'' ->
          let pm' = (prefix, iri) :: pm in
          parse_prologue pm' rest''
        | _ -> ParseErr "expected IRI after PREFIX name")
     | _ -> ParseErr "expected prefix name after PREFIX")
  | Tok_BASE :: rest ->
    (match rest with
     | Tok_IRI iri :: rest' -> parse_prologue pm rest'  (* TODO: track base *)
     | _ -> ParseErr "expected IRI after BASE")
  | _ -> ParseOk (pm, None) ts

(* Parse a complete SPARQL query string *)
and parse_sparql_query (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result query) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match parse_prologue pm ts with
  | ParseErr msg -> ParseErr msg
  | ParseOk (pm', _base) rest ->
    (match rest with
     | Tok_SELECT :: _ -> parse_select_query pm' (fuel - 1) rest
     | Tok_ASK :: rest' ->
       let rest'' = match rest' with Tok_WHERE :: r -> r | _ -> rest' in
       (match parse_group_graph_pattern pm' (fuel - 1) rest'' with
        | ParseErr msg -> ParseErr msg
        | ParseOk pattern rest''' ->
          ParseOk ({
            q_base = None;
            q_prefixes = pm';
            q_form = QF_Ask;
            q_dataset = [];
            q_pattern = pattern;
            q_group_by = None;
            q_having = None;
            q_modifier = { sm_order_by = None; sm_distinct = false;
                           sm_reduced = false; sm_offset = None; sm_limit = None };
            q_values = None;
          }) rest''')
     | Tok_CONSTRUCT :: rest' ->
       (* CONSTRUCT { template } WHERE { pattern } *)
       (match rest' with
        | Tok_LBRACE :: _ ->
          (* Has explicit template *)
          (match parse_construct_template pm' (fuel - 1) rest' with
           | ParseErr msg -> ParseErr msg
           | ParseOk template rest'' ->
             let rest''' = match rest'' with Tok_WHERE :: r -> r | _ -> rest'' in
             (match parse_group_graph_pattern pm' (fuel - 1) rest''' with
              | ParseErr msg -> ParseErr msg
              | ParseOk pattern rest'''' ->
                ParseOk ({
                  q_base = None;
                  q_prefixes = pm';
                  q_form = QF_Construct template;
                  q_dataset = [];
                  q_pattern = pattern;
                  q_group_by = None;
                  q_having = None;
                  q_modifier = { sm_order_by = None; sm_distinct = false;
                                 sm_reduced = false; sm_offset = None; sm_limit = None };
                  q_values = None;
                }) rest''''))
        | _ ->
          (* CONSTRUCT WHERE form *)
          let rest'' = match rest' with Tok_WHERE :: r -> r | _ -> rest' in
          (match parse_group_graph_pattern pm' (fuel - 1) rest'' with
           | ParseErr msg -> ParseErr msg
           | ParseOk pattern rest''' ->
             ParseOk ({
               q_base = None;
               q_prefixes = pm';
               q_form = QF_Construct [];
               q_dataset = [];
               q_pattern = pattern;
               q_group_by = None;
               q_having = None;
               q_modifier = { sm_order_by = None; sm_distinct = false;
                              sm_reduced = false; sm_offset = None; sm_limit = None };
               q_values = None;
             }) rest'''))
     | _ -> ParseErr "expected SELECT, ASK, or CONSTRUCT")

(* Parse CONSTRUCT template { triples } *)
and parse_construct_template (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (list triple_pattern)) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match ts with
  | Tok_LBRACE :: rest ->
    (match parse_construct_triples pm (fuel - 1) rest with
     | ParseErr msg -> ParseErr msg
     | ParseOk triples rest' ->
       (match rest' with
        | Tok_RBRACE :: rest'' -> ParseOk triples rest''
        | _ -> ParseErr "expected } after CONSTRUCT template"))
  | _ -> ParseErr "expected { for CONSTRUCT template"

and parse_construct_triples (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (list triple_pattern)) (decreases fuel) =
  if fuel = 0 then ParseErr "fuel exhausted"
  else match ts with
  | Tok_RBRACE :: _ -> ParseOk [] ts
  | _ ->
    (match parse_pattern_subject pm (fuel - 1) ts with
     | ParseErr _ -> ParseOk [] ts
     | ParseOk subj rest ->
       (match parse_predicate_object_list pm (fuel - 1) subj rest with
        | ParseErr msg -> ParseErr msg
        | ParseOk pats rest' ->
          let triples = extract_bgp_triples pats in
          let rest'' = match rest' with Tok_DOT :: r -> r | _ -> rest' in
          (match parse_construct_triples pm (fuel - 1) rest'' with
           | ParseErr msg -> ParseErr msg
           | ParseOk more rest''' -> ParseOk (triples @ more) rest''')))

(* ================================================================== *)
(* Helper functions (non-recursive, defined after the mutual block)   *)
(* ================================================================== *)

(* These are placed inside the mutual recursion block for F* scoping  *)

(* Join two patterns with GP_Join, optimizing for GP_Empty *)
and join_patterns (left right : group_graph_pattern)
  : Tot group_graph_pattern (decreases 0) =
  match left with
  | GP_Empty -> right
  | _ -> match right with
    | GP_Empty -> left
    | _ -> GP_Join left right

(* Apply filters to a pattern *)
and apply_filters (pat : group_graph_pattern) (filters : list expr)
  : Tot group_graph_pattern (decreases filters) =
  match filters with
  | [] -> pat
  | f :: rest -> apply_filters (GP_Filter f pat) rest

(* Combine a list of group_graph_patterns into one *)
and combine_patterns (pats : list group_graph_pattern)
  : Tot group_graph_pattern (decreases pats) =
  match pats with
  | [] -> GP_Empty
  | [p] -> p
  | p :: rest -> join_patterns p (combine_patterns rest)

(* Extract BGP triples from a list of patterns (for CONSTRUCT template) *)
and extract_bgp_triples (pats : list group_graph_pattern)
  : Tot (list triple_pattern) (decreases pats) =
  match pats with
  | [] -> []
  | GP_BGP tps :: rest -> tps @ extract_bgp_triples rest
  | _ :: rest -> extract_bgp_triples rest

(* Extract prefix name from "prefix:" format — strips trailing colon *)
and extract_prefix_name (pn : string) : Tot string (decreases 0) =
  (* The prefix name comes as "prefix:" — we need just "prefix" *)
  (* This is handled by split_pname which splits on ':' *)
  let (prefix, _local) = split_pname pn in
  prefix

(* End of mutual recursion block *)

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
