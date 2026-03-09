(* sparql_scanner_stubs.ml — OCaml implementations of SPARQL11.Parser assume vals.
   These are wired into SPARQL11_Parser.ml by ocaml-patches.sh.

   Functions 1-13: scanner/tokenizer stubs (fully implemented)
   Functions 14-16: parser stubs (not yet implemented — needs more F* work) *)

(* NOTE: This file is a reference implementation. The actual stubs are
   injected inline into SPARQL11_Parser.ml by ocaml-patches.sh.
   This file does NOT compile standalone — it documents the implementations.
   The token/pos/etc. types come from SPARQL11_Parser. *)

(* open SPARQL11_Parser -- would create circular dependency *)

(* ======================================================================
   UTF-8 encoding helper
   ====================================================================== *)

let utf8_of_codepoint cp =
  if cp < 0x80 then
    String.make 1 (Char.chr cp)
  else if cp < 0x800 then
    let b0 = 0xC0 lor (cp lsr 6) in
    let b1 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 2 in
    Bytes.set s 0 (Char.chr b0);
    Bytes.set s 1 (Char.chr b1);
    Bytes.to_string s
  else if cp < 0x10000 then
    let b0 = 0xE0 lor (cp lsr 12) in
    let b1 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b2 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 3 in
    Bytes.set s 0 (Char.chr b0);
    Bytes.set s 1 (Char.chr b1);
    Bytes.set s 2 (Char.chr b2);
    Bytes.to_string s
  else if cp < 0x110000 then
    let b0 = 0xF0 lor (cp lsr 18) in
    let b1 = 0x80 lor ((cp lsr 12) land 0x3F) in
    let b2 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b3 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 4 in
    Bytes.set s 0 (Char.chr b0);
    Bytes.set s 1 (Char.chr b1);
    Bytes.set s 2 (Char.chr b2);
    Bytes.set s 3 (Char.chr b3);
    Bytes.to_string s
  else
    failwith (Printf.sprintf "Invalid Unicode codepoint: U+%06X" cp)

(* ======================================================================
   1. char_at : string -> pos -> FStar.Char.char
   ====================================================================== *)

let char_at_impl (s : Prims.string) (p : pos) : FStar_Char.char =
  let p_int = Z.to_int p in
  if p_int >= String.length s then 0
  else Char.code s.[p_int]

(* ======================================================================
   2. substring : string -> pos -> nat -> string
   ====================================================================== *)

let substring_impl (s : Prims.string) (p : pos) (len : Prims.nat) : Prims.string =
  let p_int = Z.to_int p in
  let len_int = Z.to_int len in
  let slen = String.length s in
  if p_int >= slen then ""
  else
    let actual_len = min len_int (slen - p_int) in
    String.sub s p_int actual_len

(* ======================================================================
   3. string_upper : string -> string
   ====================================================================== *)

let string_upper_impl (s : Prims.string) : Prims.string =
  String.uppercase_ascii s

(* ======================================================================
   4. scan_iri : string -> pos -> (string & pos)
      Scans IRI content after '<' has been consumed. Reads until '>'.
      Handles \uXXXX and \UXXXXXXXX escapes.
   ====================================================================== *)

let scan_iri_impl (input : Prims.string) (p : pos) : (Prims.string * pos) =
  let len = String.length input in
  let buf = Buffer.create 64 in
  let i = ref (Z.to_int p) in
  let found = ref false in
  while !i < len && not !found do
    let c = input.[!i] in
    if c = '>' then
      (found := true; i := !i + 1)
    else if c = '\\' && !i + 1 < len then begin
      let next = input.[!i + 1] in
      if next = 'u' && !i + 5 < len then begin
        let hex = String.sub input (!i + 2) 4 in
        let cp = int_of_string ("0x" ^ hex) in
        Buffer.add_string buf (utf8_of_codepoint cp);
        i := !i + 6
      end else if next = 'U' && !i + 9 < len then begin
        let hex = String.sub input (!i + 2) 8 in
        let cp = int_of_string ("0x" ^ hex) in
        Buffer.add_string buf (utf8_of_codepoint cp);
        i := !i + 10
      end else begin
        Buffer.add_char buf c;
        i := !i + 1
      end
    end else begin
      Buffer.add_char buf c;
      i := !i + 1
    end
  done;
  (Buffer.contents buf, Z.of_int !i)

(* ======================================================================
   5. scan_string : string -> pos -> (string & pos)
      Scans a string literal starting at the quote character.
      Handles single/double quotes, short and long (triple-quoted) strings.
      Handles escape sequences: tab, backspace, newline, return, formfeed,
      double-quote, single-quote, backslash, uXXXX, UXXXXXXXX
   ====================================================================== *)

let scan_string_impl (input : Prims.string) (p : pos) : (Prims.string * pos) =
  let len = String.length input in
  let i = ref (Z.to_int p) in
  if !i >= len then ("", p)
  else begin
    let q = input.[!i] in
    i := !i + 1;
    (* Check for long string (triple-quoted) *)
    let is_long =
      !i + 1 < len && input.[!i] = q && input.[!i + 1] = q in
    if is_long then begin
      i := !i + 2; (* skip two more quotes *)
      let buf = Buffer.create 128 in
      let found = ref false in
      while !i < len && not !found do
        if input.[!i] = q && !i + 2 < len &&
           input.[!i + 1] = q && input.[!i + 2] = q then begin
          found := true;
          i := !i + 3
        end else if input.[!i] = '\\' && !i + 1 < len then begin
          i := !i + 1;
          let esc = input.[!i] in
          (match esc with
           | 't' -> Buffer.add_char buf '\t'; i := !i + 1
           | 'b' -> Buffer.add_char buf '\b'; i := !i + 1
           | 'n' -> Buffer.add_char buf '\n'; i := !i + 1
           | 'r' -> Buffer.add_char buf '\r'; i := !i + 1
           | 'f' -> Buffer.add_char buf (Char.chr 0x0C); i := !i + 1
           | '"' -> Buffer.add_char buf '"'; i := !i + 1
           | '\'' -> Buffer.add_char buf '\''; i := !i + 1
           | '\\' -> Buffer.add_char buf '\\'; i := !i + 1
           | 'u' when !i + 4 < len ->
             let hex = String.sub input (!i + 1) 4 in
             let cp = int_of_string ("0x" ^ hex) in
             Buffer.add_string buf (utf8_of_codepoint cp);
             i := !i + 5
           | 'U' when !i + 8 < len ->
             let hex = String.sub input (!i + 1) 8 in
             let cp = int_of_string ("0x" ^ hex) in
             Buffer.add_string buf (utf8_of_codepoint cp);
             i := !i + 9
           | _ -> Buffer.add_char buf '\\'; Buffer.add_char buf esc; i := !i + 1)
        end else begin
          Buffer.add_char buf input.[!i];
          i := !i + 1
        end
      done;
      (Buffer.contents buf, Z.of_int !i)
    end else begin
      (* Short string *)
      let buf = Buffer.create 64 in
      let found = ref false in
      while !i < len && not !found do
        let c = input.[!i] in
        if c = q then begin
          found := true;
          i := !i + 1
        end else if c = '\\' && !i + 1 < len then begin
          i := !i + 1;
          let esc = input.[!i] in
          (match esc with
           | 't' -> Buffer.add_char buf '\t'; i := !i + 1
           | 'b' -> Buffer.add_char buf '\b'; i := !i + 1
           | 'n' -> Buffer.add_char buf '\n'; i := !i + 1
           | 'r' -> Buffer.add_char buf '\r'; i := !i + 1
           | 'f' -> Buffer.add_char buf (Char.chr 0x0C); i := !i + 1
           | '"' -> Buffer.add_char buf '"'; i := !i + 1
           | '\'' -> Buffer.add_char buf '\''; i := !i + 1
           | '\\' -> Buffer.add_char buf '\\'; i := !i + 1
           | 'u' when !i + 4 < len ->
             let hex = String.sub input (!i + 1) 4 in
             let cp = int_of_string ("0x" ^ hex) in
             Buffer.add_string buf (utf8_of_codepoint cp);
             i := !i + 5
           | 'U' when !i + 8 < len ->
             let hex = String.sub input (!i + 1) 8 in
             let cp = int_of_string ("0x" ^ hex) in
             Buffer.add_string buf (utf8_of_codepoint cp);
             i := !i + 9
           | _ -> Buffer.add_char buf '\\'; Buffer.add_char buf esc; i := !i + 1)
        end else begin
          Buffer.add_char buf c;
          i := !i + 1
        end
      done;
      (Buffer.contents buf, Z.of_int !i)
    end
  end

(* ======================================================================
   Helper: classify a byte as a PN_CHARS-like character
   ====================================================================== *)

let is_pn_char_byte c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
  (c >= '0' && c <= '9') || c = '_' || c = '-' || c = '.' ||
  Char.code c >= 0x80

let is_alpha_byte c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

let is_digit_byte c = c >= '0' && c <= '9'

let is_alnum_byte c = is_alpha_byte c || is_digit_byte c

(* PN_LOCAL_ESC valid chars: _~.-!$&' parens star +,;=/?#@% *)
let is_pn_local_esc_byte c =
  c = '_' || c = '~' || c = '.' || c = '-' || c = '!' || c = '$' || c = '&' ||
  c = '\'' || c = '(' || c = ')' || c = '*' || c = '+' || c = ',' || c = ';' ||
  c = '=' || c = '/' || c = '?' || c = '#' || c = '@' || c = '%'

(* ======================================================================
   6. scan_pname_or_keyword : string -> pos -> lex_result
      Scans a prefixed name (foo:bar) or keyword (SELECT, WHERE, etc.)
      Starting at the first character of the name.
   ====================================================================== *)

let scan_pname_or_keyword_impl (input : Prims.string) (p : pos) : lex_result =
  let len = String.length input in
  let i = ref (Z.to_int p) in
  (* Read prefix/keyword part: PN_CHARS *)
  while !i < len && is_pn_char_byte input.[!i] do i := !i + 1 done;
  (* Check for colon (prefixed name) *)
  if !i < len && input.[!i] = ':' then begin
    i := !i + 1;
    (* Read local part: PN_CHARS, colon, percent, backslash *)
    while !i < len &&
          let c = input.[!i] in
          is_pn_char_byte c || c = ':' || c = '%' || c = '\\' do
      if input.[!i] = '\\' then begin
        i := !i + 1;
        if !i < len && is_pn_local_esc_byte input.[!i] then
          i := !i + 1
        (* else: invalid escape, stop *)
      end else
        i := !i + 1
    done;
    (* Remove trailing dots from local part *)
    while !i > Z.to_int p && input.[!i - 1] = '.' do i := !i - 1 done;
    let pname = String.sub input (Z.to_int p) (!i - Z.to_int p) in
    (Tok_PNAME pname, Z.of_int !i)
  end else begin
    let word = String.sub input (Z.to_int p) (!i - Z.to_int p) in
    let upper = String.uppercase_ascii word in
    let tok = match upper with
      | "SELECT" -> Tok_SELECT | "ASK" -> Tok_ASK | "CONSTRUCT" -> Tok_CONSTRUCT
      | "DESCRIBE" -> Tok_DESCRIBE
      | "WHERE" -> Tok_WHERE | "PREFIX" -> Tok_PREFIX | "BASE" -> Tok_BASE
      | "OPTIONAL" -> Tok_OPTIONAL | "UNION" -> Tok_UNION | "MINUS" -> Tok_MINUS_KW
      | "FILTER" -> Tok_FILTER | "BIND" -> Tok_BIND | "VALUES" -> Tok_VALUES
      | "GRAPH" -> Tok_GRAPH | "SERVICE" -> Tok_SERVICE | "SILENT" -> Tok_SILENT
      | "EXISTS" -> Tok_EXISTS | "NOT" -> Tok_NOT
      | "AS" -> Tok_AS | "DISTINCT" -> Tok_DISTINCT | "REDUCED" -> Tok_REDUCED
      | "ORDER" -> Tok_ORDER | "BY" -> Tok_BY | "ASC" -> Tok_ASC | "DESC" -> Tok_DESC
      | "GROUP" -> Tok_GROUP | "HAVING" -> Tok_HAVING
      | "LIMIT" -> Tok_LIMIT | "OFFSET" -> Tok_OFFSET
      | "IN" -> Tok_IN | "TRUE" -> Tok_TRUE | "FALSE" -> Tok_FALSE | "UNDEF" -> Tok_UNDEF
      | "A" -> Tok_A
      | "STR" -> Tok_STR | "LANG" -> Tok_LANG | "LANGMATCHES" -> Tok_LANGMATCHES
      | "DATATYPE" -> Tok_DATATYPE | "BOUND" -> Tok_BOUND | "IF" -> Tok_IF
      | "IRI" -> Tok_IRI_KW | "URI" -> Tok_URI
      | "BNODE" -> Tok_BNODE_KW | "RAND" -> Tok_RAND
      | "ABS" -> Tok_ABS | "CEIL" -> Tok_CEIL | "FLOOR" -> Tok_FLOOR | "ROUND" -> Tok_ROUND
      | "CONCAT" -> Tok_CONCAT | "STRLEN" -> Tok_STRLEN
      | "UCASE" -> Tok_UCASE | "LCASE" -> Tok_LCASE
      | "ENCODE_FOR_URI" -> Tok_ENCODE_FOR_URI
      | "CONTAINS" -> Tok_CONTAINS | "STRSTARTS" -> Tok_STRSTARTS | "STRENDS" -> Tok_STRENDS
      | "STRBEFORE" -> Tok_STRBEFORE | "STRAFTER" -> Tok_STRAFTER
      | "REPLACE" -> Tok_REPLACE | "REGEX" -> Tok_REGEX
      | "SUBSTR" -> Tok_SUBSTR
      | "ISIRI" -> Tok_ISIRI | "ISURI" -> Tok_ISIRI  (* ISURI = ISIRI *)
      | "ISBLANK" -> Tok_ISBLANK
      | "ISLITERAL" -> Tok_ISLITERAL | "ISNUMERIC" -> Tok_ISNUMERIC
      | "SAMETERM" -> Tok_SAMETERM | "STRDT" -> Tok_STRDT | "STRLANG" -> Tok_STRLANG
      | "COUNT" -> Tok_COUNT | "SUM" -> Tok_SUM
      | "MIN" -> Tok_MIN_KW | "MAX" -> Tok_MAX_KW | "AVG" -> Tok_AVG
      | "GROUP_CONCAT" -> Tok_GROUP_CONCAT | "SAMPLE" -> Tok_SAMPLE
      | "SEPARATOR" -> Tok_SEPARATOR
      | "COALESCE" -> Tok_COALESCE | "NOW" -> Tok_NOW
      | "UUID" -> Tok_UUID | "STRUUID" -> Tok_STRUUID
      | "YEAR" -> Tok_YEAR | "MONTH" -> Tok_MONTH | "DAY" -> Tok_DAY
      | "HOURS" -> Tok_HOURS | "MINUTES" -> Tok_MINUTES | "SECONDS" -> Tok_SECONDS
      | "TIMEZONE" -> Tok_TIMEZONE | "TZ" -> Tok_TZ
      | "MD5" -> Tok_MD5 | "SHA1" -> Tok_SHA1 | "SHA256" -> Tok_SHA256
      | "SHA384" -> Tok_SHA384 | "SHA512" -> Tok_SHA512
      | _ -> Tok_PNAME word  (* unrecognized keyword treated as pname *)
    in
    (tok, Z.of_int !i)
  end

(* ======================================================================
   7. scan_number : string -> pos -> lex_result
      Scans an integer, decimal, or double literal.
   ====================================================================== *)

let scan_number_impl (input : Prims.string) (p : pos) : lex_result =
  let len = String.length input in
  let i = ref (Z.to_int p) in
  (* Optional sign *)
  if !i < len && (input.[!i] = '+' || input.[!i] = '-') then i := !i + 1;
  (* Integer digits *)
  while !i < len && is_digit_byte input.[!i] do i := !i + 1 done;
  (* Check for decimal point *)
  let has_dot =
    !i < len && input.[!i] = '.' &&
    !i + 1 < len && is_digit_byte input.[!i + 1] in
  if has_dot then begin
    i := !i + 1;
    while !i < len && is_digit_byte input.[!i] do i := !i + 1 done
  end;
  (* Check for exponent *)
  let has_exp = !i < len && (input.[!i] = 'e' || input.[!i] = 'E') in
  if has_exp then begin
    i := !i + 1;
    if !i < len && (input.[!i] = '+' || input.[!i] = '-') then i := !i + 1;
    while !i < len && is_digit_byte input.[!i] do i := !i + 1 done
  end;
  let text = String.sub input (Z.to_int p) (!i - Z.to_int p) in
  let tok =
    if has_exp then Tok_DOUBLE text
    else if has_dot then Tok_DECIMAL text
    else Tok_INTEGER text in
  (tok, Z.of_int !i)

(* ======================================================================
   8. scan_bnode_label : string -> pos -> (string & pos)
      Scans blank node label after '_:' has been consumed.
   ====================================================================== *)

let scan_bnode_label_impl (input : Prims.string) (p : pos) : (Prims.string * pos) =
  let len = String.length input in
  let i = ref (Z.to_int p) in
  (* First char must be PN_CHARS_U or digit *)
  if !i < len && (is_alnum_byte input.[!i] || input.[!i] = '_' ||
                   Char.code input.[!i] >= 0x80) then begin
    i := !i + 1;
    (* Subsequent chars: PN_CHARS or '.' (but not trailing '.') *)
    while !i < len && (is_pn_char_byte input.[!i]) do i := !i + 1 done;
    (* Remove trailing dots *)
    while !i > Z.to_int p && input.[!i - 1] = '.' do i := !i - 1 done
  end;
  let label = String.sub input (Z.to_int p) (!i - Z.to_int p) in
  (label, Z.of_int !i)

(* ======================================================================
   9. scan_var_name : string -> pos -> (string & pos)
      Scans variable name after '?' or '$' has been consumed.
   ====================================================================== *)

let scan_var_name_impl (input : Prims.string) (p : pos) : (Prims.string * pos) =
  let len = String.length input in
  let i = ref (Z.to_int p) in
  while !i < len && (is_alnum_byte input.[!i] || input.[!i] = '_') do
    i := !i + 1
  done;
  let name = String.sub input (Z.to_int p) (!i - Z.to_int p) in
  (name, Z.of_int !i)

(* ======================================================================
   10. scan_langtag : string -> pos -> (string & pos)
       Scans language tag after '@' has been consumed.
   ====================================================================== *)

let scan_langtag_impl (input : Prims.string) (p : pos) : (Prims.string * pos) =
  let len = String.length input in
  let i = ref (Z.to_int p) in
  while !i < len && (is_alnum_byte input.[!i] || input.[!i] = '-') do
    i := !i + 1
  done;
  let tag = String.sub input (Z.to_int p) (!i - Z.to_int p) in
  (tag, Z.of_int !i)

(* ======================================================================
   11. tokenize : string -> list token
       Tokenizes entire input using next_token repeatedly.
   ====================================================================== *)

let tokenize_impl (input : Prims.string) : token Prims.list =
  let tokens = ref [] in
  let p = ref Z.zero in
  let finished = ref false in
  while not !finished do
    let (tok, p') = next_token input !p in
    (match tok with
     | Tok_EOF -> finished := true
     | _ -> tokens := tok :: !tokens);
    (* Guard against no progress *)
    if Z.leq p' !p then finished := true
    else p := p'
  done;
  List.rev !tokens

(* ======================================================================
   12. token_eq : token -> token -> bool
       Structural equality on tokens.
   ====================================================================== *)

let token_eq_impl (a : token) (b : token) : Prims.bool =
  a = b

(* ======================================================================
   13. split_pname : string -> (string & string)
       Splits "prefix:local" into ("prefix", "local").
       If no colon, returns ("", whole_string).
   ====================================================================== *)

let split_pname_impl (pn : Prims.string) : (Prims.string * Prims.string) =
  match String.index_opt pn ':' with
  | Some idx ->
    let prefix = String.sub pn 0 idx in
    let local = String.sub pn (idx + 1) (String.length pn - idx - 1) in
    (prefix, local)
  | None -> ("", pn)

(* ======================================================================
   14-16. Parser functions (not yet implemented — needs F* work)
   ====================================================================== *)

let parse_expr_impl (_pm : prefix_map) (_ts : token_stream) :
  SPARQL11_Algebra.expr parse_result =
  ParseErr "parse_expr: not yet implemented (needs F* parser work)"

let parse_group_graph_pattern_impl (_pm : prefix_map) (_fuel : Prims.nat)
    (_ts : token_stream) :
  SPARQL11_Algebra.group_graph_pattern parse_result =
  ParseErr "parse_group_graph_pattern: not yet implemented (needs F* parser work)"

let parse_select_query_impl (_pm : prefix_map) (_fuel : Prims.nat)
    (_ts : token_stream) : SPARQL11_Algebra.query parse_result =
  ParseErr "parse_select_query: not yet implemented (needs F* parser work)"
