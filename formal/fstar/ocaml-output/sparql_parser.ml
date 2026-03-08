(* SPARQL 1.1 query parser — UNVERIFIED TEST INFRASTRUCTURE.
   Not extracted from F*. Hand-written OCaml for parsing W3C .rq files
   into the F*-extracted SPARQL11_Algebra.query type.

   This is test glue, not the product. It will be replaced by a verified
   parser (EverParse-style) in Phase 3. *)

open RDF_Graph_Executable
open SPARQL11_Algebra

exception Parse_error of string
exception Unsupported of string

(* ============================================================================
   Lexer
   ============================================================================ *)

type token =
  | T_SELECT | T_ASK | T_CONSTRUCT | T_DESCRIBE
  | T_WHERE | T_PREFIX | T_BASE
  | T_OPTIONAL | T_UNION | T_MINUS | T_FILTER | T_BIND | T_VALUES
  | T_GRAPH | T_SERVICE | T_SILENT
  | T_EXISTS | T_NOT
  | T_AS | T_DISTINCT | T_REDUCED | T_STAR
  | T_ORDER | T_BY | T_ASC | T_DESC
  | T_GROUP | T_HAVING
  | T_LIMIT | T_OFFSET
  | T_IN | T_TRUE | T_FALSE | T_UNDEF
  | T_LBRACE | T_RBRACE | T_LPAREN | T_RPAREN | T_DOT | T_SEMI | T_COMMA
  | T_LBRACKET | T_RBRACKET
  | T_CARET | T_SLASH | T_PIPE | T_BANG | T_QMARK
  | T_PLUS | T_MINUS_OP | T_TIMES | T_DIVIDE
  | T_EQ | T_NE | T_LT | T_GT | T_LE | T_GE
  | T_AND | T_OR
  | T_HATHAT  (* ^^ *)
  | T_IRI of string
  | T_PNAME of string  (* prefixed name before expansion *)
  | T_VAR of string
  | T_STRING of string
  | T_LANGTAG of string  (* @en etc *)
  | T_INTEGER of string
  | T_DECIMAL of string
  | T_DOUBLE of string
  | T_BNODE of string   (* _:label *)
  | T_ANON              (* [] *)
  | T_A                 (* 'a' keyword = rdf:type *)
  | T_EOF
  (* Built-in function keywords *)
  | T_STR_KW | T_LANG | T_LANGMATCHES | T_DATATYPE | T_BOUND | T_IF
  | T_IRI_KW | T_URI | T_BNODE_KW | T_RAND
  | T_ABS | T_CEIL | T_FLOOR | T_ROUND
  | T_CONCAT | T_STRLEN | T_UCASE | T_LCASE
  | T_ENCODE_FOR_URI | T_CONTAINS | T_STRSTARTS | T_STRENDS
  | T_STRBEFORE | T_STRAFTER | T_REPLACE | T_REGEX
  | T_SUBSTR | T_SUBSTRING
  | T_ISIRI | T_ISURI | T_ISBLANK | T_ISLITERAL | T_ISNUMERIC
  | T_SAMETERM | T_STRDT | T_STRLANG
  | T_COUNT | T_SUM | T_MIN_KW | T_MAX_KW | T_AVG | T_GROUP_CONCAT | T_SAMPLE
  | T_SEPARATOR
  | T_COALESCE | T_NOW | T_UUID | T_STRUUID
  | T_YEAR | T_MONTH | T_DAY | T_HOURS | T_MINUTES | T_SECONDS
  | T_TIMEZONE | T_TZ
  | T_MD5 | T_SHA1 | T_SHA256 | T_SHA384 | T_SHA512

type lexer = {
  input : string;
  mutable pos : int;
}

let make_lexer input = { input; pos = 0 }
let lex_at_end lx = lx.pos >= String.length lx.input
let lex_peek lx = if lx.pos < String.length lx.input then lx.input.[lx.pos] else '\x00'
let lex_advance lx = let c = lx.input.[lx.pos] in lx.pos <- lx.pos + 1; c

let lex_skip_ws lx =
  let rec loop () =
    if not (lex_at_end lx) then
      let c = lex_peek lx in
      if c = ' ' || c = '\t' || c = '\n' || c = '\r' then
        (lx.pos <- lx.pos + 1; loop ())
      else if c = '#' then begin
        while not (lex_at_end lx) && lex_peek lx <> '\n' do lx.pos <- lx.pos + 1 done;
        loop ()
      end
  in loop ()

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let is_digit c = c >= '0' && c <= '9'
let is_alnum c = is_alpha c || is_digit c
let is_pn_char c = is_alnum c || c = '_' || c = '-' || c = '.' || Char.code c >= 0x80

let lex_iri lx =
  lx.pos <- lx.pos + 1; (* skip < *)
  let buf = Buffer.create 64 in
  let rec loop () =
    if lex_at_end lx then raise (Parse_error "Unterminated IRI");
    let c = lex_advance lx in
    if c = '>' then Buffer.contents buf
    else if c = '\\' then begin
      let e = lex_advance lx in
      if e = 'u' then begin
        let hex = String.init 4 (fun _ -> lex_advance lx) in
        let cp = int_of_string ("0x" ^ hex) in
        Buffer.add_string buf (Ntriples_parser.utf8_of_codepoint cp)
      end else if e = 'U' then begin
        let hex = String.init 8 (fun _ -> lex_advance lx) in
        let cp = int_of_string ("0x" ^ hex) in
        Buffer.add_string buf (Ntriples_parser.utf8_of_codepoint cp)
      end else raise (Parse_error "Invalid IRI escape");
      loop ()
    end else (Buffer.add_char buf c; loop ())
  in loop ()

let rec lex_string lx =
  let q = lex_advance lx in
  (* Check for long string *)
  let is_long =
    not (lex_at_end lx) && lex_peek lx = q &&
    lx.pos + 1 < String.length lx.input && lx.input.[lx.pos + 1] = q in
  if is_long then begin
    lx.pos <- lx.pos + 2; (* skip two more quotes *)
    let buf = Buffer.create 128 in
    let rec loop () =
      if lex_at_end lx then raise (Parse_error "Unterminated long string");
      if lex_peek lx = q &&
         lx.pos + 1 < String.length lx.input && lx.input.[lx.pos + 1] = q &&
         lx.pos + 2 < String.length lx.input && lx.input.[lx.pos + 2] = q then
        (lx.pos <- lx.pos + 3; Buffer.contents buf)
      else if lex_peek lx = '\\' then begin
        lx.pos <- lx.pos + 1;
        Buffer.add_string buf (lex_string_escape lx);
        loop ()
      end else
        (Buffer.add_char buf (lex_advance lx); loop ())
    in loop ()
  end else begin
    let buf = Buffer.create 64 in
    let rec loop () =
      if lex_at_end lx then raise (Parse_error "Unterminated string");
      let c = lex_advance lx in
      if c = q then Buffer.contents buf
      else if c = '\\' then (Buffer.add_string buf (lex_string_escape lx); loop ())
      else (Buffer.add_char buf c; loop ())
    in loop ()
  end

and lex_string_escape lx =
  let c = lex_advance lx in
  match c with
  | 't' -> "\t" | 'b' -> "\b" | 'n' -> "\n" | 'r' -> "\r"
  | 'f' -> String.make 1 (Char.chr 0x0C)
  | '"' -> "\"" | '\'' -> "'" | '\\' -> "\\"
  | 'u' ->
    let hex = String.init 4 (fun _ -> lex_advance lx) in
    Ntriples_parser.utf8_of_codepoint (int_of_string ("0x" ^ hex))
  | 'U' ->
    let hex = String.init 8 (fun _ -> lex_advance lx) in
    Ntriples_parser.utf8_of_codepoint (int_of_string ("0x" ^ hex))
  | _ -> raise (Parse_error (Printf.sprintf "Invalid escape: \\%c" c))

let lex_pname_or_keyword lx =
  let start = lx.pos in
  (* Read prefix part *)
  while not (lex_at_end lx) && is_pn_char (lex_peek lx) do lx.pos <- lx.pos + 1 done;
  (* Check for colon (prefixed name) *)
  if not (lex_at_end lx) && lex_peek lx = ':' then begin
    lx.pos <- lx.pos + 1;
    (* Read local part *)
    while not (lex_at_end lx) &&
          let c = lex_peek lx in
          is_pn_char c || c = ':' || c = '%' || c = '\\' do
      if lex_peek lx = '\\' then
        (lx.pos <- lx.pos + 2)  (* skip escaped char *)
      else
        lx.pos <- lx.pos + 1
    done;
    (* Remove trailing dots from the local part *)
    while lx.pos > start && lx.input.[lx.pos - 1] = '.' do lx.pos <- lx.pos - 1 done;
    T_PNAME (String.sub lx.input start (lx.pos - start))
  end else begin
    let word = String.sub lx.input start (lx.pos - start) in
    let upper = String.uppercase_ascii word in
    match upper with
    | "SELECT" -> T_SELECT | "ASK" -> T_ASK | "CONSTRUCT" -> T_CONSTRUCT
    | "DESCRIBE" -> T_DESCRIBE
    | "WHERE" -> T_WHERE | "PREFIX" -> T_PREFIX | "BASE" -> T_BASE
    | "OPTIONAL" -> T_OPTIONAL | "UNION" -> T_UNION | "MINUS" -> T_MINUS
    | "FILTER" -> T_FILTER | "BIND" -> T_BIND | "VALUES" -> T_VALUES
    | "GRAPH" -> T_GRAPH | "SERVICE" -> T_SERVICE | "SILENT" -> T_SILENT
    | "EXISTS" -> T_EXISTS | "NOT" -> T_NOT
    | "AS" -> T_AS | "DISTINCT" -> T_DISTINCT | "REDUCED" -> T_REDUCED
    | "ORDER" -> T_ORDER | "BY" -> T_BY | "ASC" -> T_ASC | "DESC" -> T_DESC
    | "GROUP" -> T_GROUP | "HAVING" -> T_HAVING
    | "LIMIT" -> T_LIMIT | "OFFSET" -> T_OFFSET
    | "IN" -> T_IN | "TRUE" -> T_TRUE | "FALSE" -> T_FALSE | "UNDEF" -> T_UNDEF
    | "A" -> T_A
    | "STR" -> T_STR_KW | "LANG" -> T_LANG | "LANGMATCHES" -> T_LANGMATCHES
    | "DATATYPE" -> T_DATATYPE | "BOUND" -> T_BOUND | "IF" -> T_IF
    | "IRI" -> T_IRI_KW | "URI" -> T_URI
    | "BNODE" -> T_BNODE_KW | "RAND" -> T_RAND
    | "ABS" -> T_ABS | "CEIL" -> T_CEIL | "FLOOR" -> T_FLOOR | "ROUND" -> T_ROUND
    | "CONCAT" -> T_CONCAT | "STRLEN" -> T_STRLEN
    | "UCASE" -> T_UCASE | "LCASE" -> T_LCASE
    | "ENCODE_FOR_URI" -> T_ENCODE_FOR_URI
    | "CONTAINS" -> T_CONTAINS | "STRSTARTS" -> T_STRSTARTS | "STRENDS" -> T_STRENDS
    | "STRBEFORE" -> T_STRBEFORE | "STRAFTER" -> T_STRAFTER
    | "REPLACE" -> T_REPLACE | "REGEX" -> T_REGEX
    | "SUBSTR" -> T_SUBSTR | "SUBSTRING" -> T_SUBSTRING
    | "ISIRI" -> T_ISIRI | "ISURI" -> T_ISURI | "ISBLANK" -> T_ISBLANK
    | "ISLITERAL" -> T_ISLITERAL | "ISNUMERIC" -> T_ISNUMERIC
    | "SAMETERM" -> T_SAMETERM | "STRDT" -> T_STRDT | "STRLANG" -> T_STRLANG
    | "COUNT" -> T_COUNT | "SUM" -> T_SUM
    | "MIN" -> T_MIN_KW | "MAX" -> T_MAX_KW | "AVG" -> T_AVG
    | "GROUP_CONCAT" -> T_GROUP_CONCAT | "SAMPLE" -> T_SAMPLE
    | "SEPARATOR" -> T_SEPARATOR
    | "COALESCE" -> T_COALESCE | "NOW" -> T_NOW
    | "UUID" -> T_UUID | "STRUUID" -> T_STRUUID
    | "YEAR" -> T_YEAR | "MONTH" -> T_MONTH | "DAY" -> T_DAY
    | "HOURS" -> T_HOURS | "MINUTES" -> T_MINUTES | "SECONDS" -> T_SECONDS
    | "TIMEZONE" -> T_TIMEZONE | "TZ" -> T_TZ
    | "MD5" -> T_MD5 | "SHA1" -> T_SHA1 | "SHA256" -> T_SHA256
    | "SHA384" -> T_SHA384 | "SHA512" -> T_SHA512
    | _ ->
      (* Could be a prefixed name with no colon yet — check if next is : *)
      T_PNAME word  (* will fail at resolve time if not a valid prefix *)
  end

let lex_number lx =
  let start = lx.pos in
  if lex_peek lx = '+' || lex_peek lx = '-' then lx.pos <- lx.pos + 1;
  while not (lex_at_end lx) && is_digit (lex_peek lx) do lx.pos <- lx.pos + 1 done;
  let has_dot = not (lex_at_end lx) && lex_peek lx = '.' &&
                lx.pos + 1 < String.length lx.input && is_digit lx.input.[lx.pos + 1] in
  if has_dot then begin
    lx.pos <- lx.pos + 1;
    while not (lex_at_end lx) && is_digit (lex_peek lx) do lx.pos <- lx.pos + 1 done
  end;
  let has_exp = not (lex_at_end lx) && (lex_peek lx = 'e' || lex_peek lx = 'E') in
  if has_exp then begin
    lx.pos <- lx.pos + 1;
    if not (lex_at_end lx) && (lex_peek lx = '+' || lex_peek lx = '-') then
      lx.pos <- lx.pos + 1;
    while not (lex_at_end lx) && is_digit (lex_peek lx) do lx.pos <- lx.pos + 1 done
  end;
  let text = String.sub lx.input start (lx.pos - start) in
  if has_exp then T_DOUBLE text
  else if has_dot then T_DECIMAL text
  else T_INTEGER text

let next_token lx =
  lex_skip_ws lx;
  if lex_at_end lx then T_EOF
  else
    let c = lex_peek lx in
    match c with
    | '<' ->
      if lx.pos + 1 < String.length lx.input && lx.input.[lx.pos + 1] = '=' then
        (lx.pos <- lx.pos + 2; T_LE)
      else begin
        (* Distinguish < (less-than) from <IRI>.
           IRIs start with a scheme (letter) or are relative; they never start
           with whitespace, digit, or end-of-input right after <. *)
        let next_ch = if lx.pos + 1 < String.length lx.input
                      then lx.input.[lx.pos + 1] else ' ' in
        if next_ch = ' ' || next_ch = '\t' || next_ch = '\n' || next_ch = '\r'
           || (next_ch >= '0' && next_ch <= '9') || next_ch = '-' then
          (lx.pos <- lx.pos + 1; T_LT)
        else T_IRI (lex_iri lx)
      end
    | '>' ->
      lx.pos <- lx.pos + 1;
      if not (lex_at_end lx) && lex_peek lx = '=' then (lx.pos <- lx.pos + 1; T_GE)
      else T_GT
    | '{' -> lx.pos <- lx.pos + 1; T_LBRACE
    | '}' -> lx.pos <- lx.pos + 1; T_RBRACE
    | '(' -> lx.pos <- lx.pos + 1; T_LPAREN
    | ')' -> lx.pos <- lx.pos + 1; T_RPAREN
    | '[' ->
      (* Check for [] = anonymous blank node *)
      let save = lx.pos in
      lx.pos <- lx.pos + 1;
      lex_skip_ws lx;
      if not (lex_at_end lx) && lex_peek lx = ']' then
        (lx.pos <- lx.pos + 1; T_ANON)
      else
        (lx.pos <- save + 1; T_LBRACKET)
    | ']' -> lx.pos <- lx.pos + 1; T_RBRACKET
    | '.' -> lx.pos <- lx.pos + 1; T_DOT
    | ';' -> lx.pos <- lx.pos + 1; T_SEMI
    | ',' -> lx.pos <- lx.pos + 1; T_COMMA
    | '*' -> lx.pos <- lx.pos + 1; T_STAR
    | '/' -> lx.pos <- lx.pos + 1; T_SLASH
    | '|' ->
      lx.pos <- lx.pos + 1;
      if not (lex_at_end lx) && lex_peek lx = '|' then (lx.pos <- lx.pos + 1; T_OR)
      else T_PIPE
    | '^' ->
      lx.pos <- lx.pos + 1;
      if not (lex_at_end lx) && lex_peek lx = '^' then (lx.pos <- lx.pos + 1; T_HATHAT)
      else T_CARET
    | '!' ->
      lx.pos <- lx.pos + 1;
      if not (lex_at_end lx) && lex_peek lx = '=' then (lx.pos <- lx.pos + 1; T_NE)
      else T_BANG
    | '?' | '$' ->
      lx.pos <- lx.pos + 1;
      let start = lx.pos in
      while not (lex_at_end lx) && (is_alnum (lex_peek lx) || lex_peek lx = '_') do
        lx.pos <- lx.pos + 1
      done;
      if lx.pos = start then
        (* '?' not followed by a variable name — this is the path modifier '?' *)
        T_QMARK
      else
        T_VAR (String.sub lx.input start (lx.pos - start))
    | '"' | '\'' -> T_STRING (lex_string lx)
    | '@' ->
      lx.pos <- lx.pos + 1;
      let start = lx.pos in
      while not (lex_at_end lx) && (is_alnum (lex_peek lx) || lex_peek lx = '-') do
        lx.pos <- lx.pos + 1
      done;
      T_LANGTAG (String.sub lx.input start (lx.pos - start))
    | '+' -> lx.pos <- lx.pos + 1; T_PLUS
    | '-' -> lx.pos <- lx.pos + 1; T_MINUS_OP
    | '=' -> lx.pos <- lx.pos + 1; T_EQ
    | '&' ->
      lx.pos <- lx.pos + 1;
      if not (lex_at_end lx) && lex_peek lx = '&' then (lx.pos <- lx.pos + 1; T_AND)
      else raise (Parse_error "Expected &&")
    | '_' ->
      if lx.pos + 1 < String.length lx.input && lx.input.[lx.pos + 1] = ':' then begin
        lx.pos <- lx.pos + 2;
        let start = lx.pos in
        while not (lex_at_end lx) && (is_pn_char (lex_peek lx) || lex_peek lx = ':') do
          lx.pos <- lx.pos + 1
        done;
        while lx.pos > start && lx.input.[lx.pos - 1] = '.' do lx.pos <- lx.pos - 1 done;
        T_BNODE (String.sub lx.input start (lx.pos - start))
      end else
        lex_pname_or_keyword lx
    | c when is_digit c -> lex_number lx
    | c when is_alpha c || c = ':' || Char.code c >= 0x80 -> lex_pname_or_keyword lx
    | c -> raise (Parse_error (Printf.sprintf "Unexpected character: '%c' (0x%02X) at %d" c (Char.code c) lx.pos))

(* ============================================================================
   Parser — token-based recursive descent
   ============================================================================ *)

type parser_state = {
  lx : lexer;
  prefixes : (string, string) Hashtbl.t;
  mutable base : string option;
  mutable cur : token;
  bnode_counter : int ref;
}

let make_parser input =
  let lx = make_lexer input in
  let ps = {
    lx;
    prefixes = Hashtbl.create 16;
    base = None;
    cur = T_EOF;
    bnode_counter = ref 0;
  } in
  ps.cur <- next_token lx;
  ps

(* Accumulator for extra triples/paths generated by blank node property lists
   and RDF collections in subject/object positions. Drained by parse_property_list_not_empty. *)
let pending_extra_triples : triple_pattern list ref = ref []
let pending_extra_paths : graph_pattern list ref = ref []

let advance ps = ps.cur <- next_token ps.lx
let peek ps = ps.cur

let expect ps tok =
  if ps.cur = tok then advance ps
  else raise (Parse_error (Printf.sprintf "Expected token at pos %d" ps.lx.pos))

let fresh_bnode ps =
  let id = Printf.sprintf "_:sparql_b%d" !(ps.bnode_counter) in
  incr ps.bnode_counter; id

(* Resolve a prefixed name to a full IRI *)
let resolve_pname ps pname =
  match String.index_opt pname ':' with
  | Some i ->
    let prefix = String.sub pname 0 i in
    let local = String.sub pname (i + 1) (String.length pname - i - 1) in
    (match Hashtbl.find_opt ps.prefixes prefix with
     | Some ns -> ns ^ local
     | None -> raise (Parse_error (Printf.sprintf "Undefined prefix: '%s'" prefix)))
  | None -> raise (Parse_error (Printf.sprintf "Invalid prefixed name: '%s'" pname))

(* Parse an IRI (full or prefixed) *)
let parse_iri ps =
  match peek ps with
  | T_IRI i -> advance ps; i
  | T_PNAME pn -> advance ps; resolve_pname ps pn
  | T_A -> advance ps; "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
  | _ -> raise (Parse_error (Printf.sprintf "Expected IRI at pos %d" ps.lx.pos))

(* ============================================================================
   Expression parser with operator precedence
   ============================================================================ *)

let rec parse_primary_expr ps =
  match peek ps with
  | T_VAR v -> advance ps; E_Var v
  | T_IRI i ->
    advance ps;
    if peek ps = T_LPAREN then begin
      (* IRI followed by '(' is a function call *)
      advance ps;
      let args = if peek ps = T_RPAREN then [] else parse_expr_list ps in
      expect ps T_RPAREN;
      E_FunctionCall (i, args)
    end else
      E_IRI i
  | T_PNAME pn ->
    advance ps;
    let iri = resolve_pname ps pn in
    if peek ps = T_LPAREN then begin
      (* Prefixed name followed by '(' is a function call *)
      advance ps;
      let args = if peek ps = T_RPAREN then [] else parse_expr_list ps in
      expect ps T_RPAREN;
      E_FunctionCall (iri, args)
    end else
      E_IRI iri
  | T_TRUE -> advance ps; E_BoolLit true
  | T_FALSE -> advance ps; E_BoolLit false
  | T_INTEGER s -> advance ps; E_NumericLit (Z.of_string s)
  | T_DECIMAL s -> advance ps; E_DecimalLit s
  | T_DOUBLE s -> advance ps; E_DoubleLit s
  | T_STRING s ->
    advance ps;
    let lex = s in
    (match peek ps with
     | T_LANGTAG lang ->
       advance ps;
       E_Literal { lexical_form = lex; datatype = rdf_lang_string;
                   lang_tag = Some lang }
     | T_HATHAT ->
       advance ps;
       let dt = parse_iri ps in
       E_Literal { lexical_form = lex; datatype = dt; lang_tag = None }
     | _ ->
       E_Literal { lexical_form = lex; datatype = xsd_string; lang_tag = None })
  | T_LPAREN ->
    advance ps;
    let e = parse_expr ps in
    expect ps T_RPAREN;
    e
  | T_BANG ->
    advance ps;
    E_Not (parse_primary_expr ps)
  | T_MINUS_OP ->
    advance ps;
    E_UnaryMinus (parse_primary_expr ps)
  | T_PLUS ->
    advance ps;
    E_UnaryPlus (parse_primary_expr ps)
  (* Aggregates *)
  | T_COUNT -> parse_aggregate ps Agg_Count
  | T_SUM -> parse_aggregate ps Agg_Sum
  | T_MIN_KW -> parse_aggregate ps Agg_Min
  | T_MAX_KW -> parse_aggregate ps Agg_Max
  | T_AVG -> parse_aggregate ps Agg_Avg
  | T_SAMPLE -> parse_aggregate ps Agg_Sample
  | T_GROUP_CONCAT -> parse_group_concat ps
  (* Built-in functions *)
  | T_BOUND -> advance ps; expect ps T_LPAREN;
    let v = (match peek ps with T_VAR v -> advance ps; v
             | _ -> raise (Parse_error "BOUND expects variable")) in
    expect ps T_RPAREN; E_Bound v
  | T_IF -> advance ps; expect ps T_LPAREN;
    let c = parse_expr ps in expect ps T_COMMA;
    let t = parse_expr ps in expect ps T_COMMA;
    let f = parse_expr ps in expect ps T_RPAREN;
    E_If (c, t, f)
  | T_COALESCE -> advance ps; expect ps T_LPAREN;
    let args = if peek ps = T_RPAREN then [] else parse_expr_list ps in
    expect ps T_RPAREN; E_Coalesce args
  | T_EXISTS -> advance ps; E_Exists (parse_group_graph_pattern ps)
  | T_NOT ->
    advance ps;
    (match peek ps with
     | T_EXISTS -> advance ps; E_NotExists (parse_group_graph_pattern ps)
     | T_IN -> advance ps; raise (Parse_error "NOT IN should be handled at comparison level")
     | _ -> raise (Parse_error "Expected EXISTS or IN after NOT"))
  | T_NOW -> advance ps; expect ps T_LPAREN; expect ps T_RPAREN; E_Now
  | T_RAND -> advance ps; expect ps T_LPAREN; expect ps T_RPAREN;
    E_FunctionCall ("http://www.w3.org/2005/xpath-functions#rand", [])
  | T_UUID -> advance ps; expect ps T_LPAREN; expect ps T_RPAREN;
    E_FunctionCall ("http://www.w3.org/2005/xpath-functions#uuid", [])
  | T_STRUUID -> advance ps; expect ps T_LPAREN; expect ps T_RPAREN;
    E_FunctionCall ("http://www.w3.org/2005/xpath-functions#struuid", [])
  | tok -> parse_builtin_call ps tok

and parse_builtin_call ps tok =
  let one_arg fn = advance ps; expect ps T_LPAREN;
    let e = parse_expr ps in expect ps T_RPAREN; fn e in
  let two_arg fn = advance ps; expect ps T_LPAREN;
    let a = parse_expr ps in expect ps T_COMMA;
    let b = parse_expr ps in expect ps T_RPAREN; fn a b in
  match tok with
  | T_STR_KW -> one_arg (fun e -> E_Str e)
  | T_LANG -> one_arg (fun e -> E_Lang e)
  | T_DATATYPE -> one_arg (fun e -> E_Datatype e)
  | T_IRI_KW | T_URI -> one_arg (fun e -> E_IRI_fn e)
  | T_ISIRI | T_ISURI -> one_arg (fun e -> E_IsIRI e)
  | T_ISBLANK -> one_arg (fun e -> E_IsBlank e)
  | T_ISLITERAL -> one_arg (fun e -> E_IsLiteral e)
  | T_ISNUMERIC -> one_arg (fun e -> E_IsNumeric e)
  | T_ABS -> one_arg (fun e -> E_Abs e)
  | T_CEIL -> one_arg (fun e -> E_Ceil e)
  | T_FLOOR -> one_arg (fun e -> E_Floor e)
  | T_ROUND -> one_arg (fun e -> E_Round e)
  | T_STRLEN -> one_arg (fun e -> E_StrLen e)
  | T_UCASE -> one_arg (fun e -> E_UCase e)
  | T_LCASE -> one_arg (fun e -> E_LCase e)
  | T_ENCODE_FOR_URI -> one_arg (fun e -> E_EncodeForUri e)
  | T_MD5 -> one_arg (fun e -> E_MD5 e)
  | T_SHA1 -> one_arg (fun e -> E_SHA1 e)
  | T_SHA256 -> one_arg (fun e -> E_SHA256 e)
  | T_SHA384 -> one_arg (fun e -> E_SHA384 e)
  | T_SHA512 -> one_arg (fun e -> E_SHA512 e)
  | T_YEAR -> one_arg (fun e -> E_Year e)
  | T_MONTH -> one_arg (fun e -> E_Month e)
  | T_DAY -> one_arg (fun e -> E_Day e)
  | T_HOURS -> one_arg (fun e -> E_Hours e)
  | T_MINUTES -> one_arg (fun e -> E_Minutes e)
  | T_SECONDS -> one_arg (fun e -> E_Seconds e)
  | T_TIMEZONE -> one_arg (fun e -> E_Timezone e)
  | T_TZ -> one_arg (fun e -> E_Tz e)
  | T_SAMETERM -> two_arg (fun a b -> E_SameTerm (a, b))
  | T_STRDT -> two_arg (fun a b -> E_StrDt (a, b))
  | T_STRLANG -> two_arg (fun a b -> E_StrLang (a, b))
  | T_CONTAINS -> two_arg (fun a b -> E_Contains (a, b))
  | T_STRSTARTS -> two_arg (fun a b -> E_StrStarts (a, b))
  | T_STRENDS -> two_arg (fun a b -> E_StrEnds (a, b))
  | T_STRBEFORE -> two_arg (fun a b -> E_StrBefore (a, b))
  | T_STRAFTER -> two_arg (fun a b -> E_StrAfter (a, b))
  | T_LANGMATCHES -> two_arg (fun a b ->
    E_FunctionCall ("http://www.w3.org/2005/xpath-functions#langMatches", [a; b]))
  | T_BNODE_KW ->
    advance ps; expect ps T_LPAREN;
    if peek ps = T_RPAREN then
      (advance ps; E_FunctionCall ("http://www.w3.org/2005/xpath-functions#bnode", []))
    else
      let e = parse_expr ps in expect ps T_RPAREN;
      E_FunctionCall ("http://www.w3.org/2005/xpath-functions#bnode", [e])
  | T_CONCAT ->
    advance ps; expect ps T_LPAREN;
    let args = if peek ps = T_RPAREN then [] else parse_expr_list ps in
    expect ps T_RPAREN; E_Concat args
  | T_SUBSTR | T_SUBSTRING ->
    advance ps; expect ps T_LPAREN;
    let s = parse_expr ps in expect ps T_COMMA;
    let start = parse_expr ps in
    let len = if peek ps = T_COMMA then
      (advance ps; Some (parse_expr ps)) else None in
    expect ps T_RPAREN; E_Substr (s, start, len)
  | T_REPLACE ->
    advance ps; expect ps T_LPAREN;
    let s = parse_expr ps in expect ps T_COMMA;
    let pat = parse_expr ps in expect ps T_COMMA;
    let rep = parse_expr ps in
    let flags = if peek ps = T_COMMA then (advance ps; Some (parse_expr ps)) else None in
    expect ps T_RPAREN; E_Replace (s, pat, rep, flags)
  | T_REGEX ->
    advance ps; expect ps T_LPAREN;
    let s = parse_expr ps in expect ps T_COMMA;
    let pat = parse_expr ps in
    let flags = if peek ps = T_COMMA then (advance ps; Some (parse_expr ps)) else None in
    expect ps T_RPAREN; E_Regex (s, pat, flags)
  | _ -> raise (Parse_error (Printf.sprintf "Unexpected token in expression at pos %d" ps.lx.pos))

and parse_aggregate ps agg_fn =
  advance ps;
  expect ps T_LPAREN;
  let distinct = peek ps = T_DISTINCT in
  if distinct then advance ps;
  let e = if agg_fn = Agg_Count && peek ps = T_STAR then
    (advance ps; E_NumericLit Z.one)  (* COUNT-star *)
  else parse_expr ps in
  expect ps T_RPAREN;
  E_Aggregate (agg_fn, distinct, e)

and parse_group_concat ps =
  advance ps;
  expect ps T_LPAREN;
  let distinct = peek ps = T_DISTINCT in
  if distinct then advance ps;
  let e = parse_expr ps in
  let sep = if peek ps = T_SEMI then begin
    advance ps;
    (match peek ps with
     | T_SEPARATOR -> advance ps; expect ps T_EQ;
       (match peek ps with
        | T_STRING s -> advance ps; Some s
        | _ -> raise (Parse_error "Expected string after SEPARATOR="))
     | _ -> raise (Parse_error "Expected SEPARATOR after ;"))
  end else None in
  expect ps T_RPAREN;
  E_Aggregate (Agg_GroupConcat sep, distinct, e)

and parse_expr_list ps =
  let rec loop acc =
    let e = parse_expr ps in
    let acc = e :: acc in
    if peek ps = T_COMMA then (advance ps; loop acc)
    else List.rev acc
  in loop []

(* Operator precedence: OR < AND < compare < IN/NOT IN < add/sub < mul/div *)
and parse_expr ps = parse_or_expr ps

and parse_or_expr ps =
  let left = parse_and_expr ps in
  let rec loop left =
    if peek ps = T_OR then (advance ps; loop (E_Or (left, parse_and_expr ps)))
    else left
  in loop left

and parse_and_expr ps =
  let left = parse_compare_expr ps in
  let rec loop left =
    if peek ps = T_AND then (advance ps; loop (E_And (left, parse_compare_expr ps)))
    else left
  in loop left

and parse_compare_expr ps =
  let left = parse_additive_expr ps in
  match peek ps with
  | T_EQ -> advance ps; E_Compare (CmpEq, left, parse_additive_expr ps)
  | T_NE -> advance ps; E_Compare (CmpNe, left, parse_additive_expr ps)
  | T_LT -> advance ps; E_Compare (CmpLt, left, parse_additive_expr ps)
  | T_GT -> advance ps; E_Compare (CmpGt, left, parse_additive_expr ps)
  | T_LE -> advance ps; E_Compare (CmpLe, left, parse_additive_expr ps)
  | T_GE -> advance ps; E_Compare (CmpGe, left, parse_additive_expr ps)
  | T_IN -> advance ps; expect ps T_LPAREN;
    let args = if peek ps = T_RPAREN then [] else parse_expr_list ps in
    expect ps T_RPAREN; E_In (left, args)
  | T_NOT ->
    let save = ps.lx.pos in
    advance ps;
    if peek ps = T_IN then begin
      advance ps; expect ps T_LPAREN;
      let args = if peek ps = T_RPAREN then [] else parse_expr_list ps in
      expect ps T_RPAREN; E_NotIn (left, args)
    end else begin
      (* Not a NOT IN, backtrack *)
      ps.lx.pos <- save;
      ps.cur <- T_NOT;
      left
    end
  | _ -> left

and parse_additive_expr ps =
  let left = parse_multiplicative_expr ps in
  let rec loop left =
    match peek ps with
    | T_PLUS -> advance ps; loop (E_Arith (Add, left, parse_multiplicative_expr ps))
    | T_MINUS_OP -> advance ps; loop (E_Arith (Sub, left, parse_multiplicative_expr ps))
    | _ -> left
  in loop left

and parse_multiplicative_expr ps =
  let left = parse_primary_expr ps in
  let rec loop left =
    match peek ps with
    | T_TIMES -> advance ps; loop (E_Arith (Mul, left, parse_primary_expr ps))
    | T_DIVIDE | T_SLASH -> advance ps; loop (E_Arith (Div, left, parse_primary_expr ps))
    | _ -> left
  in loop left

(* ============================================================================
   Pattern parser — triple patterns, graph patterns, WHERE clause
   ============================================================================ *)

(* Parse a pattern term (object/predicate position) *)
and parse_pattern_term ps =
  match peek ps with
  | T_VAR v -> advance ps; PT_Var v
  | T_IRI i -> advance ps; PT_IRI i
  | T_PNAME pn -> advance ps; PT_IRI (resolve_pname ps pn)
  | T_A -> advance ps; PT_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
  | T_BNODE b -> advance ps; PT_BNode b
  | T_ANON -> advance ps; PT_BNode (fresh_bnode ps)
  | T_TRUE -> advance ps; PT_Literal { lexical_form = "true"; datatype = xsd_boolean; lang_tag = None }
  | T_FALSE -> advance ps; PT_Literal { lexical_form = "false"; datatype = xsd_boolean; lang_tag = None }
  | T_INTEGER s -> advance ps; PT_Literal { lexical_form = s; datatype = xsd_integer; lang_tag = None }
  | T_DECIMAL s -> advance ps; PT_Literal { lexical_form = s; datatype = xsd_decimal; lang_tag = None }
  | T_DOUBLE s -> advance ps; PT_Literal { lexical_form = s; datatype = xsd_double; lang_tag = None }
  | T_STRING s ->
    advance ps;
    (match peek ps with
     | T_LANGTAG lang -> advance ps;
       PT_Literal { lexical_form = s; datatype = rdf_lang_string; lang_tag = Some lang }
     | T_HATHAT -> advance ps;
       let dt = parse_iri ps in
       PT_Literal { lexical_form = s; datatype = dt; lang_tag = None }
     | _ -> PT_Literal { lexical_form = s; datatype = xsd_string; lang_tag = None })
  | T_LBRACKET ->
    (* [ :p :o ; ... ] blank node property list in object position *)
    let bnode = fresh_bnode ps in
    advance ps;
    let (triples, paths) = parse_property_list_not_empty ps (PS_BNode bnode) in
    expect ps T_RBRACKET;
    pending_extra_triples := List.rev_append triples !pending_extra_triples;
    pending_extra_paths := List.rev_append paths !pending_extra_paths;
    PT_BNode bnode
  | T_LPAREN ->
    (* ( item1 item2 ... ) RDF collection in object position *)
    advance ps;
    if peek ps = T_RPAREN then begin
      advance ps;
      PT_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
    end else begin
      let rdf_first = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first" in
      let rdf_rest = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest" in
      let rdf_nil = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil" in
      let head_bnode = fresh_bnode ps in
      let cur = ref head_bnode in
      let first_ref = ref true in
      while peek ps <> T_RPAREN && peek ps <> T_EOF do
        let node = if !first_ref then (first_ref := false; !cur) else begin
          let next = fresh_bnode ps in
          pending_extra_triples := { tp_s = PS_BNode !cur;
                                     tp_p = PT_IRI rdf_rest;
                                     tp_o = PT_BNode next } :: !pending_extra_triples;
          cur := next;
          next
        end in
        let item = parse_pattern_term ps in
        pending_extra_triples := { tp_s = PS_BNode node;
                                   tp_p = PT_IRI rdf_first;
                                   tp_o = item } :: !pending_extra_triples;
      done;
      pending_extra_triples := { tp_s = PS_BNode !cur;
                                 tp_p = PT_IRI rdf_rest;
                                 tp_o = PT_IRI rdf_nil } :: !pending_extra_triples;
      expect ps T_RPAREN;
      PT_BNode head_bnode
    end
  | _ -> raise (Parse_error (Printf.sprintf "Expected pattern term at pos %d" ps.lx.pos))

and parse_pattern_subject ps =
  match peek ps with
  | T_VAR v -> advance ps; PS_Var v
  | T_IRI i -> advance ps; PS_IRI i
  | T_PNAME pn -> advance ps; PS_IRI (resolve_pname ps pn)
  | T_BNODE b -> advance ps; PS_BNode b
  | T_ANON -> advance ps; PS_BNode (fresh_bnode ps)
  | T_LBRACKET ->
    (* [ :p :o ; ... ] blank node property list as subject *)
    let bnode = fresh_bnode ps in
    advance ps; (* skip [ *)
    let (triples, paths) = parse_property_list_not_empty ps (PS_BNode bnode) in
    expect ps T_RBRACKET;
    pending_extra_triples := List.rev_append triples !pending_extra_triples;
    pending_extra_paths := List.rev_append paths !pending_extra_paths;
    PS_BNode bnode
  | T_LPAREN ->
    (* ( item1 item2 ... ) RDF collection in subject position *)
    advance ps;
    if peek ps = T_RPAREN then begin
      advance ps;
      PS_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
    end else begin
      let rdf_first = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first" in
      let rdf_rest = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest" in
      let rdf_nil = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil" in
      let head_bnode = fresh_bnode ps in
      let cur = ref head_bnode in
      let first_ref = ref true in
      while peek ps <> T_RPAREN && peek ps <> T_EOF do
        let node = if !first_ref then (first_ref := false; !cur) else begin
          let next = fresh_bnode ps in
          pending_extra_triples := { tp_s = PS_BNode !cur;
                                     tp_p = PT_IRI rdf_rest;
                                     tp_o = PT_BNode next } :: !pending_extra_triples;
          cur := next;
          next
        end in
        let item = parse_pattern_term ps in
        pending_extra_triples := { tp_s = PS_BNode node;
                                   tp_p = PT_IRI rdf_first;
                                   tp_o = item } :: !pending_extra_triples;
      done;
      pending_extra_triples := { tp_s = PS_BNode !cur;
                                 tp_p = PT_IRI rdf_rest;
                                 tp_o = PT_IRI rdf_nil } :: !pending_extra_triples;
      expect ps T_RPAREN;
      PS_BNode head_bnode
    end
  | _ -> raise (Parse_error (Printf.sprintf "Expected subject at pos %d" ps.lx.pos))

(* Parse property path or simple predicate *)
and parse_verb_or_path ps =
  match peek ps with
  | T_A -> advance ps; `Simple (PT_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#type")
  | T_VAR v -> advance ps; `Simple (PT_Var v)
  | _ ->
    let iri_or_path = parse_path ps in
    match iri_or_path with
    | PP_IRI i -> `Simple (PT_IRI i)
    | path -> `Path path

and parse_path ps = parse_path_alternative ps

and parse_path_alternative ps =
  let left = parse_path_sequence ps in
  let rec loop left =
    if peek ps = T_PIPE then (advance ps; loop (PP_Alternative (left, parse_path_sequence ps)))
    else left
  in loop left

and parse_path_sequence ps =
  let left = parse_path_elt_or_inverse ps in
  let rec loop left =
    if peek ps = T_SLASH then (advance ps; loop (PP_Sequence (left, parse_path_elt_or_inverse ps)))
    else left
  in loop left

and parse_path_elt_or_inverse ps =
  if peek ps = T_CARET then begin
    advance ps;
    PP_Inverse (parse_path_primary ps)
  end else
    parse_path_elt ps

and parse_path_elt ps =
  let p = parse_path_primary ps in
  match peek ps with
  | T_STAR -> advance ps; PP_ZeroOrMore p
  | T_PLUS -> advance ps; PP_OneOrMore p
  | T_QMARK -> advance ps; PP_ZeroOrOne p
  | _ -> p

and parse_path_primary ps =
  match peek ps with
  | T_IRI i -> advance ps; PP_IRI i
  | T_PNAME pn -> advance ps; PP_IRI (resolve_pname ps pn)
  | T_A -> advance ps; PP_IRI "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
  | T_LPAREN -> advance ps; let p = parse_path ps in expect ps T_RPAREN; p
  | T_BANG ->
    advance ps;
    (* Negated property set *)
    if peek ps = T_LPAREN then begin
      advance ps;
      let paths = ref [] in
      let rec loop () =
        paths := parse_path_elt_or_inverse ps :: !paths;
        if peek ps = T_PIPE then (advance ps; loop ())
      in loop ();
      expect ps T_RPAREN;
      PP_NegatedSet (List.rev !paths)
    end else
      PP_NegatedSet [parse_path_elt_or_inverse ps]
  | _ -> raise (Parse_error (Printf.sprintf "Expected path at pos %d" ps.lx.pos))

(* Parse a predicate-object list: ?p ?o [, ?o]* [; ?p ?o [, ?o]*]* *)
(* Returns (triple_patterns, property_path_patterns) *)
and parse_property_list_not_empty ps subject =
  let triples = ref [] in
  let paths = ref [] in
  let drain_extras () =
    if !pending_extra_triples <> [] then begin
      triples := List.rev_append !pending_extra_triples !triples;
      pending_extra_triples := []
    end;
    if !pending_extra_paths <> [] then begin
      paths := List.rev_append !pending_extra_paths !paths;
      pending_extra_paths := []
    end
  in
  let rec parse_po () =
    let verb = parse_verb_or_path ps in
    let rec parse_objects () =
      let obj = parse_pattern_term ps in
      drain_extras ();
      (match verb with
       | `Simple p -> triples := { tp_s = subject; tp_p = p; tp_o = obj } :: !triples
       | `Path path ->
         paths := GP_PropertyPath (subject, path, obj) :: !paths);
      if peek ps = T_COMMA then (advance ps; parse_objects ())
    in
    parse_objects ();
    if peek ps = T_SEMI then begin
      advance ps;
      if peek ps <> T_RBRACE && peek ps <> T_DOT && peek ps <> T_RBRACKET && peek ps <> T_EOF then
        parse_po ()
    end
  in
  parse_po ();
  (List.rev !triples, List.rev !paths)

(* Parse the contents of a { } block — producing a group_graph_pattern *)
and parse_group_graph_pattern ps =
  expect ps T_LBRACE;
  (* Check for sub-select *)
  if peek ps = T_SELECT then begin
    let q = parse_sub_select ps in
    (* Check for VALUES clause after sub-select but before closing brace *)
    if peek ps = T_VALUES then begin
      advance ps;
      let (vars, rows) = parse_inline_data ps in
      expect ps T_RBRACE;
      GP_Join (GP_SubSelect q, GP_Values (vars, rows))
    end else begin
      expect ps T_RBRACE;
      GP_SubSelect q
    end
  end else begin
    let pat = parse_group_pattern_contents ps in
    expect ps T_RBRACE;
    pat
  end

and parse_group_pattern_contents ps =
  let patterns = ref [] in
  let filters = ref [] in
  let current_bgp = ref [] in

  let flush_bgp () =
    if !current_bgp <> [] then begin
      patterns := GP_BGP (List.rev !current_bgp) :: !patterns;
      current_bgp := []
    end
  in

  let rec loop () =
    match peek ps with
    | T_RBRACE | T_EOF -> ()
    | T_DOT -> advance ps; loop ()
    | T_OPTIONAL ->
      flush_bgp ();
      advance ps;
      let opt = parse_group_graph_pattern ps in
      patterns := GP_LeftJoin (GP_Empty, opt, E_BoolLit true) :: !patterns;
      loop ()
    | T_UNION ->
      (* UNION binds to previous pattern *)
      flush_bgp ();
      advance ps;
      let right = parse_group_graph_pattern ps in
      let left = match !patterns with
        | p :: rest -> patterns := rest; p
        | [] -> GP_Empty in
      patterns := GP_Union (left, right) :: !patterns;
      loop ()
    | T_MINUS ->
      flush_bgp ();
      advance ps;
      let right = parse_group_graph_pattern ps in
      patterns := GP_Minus (GP_Empty, right) :: !patterns;
      loop ()
    | T_FILTER ->
      advance ps;
      let e = if peek ps = T_LPAREN then begin
        advance ps;
        let e = parse_expr ps in
        expect ps T_RPAREN; e
      end else
        parse_expr ps (* for FILTER EXISTS / FILTER NOT EXISTS *)
      in
      filters := e :: !filters;
      loop ()
    | T_BIND ->
      flush_bgp ();
      advance ps;
      expect ps T_LPAREN;
      let e = parse_expr ps in
      expect ps T_AS;
      let v = match peek ps with
        | T_VAR v -> advance ps; v
        | _ -> raise (Parse_error "Expected variable after AS") in
      expect ps T_RPAREN;
      patterns := GP_Bind (e, v, GP_Empty) :: !patterns;
      loop ()
    | T_VALUES ->
      flush_bgp ();
      advance ps;
      let (vars, rows) = parse_inline_data ps in
      patterns := GP_Values (vars, rows) :: !patterns;
      loop ()
    | T_GRAPH ->
      flush_bgp ();
      advance ps;
      let g = parse_pattern_term ps in
      let p = parse_group_graph_pattern ps in
      patterns := GP_Graph (g, p) :: !patterns;
      loop ()
    | T_SERVICE ->
      flush_bgp ();
      advance ps;
      let silent = peek ps = T_SILENT in
      if silent then advance ps;
      let iri = parse_iri ps in
      let p = parse_group_graph_pattern ps in
      patterns := GP_Service (iri, p, silent) :: !patterns;
      loop ()
    | T_LBRACE ->
      flush_bgp ();
      (* Could be sub-select or nested group *)
      let sub = parse_group_graph_pattern ps in
      patterns := sub :: !patterns;
      (* Check for UNION after nested group *)
      if peek ps = T_UNION then begin
        advance ps;
        let right = parse_group_graph_pattern ps in
        let left = match !patterns with p :: rest -> patterns := rest; p | [] -> GP_Empty in
        patterns := GP_Union (left, right) :: !patterns
      end;
      loop ()
    | _ ->
      (* Try to parse triple patterns *)
      (try
         let subject = parse_pattern_subject ps in
         (* Drain any extras from subject parsing (e.g. blank node property lists) *)
         if !pending_extra_triples <> [] then begin
           current_bgp := List.rev_append !pending_extra_triples !current_bgp;
           pending_extra_triples := []
         end;
         if !pending_extra_paths <> [] then begin
           flush_bgp ();
           patterns := List.rev_append !pending_extra_paths !patterns;
           pending_extra_paths := []
         end;
         let (triples, path_patterns) = parse_property_list_not_empty ps subject in
         current_bgp := List.rev_append triples !current_bgp;
         if path_patterns <> [] then begin
           flush_bgp ();
           patterns := List.rev_append path_patterns !patterns
         end;
         (match peek ps with T_DOT -> advance ps | _ -> ());
         loop ()
       with Parse_error _ -> ())
  in
  loop ();
  flush_bgp ();

  (* Combine all patterns with Join, then wrap filters *)
  let combined = match List.rev !patterns with
    | [] -> GP_Empty
    | [p] -> p
    | first :: rest ->
      List.fold_left (fun acc p ->
        match p with
        | GP_LeftJoin (GP_Empty, opt, cond) -> GP_LeftJoin (acc, opt, cond)
        | GP_Minus (GP_Empty, right) -> GP_Minus (acc, right)
        | GP_Bind (e, v, GP_Empty) -> GP_Bind (e, v, acc)
        | _ -> GP_Join (acc, p)
      ) first rest
  in
  (* Apply filters *)
  List.fold_left (fun acc f -> GP_Filter (f, acc)) combined (List.rev !filters)

(* Parse inline data for VALUES *)
and parse_inline_data ps =
  match peek ps with
  | T_VAR v ->
    (* Single variable: VALUES ?x { val1 val2 ... } *)
    advance ps;
    expect ps T_LBRACE;
    let rows = ref [] in
    while peek ps <> T_RBRACE && peek ps <> T_EOF do
      if peek ps = T_UNDEF then (advance ps; rows := [None] :: !rows)
      else begin
        let t = parse_rdf_term ps in
        rows := [Some t] :: !rows
      end
    done;
    expect ps T_RBRACE;
    ([v], List.rev !rows)
  | T_LPAREN ->
    (* Multi variable: VALUES (?x ?y) { (v1 v2) ... } *)
    advance ps;
    let vars = ref [] in
    while peek ps <> T_RPAREN && peek ps <> T_EOF do
      match peek ps with
      | T_VAR v -> advance ps; vars := v :: !vars
      | _ -> raise (Parse_error "Expected variable in VALUES")
    done;
    expect ps T_RPAREN;
    let vars = List.rev !vars in
    expect ps T_LBRACE;
    let rows = ref [] in
    while peek ps <> T_RBRACE && peek ps <> T_EOF do
      expect ps T_LPAREN;
      let row = List.map (fun _ ->
        if peek ps = T_UNDEF then (advance ps; None)
        else Some (parse_rdf_term ps)
      ) vars in
      expect ps T_RPAREN;
      rows := row :: !rows
    done;
    expect ps T_RBRACE;
    (vars, List.rev !rows)
  | _ -> raise (Parse_error "Expected variable or ( in VALUES")

and parse_rdf_term ps =
  match peek ps with
  | T_IRI i -> advance ps; T_IRI i
  | T_PNAME pn -> advance ps; T_IRI (resolve_pname ps pn)
  | T_BNODE b -> advance ps; T_BNode b
  | T_TRUE -> advance ps; T_Literal { lexical_form = "true"; datatype = xsd_boolean; lang_tag = None }
  | T_FALSE -> advance ps; T_Literal { lexical_form = "false"; datatype = xsd_boolean; lang_tag = None }
  | T_INTEGER s -> advance ps; T_Literal { lexical_form = s; datatype = xsd_integer; lang_tag = None }
  | T_DECIMAL s -> advance ps; T_Literal { lexical_form = s; datatype = xsd_decimal; lang_tag = None }
  | T_DOUBLE s -> advance ps; T_Literal { lexical_form = s; datatype = xsd_double; lang_tag = None }
  | T_STRING s ->
    advance ps;
    (match peek ps with
     | T_LANGTAG lang -> advance ps;
       T_Literal { lexical_form = s; datatype = rdf_lang_string; lang_tag = Some lang }
     | T_HATHAT -> advance ps; let dt = parse_iri ps in
       T_Literal { lexical_form = s; datatype = dt; lang_tag = None }
     | _ -> T_Literal { lexical_form = s; datatype = xsd_string; lang_tag = None })
  | _ -> raise (Parse_error (Printf.sprintf "Expected RDF term at pos %d" ps.lx.pos))

(* ============================================================================
   Query-level parser — SELECT, ASK, CONSTRUCT, prologue, modifiers
   ============================================================================ *)

and parse_sub_select ps =
  (* SELECT inside { } — sub-select *)
  parse_select_query ps

and parse_select_query ps =
  expect ps T_SELECT;
  let distinct = peek ps = T_DISTINCT in
  if distinct then advance ps;
  let reduced = peek ps = T_REDUCED in
  if reduced then advance ps;

  (* Select clause *)
  let select_clause = if peek ps = T_STAR then begin
    advance ps; Select_All
  end else begin
    let items = ref [] in
    let rec loop () =
      match peek ps with
      | T_VAR v -> advance ps; items := SI_Var v :: !items; loop ()
      | T_LPAREN ->
        advance ps;
        let e = parse_expr ps in
        expect ps T_AS;
        let v = match peek ps with
          | T_VAR v -> advance ps; v
          | _ -> raise (Parse_error "Expected variable after AS") in
        expect ps T_RPAREN;
        items := SI_Expr (e, v) :: !items;
        loop ()
      | _ -> ()
    in loop ();
    Select_Vars (List.rev !items)
  end in

  (* Dataset clauses — skip for now *)
  while peek ps = T_PNAME "FROM" || (match peek ps with T_PNAME s -> String.uppercase_ascii s = "FROM" | _ -> false) do
    advance ps;
    ignore (parse_iri ps)
  done;

  (* WHERE clause *)
  if peek ps = T_WHERE then advance ps;
  let pattern = parse_group_graph_pattern ps in

  (* Solution modifiers *)
  let group_by = if peek ps = T_GROUP then begin
    advance ps; expect ps T_BY;
    let conditions = ref [] in
    let rec loop () =
      match peek ps with
      | T_VAR v -> advance ps; conditions := GC_Var v :: !conditions; loop ()
      | T_LPAREN ->
        advance ps;
        let e = parse_expr ps in
        let alias = if peek ps = T_AS then begin
          advance ps;
          match peek ps with T_VAR v -> advance ps; Some v | _ -> None
        end else None in
        expect ps T_RPAREN;
        conditions := GC_Expr (e, alias) :: !conditions;
        loop ()
      | T_IRI _ | T_PNAME _ ->
        let e = parse_primary_expr ps in
        conditions := GC_BuiltIn e :: !conditions;
        loop ()
      | _ -> ()
    in loop ();
    Some (List.rev !conditions)
  end else None in

  let having = if peek ps = T_HAVING then begin
    advance ps;
    let conditions = ref [] in
    let rec loop () =
      match peek ps with
      | T_LPAREN ->
        advance ps;
        let e = parse_expr ps in
        expect ps T_RPAREN;
        conditions := e :: !conditions;
        loop ()
      | _ when !conditions = [] ->
        (* Single expression without parens *)
        conditions := [parse_expr ps]
      | _ -> ()
    in loop ();
    Some (List.rev !conditions)
  end else None in

  let order_by = if peek ps = T_ORDER then begin
    advance ps; expect ps T_BY;
    let conditions = ref [] in
    let rec loop () =
      match peek ps with
      | T_ASC -> advance ps; expect ps T_LPAREN;
        let e = parse_expr ps in expect ps T_RPAREN;
        conditions := OC_Asc e :: !conditions; loop ()
      | T_DESC -> advance ps; expect ps T_LPAREN;
        let e = parse_expr ps in expect ps T_RPAREN;
        conditions := OC_Desc e :: !conditions; loop ()
      | T_VAR _ | T_LPAREN | T_IRI _ | T_PNAME _ ->
        let e = parse_expr ps in
        conditions := OC_Asc e :: !conditions; loop ()
      | _ when !conditions = [] ->
        let e = parse_expr ps in
        conditions := OC_Asc e :: !conditions
      | _ -> ()
    in loop ();
    Some (List.rev !conditions)
  end else None in

  let limit = if peek ps = T_LIMIT then begin
    advance ps;
    match peek ps with
    | T_INTEGER s -> advance ps; Some (Z.of_string s)
    | _ -> raise (Parse_error "Expected integer after LIMIT")
  end else None in

  let offset = if peek ps = T_OFFSET then begin
    advance ps;
    match peek ps with
    | T_INTEGER s -> advance ps; Some (Z.of_string s)
    | _ -> raise (Parse_error "Expected integer after OFFSET")
  end else None in

  (* LIMIT can come after OFFSET too *)
  let limit = if limit = None && peek ps = T_LIMIT then begin
    advance ps;
    match peek ps with
    | T_INTEGER s -> advance ps; Some (Z.of_string s)
    | _ -> raise (Parse_error "Expected integer after LIMIT")
  end else limit in

  (* Post-query VALUES clause *)
  let values = if peek ps = T_VALUES then begin
    advance ps;
    let (vars, rows) = parse_inline_data ps in
    (* Convert VALUES (vars, rows) into solution_sequence *)
    let mappings = List.filter_map (fun row ->
      if List.length row <> List.length vars then None
      else
        let bindings = List.filter_map (fun (v, t_opt) ->
          match t_opt with
          | Some t -> Some (v, t)
          | None -> None
        ) (List.combine vars row) in
        Some bindings
    ) rows in
    Some mappings
  end else None in

  {
    q_base = ps.base;
    q_prefixes = Hashtbl.fold (fun k v acc -> (k, v) :: acc) ps.prefixes [];
    q_form = QF_Select select_clause;
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
  }

let parse_query input =
  let ps = make_parser input in

  (* Prologue: PREFIX and BASE *)
  let rec parse_prologue () =
    match peek ps with
    | T_PREFIX ->
      advance ps;
      let prefix = match peek ps with
        | T_PNAME pn ->
          advance ps;
          (* Extract prefix part before : *)
          (match String.index_opt pn ':' with
           | Some i -> String.sub pn 0 i
           | None -> pn)
        | _ -> raise (Parse_error "Expected prefix name after PREFIX")
      in
      let iri = match peek ps with
        | T_IRI i -> advance ps; i
        | _ -> raise (Parse_error "Expected IRI after prefix")
      in
      Hashtbl.replace ps.prefixes prefix iri;
      parse_prologue ()
    | T_BASE ->
      advance ps;
      let iri = match peek ps with
        | T_IRI i -> advance ps; i
        | _ -> raise (Parse_error "Expected IRI after BASE")
      in
      ps.base <- Some iri;
      parse_prologue ()
    | _ -> ()
  in
  parse_prologue ();

  (* Query form *)
  match peek ps with
  | T_SELECT -> parse_select_query ps
  | T_ASK ->
    advance ps;
    if peek ps = T_WHERE then advance ps;
    let pattern = parse_group_graph_pattern ps in
    {
      q_base = ps.base;
      q_prefixes = Hashtbl.fold (fun k v acc -> (k, v) :: acc) ps.prefixes [];
      q_form = QF_Ask;
      q_dataset = [];
      q_pattern = pattern;
      q_group_by = None;
      q_having = None;
      q_modifier = { sm_order_by = None; sm_distinct = false; sm_reduced = false;
                     sm_offset = None; sm_limit = None };
      q_values = None;
    }
  | T_CONSTRUCT ->
    advance ps;
    (* CONSTRUCT { template } WHERE { pattern }
       or CONSTRUCT WHERE { pattern } (WHERE pattern IS the template) *)
    let has_template = peek ps = T_LBRACE in
    let template = if has_template then begin
      advance ps;
      let triples = ref [] in
      while peek ps <> T_RBRACE && peek ps <> T_EOF do
        let subject = parse_pattern_subject ps in
        (* Drain extras from subject *)
        if !pending_extra_triples <> [] then begin
          triples := List.rev_append !pending_extra_triples !triples;
          pending_extra_triples := []
        end;
        let (tps, _paths) = parse_property_list_not_empty ps subject in
        triples := List.rev_append tps !triples;
        (match peek ps with T_DOT -> advance ps | _ -> ())
      done;
      expect ps T_RBRACE;
      List.rev !triples
    end else [] in
    (* Skip dataset clauses (FROM / FROM NAMED) *)
    while (match peek ps with T_PNAME s -> String.uppercase_ascii s = "FROM" | _ -> false) do
      advance ps;
      (* Check for NAMED *)
      (match peek ps with
       | T_PNAME s when String.uppercase_ascii s = "NAMED" -> advance ps
       | _ -> ());
      ignore (parse_iri ps)
    done;
    if peek ps = T_WHERE then advance ps;
    let pattern = parse_group_graph_pattern ps in
    (* For CONSTRUCT WHERE (no explicit template), extract triples from the pattern *)
    let template = if not has_template then
      (match pattern with
       | GP_BGP triples -> triples
       | _ -> [])
    else template in
    {
      q_base = ps.base;
      q_prefixes = Hashtbl.fold (fun k v acc -> (k, v) :: acc) ps.prefixes [];
      q_form = QF_Construct template;
      q_dataset = [];
      q_pattern = pattern;
      q_group_by = None;
      q_having = None;
      q_modifier = { sm_order_by = None; sm_distinct = false; sm_reduced = false;
                     sm_offset = None; sm_limit = None };
      q_values = None;
    }
  | _ -> raise (Parse_error (Printf.sprintf "Expected SELECT, ASK, or CONSTRUCT at pos %d" ps.lx.pos))
