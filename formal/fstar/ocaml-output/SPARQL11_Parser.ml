open Prims
type token =
  | Tok_SELECT 
  | Tok_ASK 
  | Tok_CONSTRUCT 
  | Tok_DESCRIBE 
  | Tok_WHERE 
  | Tok_PREFIX 
  | Tok_BASE 
  | Tok_OPTIONAL 
  | Tok_UNION 
  | Tok_MINUS_KW 
  | Tok_FILTER 
  | Tok_BIND 
  | Tok_VALUES 
  | Tok_GRAPH 
  | Tok_SERVICE 
  | Tok_SILENT 
  | Tok_EXISTS 
  | Tok_NOT 
  | Tok_AS 
  | Tok_DISTINCT 
  | Tok_REDUCED 
  | Tok_ORDER 
  | Tok_BY 
  | Tok_ASC 
  | Tok_DESC 
  | Tok_GROUP 
  | Tok_HAVING 
  | Tok_LIMIT 
  | Tok_OFFSET 
  | Tok_IN 
  | Tok_TRUE 
  | Tok_FALSE 
  | Tok_UNDEF 
  | Tok_A 
  | Tok_LBRACE 
  | Tok_RBRACE 
  | Tok_LPAREN 
  | Tok_RPAREN 
  | Tok_LBRACKET 
  | Tok_RBRACKET 
  | Tok_DOT 
  | Tok_SEMI 
  | Tok_COMMA 
  | Tok_STAR 
  | Tok_SLASH 
  | Tok_PIPE 
  | Tok_CARET 
  | Tok_BANG 
  | Tok_QMARK 
  | Tok_PLUS 
  | Tok_MINUS_OP 
  | Tok_EQ 
  | Tok_NE 
  | Tok_LT 
  | Tok_GT 
  | Tok_LE 
  | Tok_GE 
  | Tok_AND 
  | Tok_OR 
  | Tok_HATHAT 
  | Tok_IRI of Prims.string 
  | Tok_PNAME of Prims.string 
  | Tok_VAR of Prims.string 
  | Tok_STRING of Prims.string 
  | Tok_LANGTAG of Prims.string 
  | Tok_INTEGER of Prims.string 
  | Tok_DECIMAL of Prims.string 
  | Tok_DOUBLE of Prims.string 
  | Tok_BNODE of Prims.string 
  | Tok_ANON 
  | Tok_STR 
  | Tok_LANG 
  | Tok_LANGMATCHES 
  | Tok_DATATYPE 
  | Tok_BOUND 
  | Tok_IF 
  | Tok_IRI_KW 
  | Tok_URI 
  | Tok_BNODE_KW 
  | Tok_RAND 
  | Tok_ABS 
  | Tok_CEIL 
  | Tok_FLOOR 
  | Tok_ROUND 
  | Tok_CONCAT 
  | Tok_STRLEN 
  | Tok_UCASE 
  | Tok_LCASE 
  | Tok_ENCODE_FOR_URI 
  | Tok_CONTAINS 
  | Tok_STRSTARTS 
  | Tok_STRENDS 
  | Tok_STRBEFORE 
  | Tok_STRAFTER 
  | Tok_REPLACE 
  | Tok_REGEX 
  | Tok_SUBSTR 
  | Tok_ISIRI 
  | Tok_ISBLANK 
  | Tok_ISLITERAL 
  | Tok_ISNUMERIC 
  | Tok_SAMETERM 
  | Tok_STRDT 
  | Tok_STRLANG 
  | Tok_COUNT 
  | Tok_SUM 
  | Tok_MIN_KW 
  | Tok_MAX_KW 
  | Tok_AVG 
  | Tok_GROUP_CONCAT 
  | Tok_SAMPLE 
  | Tok_SEPARATOR 
  | Tok_COALESCE 
  | Tok_NOW 
  | Tok_UUID 
  | Tok_STRUUID 
  | Tok_YEAR 
  | Tok_MONTH 
  | Tok_DAY 
  | Tok_HOURS 
  | Tok_MINUTES 
  | Tok_SECONDS 
  | Tok_TIMEZONE 
  | Tok_TZ 
  | Tok_MD5 
  | Tok_SHA1 
  | Tok_SHA256 
  | Tok_SHA384 
  | Tok_SHA512 
  | Tok_EOF 
let uu___is_Tok_SELECT (projectee : token) : Prims.bool=
  match projectee with | Tok_SELECT -> true | uu___ -> false
let uu___is_Tok_ASK (projectee : token) : Prims.bool=
  match projectee with | Tok_ASK -> true | uu___ -> false
let uu___is_Tok_CONSTRUCT (projectee : token) : Prims.bool=
  match projectee with | Tok_CONSTRUCT -> true | uu___ -> false
let uu___is_Tok_DESCRIBE (projectee : token) : Prims.bool=
  match projectee with | Tok_DESCRIBE -> true | uu___ -> false
let uu___is_Tok_WHERE (projectee : token) : Prims.bool=
  match projectee with | Tok_WHERE -> true | uu___ -> false
let uu___is_Tok_PREFIX (projectee : token) : Prims.bool=
  match projectee with | Tok_PREFIX -> true | uu___ -> false
let uu___is_Tok_BASE (projectee : token) : Prims.bool=
  match projectee with | Tok_BASE -> true | uu___ -> false
let uu___is_Tok_OPTIONAL (projectee : token) : Prims.bool=
  match projectee with | Tok_OPTIONAL -> true | uu___ -> false
let uu___is_Tok_UNION (projectee : token) : Prims.bool=
  match projectee with | Tok_UNION -> true | uu___ -> false
let uu___is_Tok_MINUS_KW (projectee : token) : Prims.bool=
  match projectee with | Tok_MINUS_KW -> true | uu___ -> false
let uu___is_Tok_FILTER (projectee : token) : Prims.bool=
  match projectee with | Tok_FILTER -> true | uu___ -> false
let uu___is_Tok_BIND (projectee : token) : Prims.bool=
  match projectee with | Tok_BIND -> true | uu___ -> false
let uu___is_Tok_VALUES (projectee : token) : Prims.bool=
  match projectee with | Tok_VALUES -> true | uu___ -> false
let uu___is_Tok_GRAPH (projectee : token) : Prims.bool=
  match projectee with | Tok_GRAPH -> true | uu___ -> false
let uu___is_Tok_SERVICE (projectee : token) : Prims.bool=
  match projectee with | Tok_SERVICE -> true | uu___ -> false
let uu___is_Tok_SILENT (projectee : token) : Prims.bool=
  match projectee with | Tok_SILENT -> true | uu___ -> false
let uu___is_Tok_EXISTS (projectee : token) : Prims.bool=
  match projectee with | Tok_EXISTS -> true | uu___ -> false
let uu___is_Tok_NOT (projectee : token) : Prims.bool=
  match projectee with | Tok_NOT -> true | uu___ -> false
let uu___is_Tok_AS (projectee : token) : Prims.bool=
  match projectee with | Tok_AS -> true | uu___ -> false
let uu___is_Tok_DISTINCT (projectee : token) : Prims.bool=
  match projectee with | Tok_DISTINCT -> true | uu___ -> false
let uu___is_Tok_REDUCED (projectee : token) : Prims.bool=
  match projectee with | Tok_REDUCED -> true | uu___ -> false
let uu___is_Tok_ORDER (projectee : token) : Prims.bool=
  match projectee with | Tok_ORDER -> true | uu___ -> false
let uu___is_Tok_BY (projectee : token) : Prims.bool=
  match projectee with | Tok_BY -> true | uu___ -> false
let uu___is_Tok_ASC (projectee : token) : Prims.bool=
  match projectee with | Tok_ASC -> true | uu___ -> false
let uu___is_Tok_DESC (projectee : token) : Prims.bool=
  match projectee with | Tok_DESC -> true | uu___ -> false
let uu___is_Tok_GROUP (projectee : token) : Prims.bool=
  match projectee with | Tok_GROUP -> true | uu___ -> false
let uu___is_Tok_HAVING (projectee : token) : Prims.bool=
  match projectee with | Tok_HAVING -> true | uu___ -> false
let uu___is_Tok_LIMIT (projectee : token) : Prims.bool=
  match projectee with | Tok_LIMIT -> true | uu___ -> false
let uu___is_Tok_OFFSET (projectee : token) : Prims.bool=
  match projectee with | Tok_OFFSET -> true | uu___ -> false
let uu___is_Tok_IN (projectee : token) : Prims.bool=
  match projectee with | Tok_IN -> true | uu___ -> false
let uu___is_Tok_TRUE (projectee : token) : Prims.bool=
  match projectee with | Tok_TRUE -> true | uu___ -> false
let uu___is_Tok_FALSE (projectee : token) : Prims.bool=
  match projectee with | Tok_FALSE -> true | uu___ -> false
let uu___is_Tok_UNDEF (projectee : token) : Prims.bool=
  match projectee with | Tok_UNDEF -> true | uu___ -> false
let uu___is_Tok_A (projectee : token) : Prims.bool=
  match projectee with | Tok_A -> true | uu___ -> false
let uu___is_Tok_LBRACE (projectee : token) : Prims.bool=
  match projectee with | Tok_LBRACE -> true | uu___ -> false
let uu___is_Tok_RBRACE (projectee : token) : Prims.bool=
  match projectee with | Tok_RBRACE -> true | uu___ -> false
let uu___is_Tok_LPAREN (projectee : token) : Prims.bool=
  match projectee with | Tok_LPAREN -> true | uu___ -> false
let uu___is_Tok_RPAREN (projectee : token) : Prims.bool=
  match projectee with | Tok_RPAREN -> true | uu___ -> false
let uu___is_Tok_LBRACKET (projectee : token) : Prims.bool=
  match projectee with | Tok_LBRACKET -> true | uu___ -> false
let uu___is_Tok_RBRACKET (projectee : token) : Prims.bool=
  match projectee with | Tok_RBRACKET -> true | uu___ -> false
let uu___is_Tok_DOT (projectee : token) : Prims.bool=
  match projectee with | Tok_DOT -> true | uu___ -> false
let uu___is_Tok_SEMI (projectee : token) : Prims.bool=
  match projectee with | Tok_SEMI -> true | uu___ -> false
let uu___is_Tok_COMMA (projectee : token) : Prims.bool=
  match projectee with | Tok_COMMA -> true | uu___ -> false
let uu___is_Tok_STAR (projectee : token) : Prims.bool=
  match projectee with | Tok_STAR -> true | uu___ -> false
let uu___is_Tok_SLASH (projectee : token) : Prims.bool=
  match projectee with | Tok_SLASH -> true | uu___ -> false
let uu___is_Tok_PIPE (projectee : token) : Prims.bool=
  match projectee with | Tok_PIPE -> true | uu___ -> false
let uu___is_Tok_CARET (projectee : token) : Prims.bool=
  match projectee with | Tok_CARET -> true | uu___ -> false
let uu___is_Tok_BANG (projectee : token) : Prims.bool=
  match projectee with | Tok_BANG -> true | uu___ -> false
let uu___is_Tok_QMARK (projectee : token) : Prims.bool=
  match projectee with | Tok_QMARK -> true | uu___ -> false
let uu___is_Tok_PLUS (projectee : token) : Prims.bool=
  match projectee with | Tok_PLUS -> true | uu___ -> false
let uu___is_Tok_MINUS_OP (projectee : token) : Prims.bool=
  match projectee with | Tok_MINUS_OP -> true | uu___ -> false
let uu___is_Tok_EQ (projectee : token) : Prims.bool=
  match projectee with | Tok_EQ -> true | uu___ -> false
let uu___is_Tok_NE (projectee : token) : Prims.bool=
  match projectee with | Tok_NE -> true | uu___ -> false
let uu___is_Tok_LT (projectee : token) : Prims.bool=
  match projectee with | Tok_LT -> true | uu___ -> false
let uu___is_Tok_GT (projectee : token) : Prims.bool=
  match projectee with | Tok_GT -> true | uu___ -> false
let uu___is_Tok_LE (projectee : token) : Prims.bool=
  match projectee with | Tok_LE -> true | uu___ -> false
let uu___is_Tok_GE (projectee : token) : Prims.bool=
  match projectee with | Tok_GE -> true | uu___ -> false
let uu___is_Tok_AND (projectee : token) : Prims.bool=
  match projectee with | Tok_AND -> true | uu___ -> false
let uu___is_Tok_OR (projectee : token) : Prims.bool=
  match projectee with | Tok_OR -> true | uu___ -> false
let uu___is_Tok_HATHAT (projectee : token) : Prims.bool=
  match projectee with | Tok_HATHAT -> true | uu___ -> false
let uu___is_Tok_IRI (projectee : token) : Prims.bool=
  match projectee with | Tok_IRI _0 -> true | uu___ -> false
let __proj__Tok_IRI__item___0 (projectee : token) : Prims.string=
  match projectee with | Tok_IRI _0 -> _0
let uu___is_Tok_PNAME (projectee : token) : Prims.bool=
  match projectee with | Tok_PNAME _0 -> true | uu___ -> false
let __proj__Tok_PNAME__item___0 (projectee : token) : Prims.string=
  match projectee with | Tok_PNAME _0 -> _0
let uu___is_Tok_VAR (projectee : token) : Prims.bool=
  match projectee with | Tok_VAR _0 -> true | uu___ -> false
let __proj__Tok_VAR__item___0 (projectee : token) : Prims.string=
  match projectee with | Tok_VAR _0 -> _0
let uu___is_Tok_STRING (projectee : token) : Prims.bool=
  match projectee with | Tok_STRING _0 -> true | uu___ -> false
let __proj__Tok_STRING__item___0 (projectee : token) : Prims.string=
  match projectee with | Tok_STRING _0 -> _0
let uu___is_Tok_LANGTAG (projectee : token) : Prims.bool=
  match projectee with | Tok_LANGTAG _0 -> true | uu___ -> false
let __proj__Tok_LANGTAG__item___0 (projectee : token) : Prims.string=
  match projectee with | Tok_LANGTAG _0 -> _0
let uu___is_Tok_INTEGER (projectee : token) : Prims.bool=
  match projectee with | Tok_INTEGER _0 -> true | uu___ -> false
let __proj__Tok_INTEGER__item___0 (projectee : token) : Prims.string=
  match projectee with | Tok_INTEGER _0 -> _0
let uu___is_Tok_DECIMAL (projectee : token) : Prims.bool=
  match projectee with | Tok_DECIMAL _0 -> true | uu___ -> false
let __proj__Tok_DECIMAL__item___0 (projectee : token) : Prims.string=
  match projectee with | Tok_DECIMAL _0 -> _0
let uu___is_Tok_DOUBLE (projectee : token) : Prims.bool=
  match projectee with | Tok_DOUBLE _0 -> true | uu___ -> false
let __proj__Tok_DOUBLE__item___0 (projectee : token) : Prims.string=
  match projectee with | Tok_DOUBLE _0 -> _0
let uu___is_Tok_BNODE (projectee : token) : Prims.bool=
  match projectee with | Tok_BNODE _0 -> true | uu___ -> false
let __proj__Tok_BNODE__item___0 (projectee : token) : Prims.string=
  match projectee with | Tok_BNODE _0 -> _0
let uu___is_Tok_ANON (projectee : token) : Prims.bool=
  match projectee with | Tok_ANON -> true | uu___ -> false
let uu___is_Tok_STR (projectee : token) : Prims.bool=
  match projectee with | Tok_STR -> true | uu___ -> false
let uu___is_Tok_LANG (projectee : token) : Prims.bool=
  match projectee with | Tok_LANG -> true | uu___ -> false
let uu___is_Tok_LANGMATCHES (projectee : token) : Prims.bool=
  match projectee with | Tok_LANGMATCHES -> true | uu___ -> false
let uu___is_Tok_DATATYPE (projectee : token) : Prims.bool=
  match projectee with | Tok_DATATYPE -> true | uu___ -> false
let uu___is_Tok_BOUND (projectee : token) : Prims.bool=
  match projectee with | Tok_BOUND -> true | uu___ -> false
let uu___is_Tok_IF (projectee : token) : Prims.bool=
  match projectee with | Tok_IF -> true | uu___ -> false
let uu___is_Tok_IRI_KW (projectee : token) : Prims.bool=
  match projectee with | Tok_IRI_KW -> true | uu___ -> false
let uu___is_Tok_URI (projectee : token) : Prims.bool=
  match projectee with | Tok_URI -> true | uu___ -> false
let uu___is_Tok_BNODE_KW (projectee : token) : Prims.bool=
  match projectee with | Tok_BNODE_KW -> true | uu___ -> false
let uu___is_Tok_RAND (projectee : token) : Prims.bool=
  match projectee with | Tok_RAND -> true | uu___ -> false
let uu___is_Tok_ABS (projectee : token) : Prims.bool=
  match projectee with | Tok_ABS -> true | uu___ -> false
let uu___is_Tok_CEIL (projectee : token) : Prims.bool=
  match projectee with | Tok_CEIL -> true | uu___ -> false
let uu___is_Tok_FLOOR (projectee : token) : Prims.bool=
  match projectee with | Tok_FLOOR -> true | uu___ -> false
let uu___is_Tok_ROUND (projectee : token) : Prims.bool=
  match projectee with | Tok_ROUND -> true | uu___ -> false
let uu___is_Tok_CONCAT (projectee : token) : Prims.bool=
  match projectee with | Tok_CONCAT -> true | uu___ -> false
let uu___is_Tok_STRLEN (projectee : token) : Prims.bool=
  match projectee with | Tok_STRLEN -> true | uu___ -> false
let uu___is_Tok_UCASE (projectee : token) : Prims.bool=
  match projectee with | Tok_UCASE -> true | uu___ -> false
let uu___is_Tok_LCASE (projectee : token) : Prims.bool=
  match projectee with | Tok_LCASE -> true | uu___ -> false
let uu___is_Tok_ENCODE_FOR_URI (projectee : token) : Prims.bool=
  match projectee with | Tok_ENCODE_FOR_URI -> true | uu___ -> false
let uu___is_Tok_CONTAINS (projectee : token) : Prims.bool=
  match projectee with | Tok_CONTAINS -> true | uu___ -> false
let uu___is_Tok_STRSTARTS (projectee : token) : Prims.bool=
  match projectee with | Tok_STRSTARTS -> true | uu___ -> false
let uu___is_Tok_STRENDS (projectee : token) : Prims.bool=
  match projectee with | Tok_STRENDS -> true | uu___ -> false
let uu___is_Tok_STRBEFORE (projectee : token) : Prims.bool=
  match projectee with | Tok_STRBEFORE -> true | uu___ -> false
let uu___is_Tok_STRAFTER (projectee : token) : Prims.bool=
  match projectee with | Tok_STRAFTER -> true | uu___ -> false
let uu___is_Tok_REPLACE (projectee : token) : Prims.bool=
  match projectee with | Tok_REPLACE -> true | uu___ -> false
let uu___is_Tok_REGEX (projectee : token) : Prims.bool=
  match projectee with | Tok_REGEX -> true | uu___ -> false
let uu___is_Tok_SUBSTR (projectee : token) : Prims.bool=
  match projectee with | Tok_SUBSTR -> true | uu___ -> false
let uu___is_Tok_ISIRI (projectee : token) : Prims.bool=
  match projectee with | Tok_ISIRI -> true | uu___ -> false
let uu___is_Tok_ISBLANK (projectee : token) : Prims.bool=
  match projectee with | Tok_ISBLANK -> true | uu___ -> false
let uu___is_Tok_ISLITERAL (projectee : token) : Prims.bool=
  match projectee with | Tok_ISLITERAL -> true | uu___ -> false
let uu___is_Tok_ISNUMERIC (projectee : token) : Prims.bool=
  match projectee with | Tok_ISNUMERIC -> true | uu___ -> false
let uu___is_Tok_SAMETERM (projectee : token) : Prims.bool=
  match projectee with | Tok_SAMETERM -> true | uu___ -> false
let uu___is_Tok_STRDT (projectee : token) : Prims.bool=
  match projectee with | Tok_STRDT -> true | uu___ -> false
let uu___is_Tok_STRLANG (projectee : token) : Prims.bool=
  match projectee with | Tok_STRLANG -> true | uu___ -> false
let uu___is_Tok_COUNT (projectee : token) : Prims.bool=
  match projectee with | Tok_COUNT -> true | uu___ -> false
let uu___is_Tok_SUM (projectee : token) : Prims.bool=
  match projectee with | Tok_SUM -> true | uu___ -> false
let uu___is_Tok_MIN_KW (projectee : token) : Prims.bool=
  match projectee with | Tok_MIN_KW -> true | uu___ -> false
let uu___is_Tok_MAX_KW (projectee : token) : Prims.bool=
  match projectee with | Tok_MAX_KW -> true | uu___ -> false
let uu___is_Tok_AVG (projectee : token) : Prims.bool=
  match projectee with | Tok_AVG -> true | uu___ -> false
let uu___is_Tok_GROUP_CONCAT (projectee : token) : Prims.bool=
  match projectee with | Tok_GROUP_CONCAT -> true | uu___ -> false
let uu___is_Tok_SAMPLE (projectee : token) : Prims.bool=
  match projectee with | Tok_SAMPLE -> true | uu___ -> false
let uu___is_Tok_SEPARATOR (projectee : token) : Prims.bool=
  match projectee with | Tok_SEPARATOR -> true | uu___ -> false
let uu___is_Tok_COALESCE (projectee : token) : Prims.bool=
  match projectee with | Tok_COALESCE -> true | uu___ -> false
let uu___is_Tok_NOW (projectee : token) : Prims.bool=
  match projectee with | Tok_NOW -> true | uu___ -> false
let uu___is_Tok_UUID (projectee : token) : Prims.bool=
  match projectee with | Tok_UUID -> true | uu___ -> false
let uu___is_Tok_STRUUID (projectee : token) : Prims.bool=
  match projectee with | Tok_STRUUID -> true | uu___ -> false
let uu___is_Tok_YEAR (projectee : token) : Prims.bool=
  match projectee with | Tok_YEAR -> true | uu___ -> false
let uu___is_Tok_MONTH (projectee : token) : Prims.bool=
  match projectee with | Tok_MONTH -> true | uu___ -> false
let uu___is_Tok_DAY (projectee : token) : Prims.bool=
  match projectee with | Tok_DAY -> true | uu___ -> false
let uu___is_Tok_HOURS (projectee : token) : Prims.bool=
  match projectee with | Tok_HOURS -> true | uu___ -> false
let uu___is_Tok_MINUTES (projectee : token) : Prims.bool=
  match projectee with | Tok_MINUTES -> true | uu___ -> false
let uu___is_Tok_SECONDS (projectee : token) : Prims.bool=
  match projectee with | Tok_SECONDS -> true | uu___ -> false
let uu___is_Tok_TIMEZONE (projectee : token) : Prims.bool=
  match projectee with | Tok_TIMEZONE -> true | uu___ -> false
let uu___is_Tok_TZ (projectee : token) : Prims.bool=
  match projectee with | Tok_TZ -> true | uu___ -> false
let uu___is_Tok_MD5 (projectee : token) : Prims.bool=
  match projectee with | Tok_MD5 -> true | uu___ -> false
let uu___is_Tok_SHA1 (projectee : token) : Prims.bool=
  match projectee with | Tok_SHA1 -> true | uu___ -> false
let uu___is_Tok_SHA256 (projectee : token) : Prims.bool=
  match projectee with | Tok_SHA256 -> true | uu___ -> false
let uu___is_Tok_SHA384 (projectee : token) : Prims.bool=
  match projectee with | Tok_SHA384 -> true | uu___ -> false
let uu___is_Tok_SHA512 (projectee : token) : Prims.bool=
  match projectee with | Tok_SHA512 -> true | uu___ -> false
let uu___is_Tok_EOF (projectee : token) : Prims.bool=
  match projectee with | Tok_EOF -> true | uu___ -> false
type pos = Prims.nat
type lex_result = (token * pos)
let char_at (s : Prims.string) (p : pos) : FStar_Char.char=
  if p < (FStar_String.strlen s)
  then FStar_String.index s p
  else FStar_Char.char_of_int Prims.int_zero
let at_end (input : Prims.string) (p : pos) : Prims.bool=
  p >= (FStar_String.strlen input)
let peek_char (input : Prims.string) (p : pos) : FStar_Char.char=
  if at_end input p
  then FStar_Char.char_of_int Prims.int_zero
  else char_at input p
let substring (s : Prims.string) (p : pos) (len : Prims.nat) : Prims.string=
  if len = Prims.int_zero
  then ""
  else
    if (p + len) <= (FStar_String.strlen s)
    then FStar_String.sub s p len
    else
      if p < (FStar_String.strlen s)
      then FStar_String.sub s p ((FStar_String.strlen s) - p)
      else ""
let char_code (c : FStar_Char.char) : Prims.nat= FStar_Char.int_of_char c
let is_alpha (c : FStar_Char.char) : Prims.bool=
  let code = char_code c in
  ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))) ||
    ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A))))
let is_digit (c : FStar_Char.char) : Prims.bool=
  let code = char_code c in
  (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
let is_alnum (c : FStar_Char.char) : Prims.bool= (is_alpha c) || (is_digit c)
let is_ws (c : FStar_Char.char) : Prims.bool=
  let code = char_code c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let is_pn_char (c : FStar_Char.char) : Prims.bool=
  ((((is_alnum c) || ((char_code c) = (Prims.of_int (0x5F)))) ||
      ((char_code c) = (Prims.of_int (0x2D))))
     || ((char_code c) = (Prims.of_int (0x2E))))
    || ((char_code c) >= (Prims.of_int (0x80)))
let is_pn_local_esc (c : FStar_Char.char) : Prims.bool=
  let code = char_code c in
  (((((((((((((((((((code = (Prims.of_int (0x5F))) ||
                      (code = (Prims.of_int (0x7E))))
                     || (code = (Prims.of_int (0x2E))))
                    || (code = (Prims.of_int (0x2D))))
                   || (code = (Prims.of_int (0x21))))
                  || (code = (Prims.of_int (0x24))))
                 || (code = (Prims.of_int (0x26))))
                || (code = (Prims.of_int (0x27))))
               || (code = (Prims.of_int (0x28))))
              || (code = (Prims.of_int (0x29))))
             || (code = (Prims.of_int (0x2A))))
            || (code = (Prims.of_int (0x2B))))
           || (code = (Prims.of_int (0x2C))))
          || (code = (Prims.of_int (0x3B))))
         || (code = (Prims.of_int (0x3D))))
        || (code = (Prims.of_int (0x2F))))
       || (code = (Prims.of_int (0x3F))))
      || (code = (Prims.of_int (0x23))))
     || (code = (Prims.of_int (0x40))))
    || (code = (Prims.of_int (0x25)))
let char_upper (c : FStar_Char.char) : FStar_Char.char=
  let cd = char_code c in
  if (cd >= (Prims.of_int (0x61))) && (cd <= (Prims.of_int (0x7A)))
  then FStar_Char.char_of_int (cd - (Prims.of_int (32)))
  else c
let string_upper (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (FStar_List_Tot_Base.map char_upper (FStar_String.list_of_string s))
let streq (a : Prims.string) (b : Prims.string) : Prims.bool= a = b
let rec skip_ws (input : Prims.string) (p : pos) : pos=
  if at_end input p
  then p
  else
    (let c = peek_char input p in
     if is_ws c
     then skip_ws input (p + Prims.int_one)
     else
       if (char_code c) = (Prims.of_int (0x23))
       then skip_comment input (p + Prims.int_one)
       else p)
and skip_comment (input : Prims.string) (p : pos) : pos=
  if at_end input p
  then p
  else
    if (char_code (peek_char input p)) = (Prims.of_int (0x0A))
    then skip_ws input (p + Prims.int_one)
    else skip_comment input (p + Prims.int_one)
let rec scan_while (input : Prims.string) (p : pos)
  (pred : FStar_Char.char -> Prims.bool) : pos=
  if at_end input p
  then p
  else
    if pred (peek_char input p)
    then scan_while input (p + Prims.int_one) pred
    else p
let rec scan_iri_body (input : Prims.string) (p : pos) (start : pos) :
  (Prims.string * pos)=
  if at_end input p
  then ((substring input start (p - start)), p)
  else
    if (char_code (peek_char input p)) = (Prims.of_int (0x3E))
    then ((substring input start (p - start)), (p + Prims.int_one))
    else scan_iri_body input (p + Prims.int_one) start
let scan_iri (input : Prims.string) (p : pos) : (Prims.string * pos)=
  scan_iri_body input p p
let rec scan_short_str (input : Prims.string) (p : pos) (start : pos)
  (q : Prims.nat) : (Prims.string * pos)=
  if at_end input p
  then ((substring input start (p - start)), p)
  else
    (let c = peek_char input p in
     if (char_code c) = (Prims.of_int (0x5C))
     then
       (if at_end input (p + Prims.int_one)
        then
          ((substring input start ((p + Prims.int_one) - start)),
            (p + Prims.int_one))
        else scan_short_str input (p + (Prims.of_int (2))) start q)
     else
       if (char_code c) = q
       then ((substring input start (p - start)), (p + Prims.int_one))
       else scan_short_str input (p + Prims.int_one) start q)
let rec scan_long_str (input : Prims.string) (p : pos) (start : pos)
  (q : Prims.nat) : (Prims.string * pos)=
  if at_end input p
  then ((substring input start (p - start)), p)
  else
    (let c = peek_char input p in
     if (char_code c) = (Prims.of_int (0x5C))
     then
       (if at_end input (p + Prims.int_one)
        then
          ((substring input start ((p + Prims.int_one) - start)),
            (p + Prims.int_one))
        else scan_long_str input (p + (Prims.of_int (2))) start q)
     else
       if
         (((((char_code c) = q) &&
              (Prims.op_Negation (at_end input (p + Prims.int_one))))
             && ((char_code (peek_char input (p + Prims.int_one))) = q))
            && (Prims.op_Negation (at_end input (p + (Prims.of_int (2))))))
           && ((char_code (peek_char input (p + (Prims.of_int (2))))) = q)
       then ((substring input start (p - start)), (p + (Prims.of_int (3))))
       else scan_long_str input (p + Prims.int_one) start q)
let scan_string (input : Prims.string) (p : pos) : (Prims.string * pos)=
  let q = char_code (peek_char input p) in
  if
    (((Prims.op_Negation (at_end input (p + Prims.int_one))) &&
        ((char_code (peek_char input (p + Prims.int_one))) = q))
       && (Prims.op_Negation (at_end input (p + (Prims.of_int (2))))))
      && ((char_code (peek_char input (p + (Prims.of_int (2))))) = q)
  then
    scan_long_str input (p + (Prims.of_int (3))) (p + (Prims.of_int (3))) q
  else scan_short_str input (p + Prims.int_one) (p + Prims.int_one) q
let keyword_of_upper (u : Prims.string) :
  token FStar_Pervasives_Native.option=
  if u = "SELECT"
  then FStar_Pervasives_Native.Some Tok_SELECT
  else
    if u = "ASK"
    then FStar_Pervasives_Native.Some Tok_ASK
    else
      if u = "CONSTRUCT"
      then FStar_Pervasives_Native.Some Tok_CONSTRUCT
      else
        if u = "DESCRIBE"
        then FStar_Pervasives_Native.Some Tok_DESCRIBE
        else
          if u = "WHERE"
          then FStar_Pervasives_Native.Some Tok_WHERE
          else
            if u = "PREFIX"
            then FStar_Pervasives_Native.Some Tok_PREFIX
            else
              if u = "BASE"
              then FStar_Pervasives_Native.Some Tok_BASE
              else
                if u = "OPTIONAL"
                then FStar_Pervasives_Native.Some Tok_OPTIONAL
                else
                  if u = "UNION"
                  then FStar_Pervasives_Native.Some Tok_UNION
                  else
                    if u = "MINUS"
                    then FStar_Pervasives_Native.Some Tok_MINUS_KW
                    else
                      if u = "FILTER"
                      then FStar_Pervasives_Native.Some Tok_FILTER
                      else
                        if u = "BIND"
                        then FStar_Pervasives_Native.Some Tok_BIND
                        else
                          if u = "VALUES"
                          then FStar_Pervasives_Native.Some Tok_VALUES
                          else
                            if u = "GRAPH"
                            then FStar_Pervasives_Native.Some Tok_GRAPH
                            else
                              if u = "SERVICE"
                              then FStar_Pervasives_Native.Some Tok_SERVICE
                              else
                                if u = "SILENT"
                                then FStar_Pervasives_Native.Some Tok_SILENT
                                else
                                  if u = "EXISTS"
                                  then
                                    FStar_Pervasives_Native.Some Tok_EXISTS
                                  else
                                    if u = "NOT"
                                    then FStar_Pervasives_Native.Some Tok_NOT
                                    else
                                      if u = "AS"
                                      then
                                        FStar_Pervasives_Native.Some Tok_AS
                                      else
                                        if u = "DISTINCT"
                                        then
                                          FStar_Pervasives_Native.Some
                                            Tok_DISTINCT
                                        else
                                          if u = "REDUCED"
                                          then
                                            FStar_Pervasives_Native.Some
                                              Tok_REDUCED
                                          else
                                            if u = "ORDER"
                                            then
                                              FStar_Pervasives_Native.Some
                                                Tok_ORDER
                                            else
                                              if u = "BY"
                                              then
                                                FStar_Pervasives_Native.Some
                                                  Tok_BY
                                              else
                                                if u = "ASC"
                                                then
                                                  FStar_Pervasives_Native.Some
                                                    Tok_ASC
                                                else
                                                  if u = "DESC"
                                                  then
                                                    FStar_Pervasives_Native.Some
                                                      Tok_DESC
                                                  else
                                                    if u = "GROUP"
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        Tok_GROUP
                                                    else
                                                      if u = "HAVING"
                                                      then
                                                        FStar_Pervasives_Native.Some
                                                          Tok_HAVING
                                                      else
                                                        if u = "LIMIT"
                                                        then
                                                          FStar_Pervasives_Native.Some
                                                            Tok_LIMIT
                                                        else
                                                          if u = "OFFSET"
                                                          then
                                                            FStar_Pervasives_Native.Some
                                                              Tok_OFFSET
                                                          else
                                                            if u = "IN"
                                                            then
                                                              FStar_Pervasives_Native.Some
                                                                Tok_IN
                                                            else
                                                              if u = "TRUE"
                                                              then
                                                                FStar_Pervasives_Native.Some
                                                                  Tok_TRUE
                                                              else
                                                                if
                                                                  u = "FALSE"
                                                                then
                                                                  FStar_Pervasives_Native.Some
                                                                    Tok_FALSE
                                                                else
                                                                  if
                                                                    u =
                                                                    "UNDEF"
                                                                  then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_UNDEF
                                                                  else
                                                                    if
                                                                    u = "A"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_A
                                                                    else
                                                                    if
                                                                    u = "STR"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_STR
                                                                    else
                                                                    if
                                                                    u =
                                                                    "LANG"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_LANG
                                                                    else
                                                                    if
                                                                    u =
                                                                    "LANGMATCHES"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_LANGMATCHES
                                                                    else
                                                                    if
                                                                    u =
                                                                    "DATATYPE"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_DATATYPE
                                                                    else
                                                                    if
                                                                    u =
                                                                    "BOUND"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_BOUND
                                                                    else
                                                                    if
                                                                    u = "IF"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_IF
                                                                    else
                                                                    if
                                                                    u = "IRI"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_IRI_KW
                                                                    else
                                                                    if
                                                                    u = "URI"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_URI
                                                                    else
                                                                    if
                                                                    u =
                                                                    "BNODE"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_BNODE_KW
                                                                    else
                                                                    if
                                                                    u =
                                                                    "RAND"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_RAND
                                                                    else
                                                                    if
                                                                    u = "ABS"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_ABS
                                                                    else
                                                                    if
                                                                    u =
                                                                    "CEIL"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_CEIL
                                                                    else
                                                                    if
                                                                    u =
                                                                    "FLOOR"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_FLOOR
                                                                    else
                                                                    if
                                                                    u =
                                                                    "ROUND"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_ROUND
                                                                    else
                                                                    if
                                                                    u =
                                                                    "CONCAT"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_CONCAT
                                                                    else
                                                                    if
                                                                    u =
                                                                    "STRLEN"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_STRLEN
                                                                    else
                                                                    if
                                                                    u =
                                                                    "UCASE"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_UCASE
                                                                    else
                                                                    if
                                                                    u =
                                                                    "LCASE"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_LCASE
                                                                    else
                                                                    if
                                                                    u =
                                                                    "ENCODE_FOR_URI"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_ENCODE_FOR_URI
                                                                    else
                                                                    if
                                                                    u =
                                                                    "CONTAINS"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_CONTAINS
                                                                    else
                                                                    if
                                                                    u =
                                                                    "STRSTARTS"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_STRSTARTS
                                                                    else
                                                                    if
                                                                    u =
                                                                    "STRENDS"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_STRENDS
                                                                    else
                                                                    if
                                                                    u =
                                                                    "STRBEFORE"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_STRBEFORE
                                                                    else
                                                                    if
                                                                    u =
                                                                    "STRAFTER"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_STRAFTER
                                                                    else
                                                                    if
                                                                    u =
                                                                    "REPLACE"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_REPLACE
                                                                    else
                                                                    if
                                                                    u =
                                                                    "REGEX"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_REGEX
                                                                    else
                                                                    if
                                                                    u =
                                                                    "SUBSTR"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_SUBSTR
                                                                    else
                                                                    if
                                                                    u =
                                                                    "ISIRI"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_ISIRI
                                                                    else
                                                                    if
                                                                    u =
                                                                    "ISURI"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_ISIRI
                                                                    else
                                                                    if
                                                                    u =
                                                                    "ISBLANK"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_ISBLANK
                                                                    else
                                                                    if
                                                                    u =
                                                                    "ISLITERAL"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_ISLITERAL
                                                                    else
                                                                    if
                                                                    u =
                                                                    "ISNUMERIC"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_ISNUMERIC
                                                                    else
                                                                    if
                                                                    u =
                                                                    "SAMETERM"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_SAMETERM
                                                                    else
                                                                    if
                                                                    u =
                                                                    "STRDT"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_STRDT
                                                                    else
                                                                    if
                                                                    u =
                                                                    "STRLANG"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_STRLANG
                                                                    else
                                                                    if
                                                                    u =
                                                                    "COUNT"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_COUNT
                                                                    else
                                                                    if
                                                                    u = "SUM"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_SUM
                                                                    else
                                                                    if
                                                                    u = "MIN"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_MIN_KW
                                                                    else
                                                                    if
                                                                    u = "MAX"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_MAX_KW
                                                                    else
                                                                    if
                                                                    u = "AVG"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_AVG
                                                                    else
                                                                    if
                                                                    u =
                                                                    "GROUP_CONCAT"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_GROUP_CONCAT
                                                                    else
                                                                    if
                                                                    u =
                                                                    "SAMPLE"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_SAMPLE
                                                                    else
                                                                    if
                                                                    u =
                                                                    "SEPARATOR"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_SEPARATOR
                                                                    else
                                                                    if
                                                                    u =
                                                                    "COALESCE"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_COALESCE
                                                                    else
                                                                    if
                                                                    u = "NOW"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_NOW
                                                                    else
                                                                    if
                                                                    u =
                                                                    "UUID"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_UUID
                                                                    else
                                                                    if
                                                                    u =
                                                                    "STRUUID"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_STRUUID
                                                                    else
                                                                    if
                                                                    u =
                                                                    "YEAR"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_YEAR
                                                                    else
                                                                    if
                                                                    u =
                                                                    "MONTH"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_MONTH
                                                                    else
                                                                    if
                                                                    u = "DAY"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_DAY
                                                                    else
                                                                    if
                                                                    u =
                                                                    "HOURS"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_HOURS
                                                                    else
                                                                    if
                                                                    u =
                                                                    "MINUTES"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_MINUTES
                                                                    else
                                                                    if
                                                                    u =
                                                                    "SECONDS"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_SECONDS
                                                                    else
                                                                    if
                                                                    u =
                                                                    "TIMEZONE"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_TIMEZONE
                                                                    else
                                                                    if
                                                                    u = "TZ"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_TZ
                                                                    else
                                                                    if
                                                                    u = "MD5"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_MD5
                                                                    else
                                                                    if
                                                                    u =
                                                                    "SHA1"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_SHA1
                                                                    else
                                                                    if
                                                                    u =
                                                                    "SHA256"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_SHA256
                                                                    else
                                                                    if
                                                                    u =
                                                                    "SHA384"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_SHA384
                                                                    else
                                                                    if
                                                                    u =
                                                                    "SHA512"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    Tok_SHA512
                                                                    else
                                                                    FStar_Pervasives_Native.None
let scan_pname_or_keyword (input : Prims.string) (p : pos) : lex_result=
  let p' =
    scan_while input p
      (fun c -> (is_pn_char c) || ((char_code c) = (Prims.of_int (0x3A)))) in
  let word = substring input p (p' - p) in
  let has_colon = RDF_Graph_Executable.string_contains_colon word in
  if has_colon
  then ((Tok_PNAME word), p')
  else
    (match keyword_of_upper (string_upper word) with
     | FStar_Pervasives_Native.Some tok -> (tok, p')
     | FStar_Pervasives_Native.None -> ((Tok_PNAME word), p'))
let scan_number (input : Prims.string) (p : pos) : lex_result=
  let p' = scan_while input p is_digit in
  if
    (Prims.op_Negation (at_end input p')) &&
      ((char_code (peek_char input p')) = (Prims.of_int (0x2E)))
  then
    let p'' = scan_while input (p' + Prims.int_one) is_digit in
    (if
       (Prims.op_Negation (at_end input p'')) &&
         (((char_code (peek_char input p'')) = (Prims.of_int (0x45))) ||
            ((char_code (peek_char input p'')) = (Prims.of_int (0x65))))
     then
       let p3 = p'' + Prims.int_one in
       let p31 =
         if
           (Prims.op_Negation (at_end input p3)) &&
             (((char_code (peek_char input p3)) = (Prims.of_int (0x2B))) ||
                ((char_code (peek_char input p3)) = (Prims.of_int (0x2D))))
         then p3 + Prims.int_one
         else p3 in
       let p4 = scan_while input p31 is_digit in
       ((Tok_DOUBLE (substring input p (p4 - p))), p4)
     else ((Tok_DECIMAL (substring input p (p'' - p))), p''))
  else
    if
      (Prims.op_Negation (at_end input p')) &&
        (((char_code (peek_char input p')) = (Prims.of_int (0x45))) ||
           ((char_code (peek_char input p')) = (Prims.of_int (0x65))))
    then
      (let p'' = p' + Prims.int_one in
       let p''1 =
         if
           (Prims.op_Negation (at_end input p'')) &&
             (((char_code (peek_char input p'')) = (Prims.of_int (0x2B))) ||
                ((char_code (peek_char input p'')) = (Prims.of_int (0x2D))))
         then p'' + Prims.int_one
         else p'' in
       let p3 = scan_while input p''1 is_digit in
       ((Tok_DOUBLE (substring input p (p3 - p))), p3))
    else ((Tok_INTEGER (substring input p (p' - p))), p')
let scan_bnode_label (input : Prims.string) (p : pos) : (Prims.string * pos)=
  let p' = scan_while input p is_pn_char in
  let rec trim_dots q =
    if q <= p
    then p
    else
      if
        (char_code (char_at input (q - Prims.int_one))) =
          (Prims.of_int (0x2E))
      then trim_dots (q - Prims.int_one)
      else q in
  let p'' = trim_dots p' in ((substring input p (p'' - p)), p'')
let scan_var_name (input : Prims.string) (p : pos) : (Prims.string * pos)=
  let p' =
    scan_while input p
      (fun c -> (is_alnum c) || ((char_code c) = (Prims.of_int (0x5F)))) in
  ((substring input p (p' - p)), p')
let rec scan_lang_subtags (input : Prims.string) (p : pos) (fuel : Prims.nat)
  : pos=
  if fuel = Prims.int_zero
  then p
  else
    if
      (Prims.op_Negation (at_end input p)) &&
        ((char_code (peek_char input p)) = (Prims.of_int (0x2D)))
    then
      (let p' = scan_while input (p + Prims.int_one) is_alnum in
       if p' > (p + Prims.int_one)
       then scan_lang_subtags input p' (fuel - Prims.int_one)
       else p)
    else p
let scan_langtag (input : Prims.string) (p : pos) : (Prims.string * pos)=
  let p' = scan_while input p is_alpha in
  if p' = p
  then ("", p)
  else
    (let p'' = scan_lang_subtags input p' (Prims.of_int (20)) in
     ((substring input p (p'' - p)), p''))
let next_token (input : Prims.string) (p : pos) : lex_result=
  let p1 = skip_ws input p in
  if at_end input p1
  then (Tok_EOF, p1)
  else
    (let c = peek_char input p1 in
     let code = char_code c in
     if code = (Prims.of_int (0x3C))
     then
       (if
          (Prims.op_Negation (at_end input (p1 + Prims.int_one))) &&
            ((char_code (peek_char input (p1 + Prims.int_one))) =
               (Prims.of_int (0x3D)))
        then (Tok_LE, (p1 + (Prims.of_int (2))))
        else
          (let uu___2 = scan_iri input (p1 + Prims.int_one) in
           match uu___2 with | (iri, p') -> ((Tok_IRI iri), p')))
     else
       if code = (Prims.of_int (0x3E))
       then
         (if
            (Prims.op_Negation (at_end input (p1 + Prims.int_one))) &&
              ((char_code (peek_char input (p1 + Prims.int_one))) =
                 (Prims.of_int (0x3D)))
          then (Tok_GE, (p1 + (Prims.of_int (2))))
          else (Tok_GT, (p1 + Prims.int_one)))
       else
         if code = (Prims.of_int (0x7B))
         then (Tok_LBRACE, (p1 + Prims.int_one))
         else
           if code = (Prims.of_int (0x7D))
           then (Tok_RBRACE, (p1 + Prims.int_one))
           else
             if code = (Prims.of_int (0x28))
             then (Tok_LPAREN, (p1 + Prims.int_one))
             else
               if code = (Prims.of_int (0x29))
               then (Tok_RPAREN, (p1 + Prims.int_one))
               else
                 if code = (Prims.of_int (0x5B))
                 then (Tok_LBRACKET, (p1 + Prims.int_one))
                 else
                   if code = (Prims.of_int (0x5D))
                   then (Tok_RBRACKET, (p1 + Prims.int_one))
                   else
                     if code = (Prims.of_int (0x2E))
                     then (Tok_DOT, (p1 + Prims.int_one))
                     else
                       if code = (Prims.of_int (0x3B))
                       then (Tok_SEMI, (p1 + Prims.int_one))
                       else
                         if code = (Prims.of_int (0x2C))
                         then (Tok_COMMA, (p1 + Prims.int_one))
                         else
                           if code = (Prims.of_int (0x2A))
                           then (Tok_STAR, (p1 + Prims.int_one))
                           else
                             if code = (Prims.of_int (0x2F))
                             then (Tok_SLASH, (p1 + Prims.int_one))
                             else
                               if code = (Prims.of_int (0x7C))
                               then
                                 (if
                                    (Prims.op_Negation
                                       (at_end input (p1 + Prims.int_one)))
                                      &&
                                      ((char_code
                                          (peek_char input
                                             (p1 + Prims.int_one)))
                                         = (Prims.of_int (0x7C)))
                                  then (Tok_OR, (p1 + (Prims.of_int (2))))
                                  else (Tok_PIPE, (p1 + Prims.int_one)))
                               else
                                 if code = (Prims.of_int (0x5E))
                                 then
                                   (if
                                      (Prims.op_Negation
                                         (at_end input (p1 + Prims.int_one)))
                                        &&
                                        ((char_code
                                            (peek_char input
                                               (p1 + Prims.int_one)))
                                           = (Prims.of_int (0x5E)))
                                    then
                                      (Tok_HATHAT, (p1 + (Prims.of_int (2))))
                                    else (Tok_CARET, (p1 + Prims.int_one)))
                                 else
                                   if code = (Prims.of_int (0x21))
                                   then
                                     (if
                                        (Prims.op_Negation
                                           (at_end input (p1 + Prims.int_one)))
                                          &&
                                          ((char_code
                                              (peek_char input
                                                 (p1 + Prims.int_one)))
                                             = (Prims.of_int (0x3D)))
                                      then
                                        (Tok_NE, (p1 + (Prims.of_int (2))))
                                      else (Tok_BANG, (p1 + Prims.int_one)))
                                   else
                                     if code = (Prims.of_int (0x3D))
                                     then (Tok_EQ, (p1 + Prims.int_one))
                                     else
                                       if code = (Prims.of_int (0x26))
                                       then
                                         (if
                                            (Prims.op_Negation
                                               (at_end input
                                                  (p1 + Prims.int_one)))
                                              &&
                                              ((char_code
                                                  (peek_char input
                                                     (p1 + Prims.int_one)))
                                                 = (Prims.of_int (0x26)))
                                          then
                                            (Tok_AND,
                                              (p1 + (Prims.of_int (2))))
                                          else
                                            (Tok_AND,
                                              (p1 + (Prims.of_int (2)))))
                                       else
                                         if
                                           (code = (Prims.of_int (0x3F))) ||
                                             (code = (Prims.of_int (0x24)))
                                         then
                                           (let uu___19 =
                                              scan_var_name input
                                                (p1 + Prims.int_one) in
                                            match uu___19 with
                                            | (name, p') ->
                                                if
                                                  (FStar_String.strlen name)
                                                    = Prims.int_zero
                                                then
                                                  (Tok_QMARK,
                                                    (p1 + Prims.int_one))
                                                else ((Tok_VAR name), p'))
                                         else
                                           if
                                             (code = (Prims.of_int (0x22)))
                                               ||
                                               (code = (Prims.of_int (0x27)))
                                           then
                                             (let uu___20 =
                                                scan_string input p1 in
                                              match uu___20 with
                                              | (s, p') ->
                                                  ((Tok_STRING s), p'))
                                           else
                                             if code = (Prims.of_int (0x40))
                                             then
                                               (let uu___21 =
                                                  scan_langtag input
                                                    (p1 + Prims.int_one) in
                                                match uu___21 with
                                                | (tag, p') ->
                                                    ((Tok_LANGTAG tag), p'))
                                             else
                                               if
                                                 code = (Prims.of_int (0x2B))
                                               then
                                                 (Tok_PLUS,
                                                   (p1 + Prims.int_one))
                                               else
                                                 if
                                                   code =
                                                     (Prims.of_int (0x2D))
                                                 then
                                                   (Tok_MINUS_OP,
                                                     (p1 + Prims.int_one))
                                                 else
                                                   if
                                                     code =
                                                       (Prims.of_int (0x5F))
                                                   then
                                                     (if
                                                        (Prims.op_Negation
                                                           (at_end input
                                                              (p1 +
                                                                 Prims.int_one)))
                                                          &&
                                                          ((char_code
                                                              (peek_char
                                                                 input
                                                                 (p1 +
                                                                    Prims.int_one)))
                                                             =
                                                             (Prims.of_int (0x3A)))
                                                      then
                                                        let uu___24 =
                                                          scan_bnode_label
                                                            input
                                                            (p1 +
                                                               (Prims.of_int (2))) in
                                                        match uu___24 with
                                                        | (label, p') ->
                                                            ((Tok_BNODE label),
                                                              p')
                                                      else
                                                        scan_pname_or_keyword
                                                          input p1)
                                                   else
                                                     if is_digit c
                                                     then
                                                       scan_number input p1
                                                     else
                                                       if
                                                         ((is_alpha c) ||
                                                            (code =
                                                               (Prims.of_int (0x3A))))
                                                           ||
                                                           (code >=
                                                              (Prims.of_int (0x80)))
                                                       then
                                                         scan_pname_or_keyword
                                                           input p1
                                                       else
                                                         (Tok_EOF,
                                                           (p1 +
                                                              Prims.int_one)))
type 'a parse_result =
  | ParseOk of 'a * token Prims.list 
  | ParseErr of Prims.string 
let uu___is_ParseOk (projectee : 'a parse_result) : Prims.bool=
  match projectee with | ParseOk (v, remaining) -> true | uu___ -> false
let __proj__ParseOk__item__v (projectee : 'a parse_result) : 'a=
  match projectee with | ParseOk (v, remaining) -> v
let __proj__ParseOk__item__remaining (projectee : 'a parse_result) :
  token Prims.list=
  match projectee with | ParseOk (v, remaining) -> remaining
let uu___is_ParseErr (projectee : 'a parse_result) : Prims.bool=
  match projectee with | ParseErr msg -> true | uu___ -> false
let __proj__ParseErr__item__msg (projectee : 'a parse_result) : Prims.string=
  match projectee with | ParseErr msg -> msg
type token_stream = token Prims.list
let is_eof (t : token) : Prims.bool=
  match t with | Tok_EOF -> true | uu___ -> false
let rec tokenize_acc (input : Prims.string) (p : pos)
  (acc : token Prims.list) (fuel : Prims.nat) : token Prims.list=
  if fuel = Prims.int_zero
  then FStar_List_Tot_Base.rev (Tok_EOF :: acc)
  else
    (let uu___1 = next_token input p in
     match uu___1 with
     | (tok, p') ->
         if is_eof tok
         then FStar_List_Tot_Base.rev (Tok_EOF :: acc)
         else tokenize_acc input p' (tok :: acc) (fuel - Prims.int_one))
let tokenize (input : Prims.string) : token Prims.list=
  tokenize_acc input Prims.int_zero []
    ((FStar_String.strlen input) + (Prims.of_int (100)))
let parse_ok (v : 'a) (ts : token_stream) : 'a parse_result= ParseOk (v, ts)
let parse_err (msg : Prims.string) : 'a parse_result= ParseErr msg
let parse_bind (p : 'a parse_result)
  (f : 'a -> token_stream -> 'b parse_result) : 'b parse_result=
  match p with | ParseOk (v, ts) -> f v ts | ParseErr msg -> ParseErr msg
let parse_peek (ts : token_stream) : token=
  match ts with | [] -> Tok_EOF | t::uu___ -> t
let parse_advance (ts : token_stream) : token_stream=
  match ts with | [] -> [] | uu___::rest -> rest
let token_eq (t1 : token) (t2 : token) : Prims.bool=
  match (t1, t2) with
  | (Tok_SELECT, Tok_SELECT) -> true
  | (Tok_ASK, Tok_ASK) -> true
  | (Tok_CONSTRUCT, Tok_CONSTRUCT) -> true
  | (Tok_DESCRIBE, Tok_DESCRIBE) -> true
  | (Tok_WHERE, Tok_WHERE) -> true
  | (Tok_PREFIX, Tok_PREFIX) -> true
  | (Tok_BASE, Tok_BASE) -> true
  | (Tok_OPTIONAL, Tok_OPTIONAL) -> true
  | (Tok_UNION, Tok_UNION) -> true
  | (Tok_MINUS_KW, Tok_MINUS_KW) -> true
  | (Tok_FILTER, Tok_FILTER) -> true
  | (Tok_BIND, Tok_BIND) -> true
  | (Tok_VALUES, Tok_VALUES) -> true
  | (Tok_GRAPH, Tok_GRAPH) -> true
  | (Tok_SERVICE, Tok_SERVICE) -> true
  | (Tok_SILENT, Tok_SILENT) -> true
  | (Tok_EXISTS, Tok_EXISTS) -> true
  | (Tok_NOT, Tok_NOT) -> true
  | (Tok_AS, Tok_AS) -> true
  | (Tok_DISTINCT, Tok_DISTINCT) -> true
  | (Tok_REDUCED, Tok_REDUCED) -> true
  | (Tok_ORDER, Tok_ORDER) -> true
  | (Tok_BY, Tok_BY) -> true
  | (Tok_ASC, Tok_ASC) -> true
  | (Tok_DESC, Tok_DESC) -> true
  | (Tok_GROUP, Tok_GROUP) -> true
  | (Tok_HAVING, Tok_HAVING) -> true
  | (Tok_LIMIT, Tok_LIMIT) -> true
  | (Tok_OFFSET, Tok_OFFSET) -> true
  | (Tok_IN, Tok_IN) -> true
  | (Tok_TRUE, Tok_TRUE) -> true
  | (Tok_FALSE, Tok_FALSE) -> true
  | (Tok_UNDEF, Tok_UNDEF) -> true
  | (Tok_A, Tok_A) -> true
  | (Tok_LBRACE, Tok_LBRACE) -> true
  | (Tok_RBRACE, Tok_RBRACE) -> true
  | (Tok_LPAREN, Tok_LPAREN) -> true
  | (Tok_RPAREN, Tok_RPAREN) -> true
  | (Tok_LBRACKET, Tok_LBRACKET) -> true
  | (Tok_RBRACKET, Tok_RBRACKET) -> true
  | (Tok_DOT, Tok_DOT) -> true
  | (Tok_SEMI, Tok_SEMI) -> true
  | (Tok_COMMA, Tok_COMMA) -> true
  | (Tok_STAR, Tok_STAR) -> true
  | (Tok_SLASH, Tok_SLASH) -> true
  | (Tok_PIPE, Tok_PIPE) -> true
  | (Tok_CARET, Tok_CARET) -> true
  | (Tok_BANG, Tok_BANG) -> true
  | (Tok_QMARK, Tok_QMARK) -> true
  | (Tok_PLUS, Tok_PLUS) -> true
  | (Tok_MINUS_OP, Tok_MINUS_OP) -> true
  | (Tok_EQ, Tok_EQ) -> true
  | (Tok_NE, Tok_NE) -> true
  | (Tok_LT, Tok_LT) -> true
  | (Tok_GT, Tok_GT) -> true
  | (Tok_LE, Tok_LE) -> true
  | (Tok_GE, Tok_GE) -> true
  | (Tok_AND, Tok_AND) -> true
  | (Tok_OR, Tok_OR) -> true
  | (Tok_HATHAT, Tok_HATHAT) -> true
  | (Tok_ANON, Tok_ANON) -> true
  | (Tok_EOF, Tok_EOF) -> true
  | (Tok_STR, Tok_STR) -> true
  | (Tok_LANG, Tok_LANG) -> true
  | (Tok_LANGMATCHES, Tok_LANGMATCHES) -> true
  | (Tok_DATATYPE, Tok_DATATYPE) -> true
  | (Tok_BOUND, Tok_BOUND) -> true
  | (Tok_IF, Tok_IF) -> true
  | (Tok_IRI_KW, Tok_IRI_KW) -> true
  | (Tok_URI, Tok_URI) -> true
  | (Tok_BNODE_KW, Tok_BNODE_KW) -> true
  | (Tok_RAND, Tok_RAND) -> true
  | (Tok_ABS, Tok_ABS) -> true
  | (Tok_CEIL, Tok_CEIL) -> true
  | (Tok_FLOOR, Tok_FLOOR) -> true
  | (Tok_ROUND, Tok_ROUND) -> true
  | (Tok_CONCAT, Tok_CONCAT) -> true
  | (Tok_STRLEN, Tok_STRLEN) -> true
  | (Tok_UCASE, Tok_UCASE) -> true
  | (Tok_LCASE, Tok_LCASE) -> true
  | (Tok_ENCODE_FOR_URI, Tok_ENCODE_FOR_URI) -> true
  | (Tok_CONTAINS, Tok_CONTAINS) -> true
  | (Tok_STRSTARTS, Tok_STRSTARTS) -> true
  | (Tok_STRENDS, Tok_STRENDS) -> true
  | (Tok_STRBEFORE, Tok_STRBEFORE) -> true
  | (Tok_STRAFTER, Tok_STRAFTER) -> true
  | (Tok_REPLACE, Tok_REPLACE) -> true
  | (Tok_REGEX, Tok_REGEX) -> true
  | (Tok_SUBSTR, Tok_SUBSTR) -> true
  | (Tok_ISIRI, Tok_ISIRI) -> true
  | (Tok_ISBLANK, Tok_ISBLANK) -> true
  | (Tok_ISLITERAL, Tok_ISLITERAL) -> true
  | (Tok_ISNUMERIC, Tok_ISNUMERIC) -> true
  | (Tok_SAMETERM, Tok_SAMETERM) -> true
  | (Tok_STRDT, Tok_STRDT) -> true
  | (Tok_STRLANG, Tok_STRLANG) -> true
  | (Tok_COUNT, Tok_COUNT) -> true
  | (Tok_SUM, Tok_SUM) -> true
  | (Tok_MIN_KW, Tok_MIN_KW) -> true
  | (Tok_MAX_KW, Tok_MAX_KW) -> true
  | (Tok_AVG, Tok_AVG) -> true
  | (Tok_GROUP_CONCAT, Tok_GROUP_CONCAT) -> true
  | (Tok_SAMPLE, Tok_SAMPLE) -> true
  | (Tok_SEPARATOR, Tok_SEPARATOR) -> true
  | (Tok_COALESCE, Tok_COALESCE) -> true
  | (Tok_NOW, Tok_NOW) -> true
  | (Tok_UUID, Tok_UUID) -> true
  | (Tok_STRUUID, Tok_STRUUID) -> true
  | (Tok_YEAR, Tok_YEAR) -> true
  | (Tok_MONTH, Tok_MONTH) -> true
  | (Tok_DAY, Tok_DAY) -> true
  | (Tok_HOURS, Tok_HOURS) -> true
  | (Tok_MINUTES, Tok_MINUTES) -> true
  | (Tok_SECONDS, Tok_SECONDS) -> true
  | (Tok_TIMEZONE, Tok_TIMEZONE) -> true
  | (Tok_TZ, Tok_TZ) -> true
  | (Tok_MD5, Tok_MD5) -> true
  | (Tok_SHA1, Tok_SHA1) -> true
  | (Tok_SHA256, Tok_SHA256) -> true
  | (Tok_SHA384, Tok_SHA384) -> true
  | (Tok_SHA512, Tok_SHA512) -> true
  | (Tok_IRI s1, Tok_IRI s2) -> s1 = s2
  | (Tok_PNAME s1, Tok_PNAME s2) -> s1 = s2
  | (Tok_VAR s1, Tok_VAR s2) -> s1 = s2
  | (Tok_STRING s1, Tok_STRING s2) -> s1 = s2
  | (Tok_LANGTAG s1, Tok_LANGTAG s2) -> s1 = s2
  | (Tok_INTEGER s1, Tok_INTEGER s2) -> s1 = s2
  | (Tok_DECIMAL s1, Tok_DECIMAL s2) -> s1 = s2
  | (Tok_DOUBLE s1, Tok_DOUBLE s2) -> s1 = s2
  | (Tok_BNODE s1, Tok_BNODE s2) -> s1 = s2
  | (uu___, uu___1) -> false
let parse_expect (tok : token) (ts : token_stream) : unit parse_result=
  match ts with
  | t::rest ->
      if token_eq t tok
      then ParseOk ((), rest)
      else ParseErr "unexpected token"
  | [] -> ParseErr "unexpected end of input"
type prefix_map = (Prims.string * Prims.string) Prims.list
let rec lookup_prefix (prefix : Prims.string) (pm : prefix_map) :
  Prims.string FStar_Pervasives_Native.option=
  match pm with
  | [] -> FStar_Pervasives_Native.None
  | (k, v)::rest ->
      if k = prefix
      then FStar_Pervasives_Native.Some v
      else lookup_prefix prefix rest
let rec find_colon (cs : FStar_Char.char Prims.list) (i : Prims.nat) :
  Prims.nat=
  match cs with
  | [] -> i
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x3A))
      then i
      else find_colon rest (i + Prims.int_one)
let split_pname (pn : Prims.string) : (Prims.string * Prims.string)=
  let chars = FStar_String.list_of_string pn in
  let cp = find_colon chars Prims.int_zero in
  if cp >= (FStar_String.strlen pn)
  then (pn, "")
  else
    ((substring pn Prims.int_zero cp),
      (substring pn (cp + Prims.int_one)
         (((FStar_String.strlen pn) - cp) - Prims.int_one)))
let resolve_pname (pn : Prims.string) (pm : prefix_map) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ = split_pname pn in
  match uu___ with
  | (prefix, local) ->
      (match lookup_prefix prefix pm with
       | FStar_Pervasives_Native.Some ns ->
           FStar_Pervasives_Native.Some (Prims.strcat ns local)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let make_iri (s : Prims.string) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri s
  then FStar_Pervasives_Native.Some s
  else FStar_Pervasives_Native.None
let default_modifier : SPARQL11_Algebra.solution_modifier=
  {
    SPARQL11_Algebra.sm_order_by = FStar_Pervasives_Native.None;
    SPARQL11_Algebra.sm_distinct = false;
    SPARQL11_Algebra.sm_reduced = false;
    SPARQL11_Algebra.sm_offset = FStar_Pervasives_Native.None;
    SPARQL11_Algebra.sm_limit = FStar_Pervasives_Native.None
  }
let rec chars_to_int (cs : FStar_Char.char Prims.list) (acc : Prims.int) :
  Prims.int=
  match cs with
  | [] -> acc
  | c::rest ->
      chars_to_int rest
        ((acc * (Prims.of_int (10))) +
           ((FStar_Char.int_of_char c) - (Prims.of_int (0x30))))
let parse_int_str (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  let cs = FStar_String.list_of_string s in
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x2D))
      then
        (if
           ((FStar_List_Tot_Base.length rest) > Prims.int_zero) &&
             (FStar_List_Tot_Base.for_all (fun c1 -> is_digit c1) rest)
         then
           FStar_Pervasives_Native.Some
             (Prims.int_zero - (chars_to_int rest Prims.int_zero))
         else FStar_Pervasives_Native.None)
      else
        if (FStar_Char.int_of_char c) = (Prims.of_int (0x2B))
        then
          (if
             ((FStar_List_Tot_Base.length rest) > Prims.int_zero) &&
               (FStar_List_Tot_Base.for_all (fun c1 -> is_digit c1) rest)
           then
             FStar_Pervasives_Native.Some (chars_to_int rest Prims.int_zero)
           else FStar_Pervasives_Native.None)
        else
          if FStar_List_Tot_Base.for_all (fun c1 -> is_digit c1) cs
          then FStar_Pervasives_Native.Some (chars_to_int cs Prims.int_zero)
          else FStar_Pervasives_Native.None
let make_plain_literal (lex : Prims.string) :
  RDF_Graph_Executable.wf_literal=
  {
    RDF_Graph_Executable.lexical_form = lex;
    RDF_Graph_Executable.datatype = "http://www.w3.org/2001/XMLSchema#string";
    RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
  }
let make_typed_literal (lex : Prims.string) (dt : Prims.string) :
  RDF_Graph_Executable.wf_literal FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri dt
  then
    (if dt = "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"
     then FStar_Pervasives_Native.None
     else
       FStar_Pervasives_Native.Some
         {
           RDF_Graph_Executable.lexical_form = lex;
           RDF_Graph_Executable.datatype = dt;
           RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
         })
  else FStar_Pervasives_Native.None
let make_lang_literal (lex : Prims.string) (lang : Prims.string) :
  RDF_Graph_Executable.wf_literal=
  {
    RDF_Graph_Executable.lexical_form = lex;
    RDF_Graph_Executable.datatype =
      "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString";
    RDF_Graph_Executable.lang_tag = (FStar_Pervasives_Native.Some lang)
  }
let rdf_type_iri_str : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rec parse_expr (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else parse_or_expr pm (fuel - Prims.int_one) ts
and parse_or_expr (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_and_expr pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (e, ts') -> parse_or_rest pm (fuel - Prims.int_one) e ts')
and parse_or_rest (pm : prefix_map) (fuel : Prims.nat)
  (e : SPARQL11_Algebra.expr) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseOk (e, ts)
  else
    (match parse_peek ts with
     | Tok_OR ->
         (match parse_and_expr pm (fuel - Prims.int_one) (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (e2, ts') ->
              parse_or_rest pm (fuel - Prims.int_one)
                (SPARQL11_Algebra.E_Or (e, e2)) ts')
     | uu___1 -> ParseOk (e, ts))
and parse_and_expr (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_rel_expr pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (e, ts') -> parse_and_rest pm (fuel - Prims.int_one) e ts')
and parse_and_rest (pm : prefix_map) (fuel : Prims.nat)
  (e : SPARQL11_Algebra.expr) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseOk (e, ts)
  else
    (match parse_peek ts with
     | Tok_AND ->
         (match parse_rel_expr pm (fuel - Prims.int_one) (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (e2, ts') ->
              parse_and_rest pm (fuel - Prims.int_one)
                (SPARQL11_Algebra.E_And (e, e2)) ts')
     | uu___1 -> ParseOk (e, ts))
and parse_rel_expr (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_add_expr pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (e1, ts') ->
         (match parse_peek ts' with
          | Tok_EQ ->
              parse_rel_rhs pm (fuel - Prims.int_one)
                (fun uu___1 ->
                   SPARQL11_Algebra.E_Compare
                     (SPARQL11_Algebra.CmpEq, e1, uu___1)) ts'
          | Tok_NE ->
              parse_rel_rhs pm (fuel - Prims.int_one)
                (fun uu___1 ->
                   SPARQL11_Algebra.E_Compare
                     (SPARQL11_Algebra.CmpNe, e1, uu___1)) ts'
          | Tok_LT ->
              parse_rel_rhs pm (fuel - Prims.int_one)
                (fun uu___1 ->
                   SPARQL11_Algebra.E_Compare
                     (SPARQL11_Algebra.CmpLt, e1, uu___1)) ts'
          | Tok_GT ->
              parse_rel_rhs pm (fuel - Prims.int_one)
                (fun uu___1 ->
                   SPARQL11_Algebra.E_Compare
                     (SPARQL11_Algebra.CmpGt, e1, uu___1)) ts'
          | Tok_LE ->
              parse_rel_rhs pm (fuel - Prims.int_one)
                (fun uu___1 ->
                   SPARQL11_Algebra.E_Compare
                     (SPARQL11_Algebra.CmpLe, e1, uu___1)) ts'
          | Tok_GE ->
              parse_rel_rhs pm (fuel - Prims.int_one)
                (fun uu___1 ->
                   SPARQL11_Algebra.E_Compare
                     (SPARQL11_Algebra.CmpGe, e1, uu___1)) ts'
          | Tok_IN ->
              parse_in_list pm (fuel - Prims.int_one) e1 (parse_advance ts')
          | Tok_NOT ->
              let ts'' = parse_advance ts' in
              (match parse_peek ts'' with
               | Tok_IN ->
                   parse_not_in_list pm (fuel - Prims.int_one) e1
                     (parse_advance ts'')
               | uu___1 -> ParseOk (e1, ts'))
          | uu___1 -> ParseOk (e1, ts')))
and parse_rel_rhs (pm : prefix_map) (fuel : Prims.nat)
  (ctor : SPARQL11_Algebra.expr -> SPARQL11_Algebra.expr) (ts : token_stream)
  : SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_add_expr pm (fuel - Prims.int_one) (parse_advance ts) with
     | ParseErr m -> ParseErr m
     | ParseOk (e2, ts') -> ParseOk ((ctor e2), ts'))
and parse_in_list (pm : prefix_map) (fuel : Prims.nat)
  (e : SPARQL11_Algebra.expr) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts') ->
         (match parse_expr_list pm (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (es, ts'') ->
              (match parse_expect Tok_RPAREN ts'' with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts''') ->
                   ParseOk ((SPARQL11_Algebra.E_In (e, es)), ts'''))))
and parse_not_in_list (pm : prefix_map) (fuel : Prims.nat)
  (e : SPARQL11_Algebra.expr) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts') ->
         (match parse_expr_list pm (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (es, ts'') ->
              (match parse_expect Tok_RPAREN ts'' with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts''') ->
                   ParseOk ((SPARQL11_Algebra.E_NotIn (e, es)), ts'''))))
and parse_expr_list (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream)
  : SPARQL11_Algebra.expr Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ([], ts)
  else
    (match parse_peek ts with
     | Tok_RPAREN -> ParseOk ([], ts)
     | uu___1 ->
         (match parse_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_expr_list_rest pm (fuel - Prims.int_one) [e] ts'))
and parse_expr_list_rest (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.expr Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.expr Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_COMMA ->
         (match parse_expr pm (fuel - Prims.int_one) (parse_advance ts) with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_expr_list_rest pm (fuel - Prims.int_one) (e :: acc) ts')
     | uu___1 -> ParseOk ((FStar_List_Tot_Base.rev acc), ts))
and parse_add_expr (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_mul_expr pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (e, ts') -> parse_add_rest pm (fuel - Prims.int_one) e ts')
and parse_add_rest (pm : prefix_map) (fuel : Prims.nat)
  (e : SPARQL11_Algebra.expr) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseOk (e, ts)
  else
    (match parse_peek ts with
     | Tok_PLUS ->
         (match parse_mul_expr pm (fuel - Prims.int_one) (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (e2, ts') ->
              parse_add_rest pm (fuel - Prims.int_one)
                (SPARQL11_Algebra.E_Arith (SPARQL11_Algebra.Add, e, e2)) ts')
     | Tok_MINUS_OP ->
         (match parse_mul_expr pm (fuel - Prims.int_one) (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (e2, ts') ->
              parse_add_rest pm (fuel - Prims.int_one)
                (SPARQL11_Algebra.E_Arith (SPARQL11_Algebra.Sub, e, e2)) ts')
     | uu___1 -> ParseOk (e, ts))
and parse_mul_expr (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_unary_expr pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (e, ts') -> parse_mul_rest pm (fuel - Prims.int_one) e ts')
and parse_mul_rest (pm : prefix_map) (fuel : Prims.nat)
  (e : SPARQL11_Algebra.expr) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseOk (e, ts)
  else
    (match parse_peek ts with
     | Tok_STAR ->
         (match parse_unary_expr pm (fuel - Prims.int_one) (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (e2, ts') ->
              parse_mul_rest pm (fuel - Prims.int_one)
                (SPARQL11_Algebra.E_Arith (SPARQL11_Algebra.Mul, e, e2)) ts')
     | Tok_SLASH ->
         (match parse_unary_expr pm (fuel - Prims.int_one) (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (e2, ts') ->
              parse_mul_rest pm (fuel - Prims.int_one)
                (SPARQL11_Algebra.E_Arith (SPARQL11_Algebra.Div, e, e2)) ts')
     | uu___1 -> ParseOk (e, ts))
and parse_unary_expr (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream)
  : SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_BANG ->
         (match parse_primary_expr pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') -> ParseOk ((SPARQL11_Algebra.E_Not e), ts'))
     | Tok_PLUS ->
         (match parse_primary_expr pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              ParseOk ((SPARQL11_Algebra.E_UnaryPlus e), ts'))
     | Tok_MINUS_OP ->
         (match parse_primary_expr pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              ParseOk ((SPARQL11_Algebra.E_UnaryMinus e), ts'))
     | uu___1 -> parse_primary_expr pm (fuel - Prims.int_one) ts)
and parse_primary_expr (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v -> ParseOk ((SPARQL11_Algebra.E_Var v), (parse_advance ts))
     | Tok_TRUE ->
         ParseOk ((SPARQL11_Algebra.E_BoolLit true), (parse_advance ts))
     | Tok_FALSE ->
         ParseOk ((SPARQL11_Algebra.E_BoolLit false), (parse_advance ts))
     | Tok_INTEGER n ->
         (match parse_int_str n with
          | FStar_Pervasives_Native.Some i ->
              ParseOk ((SPARQL11_Algebra.E_NumericLit i), (parse_advance ts))
          | FStar_Pervasives_Native.None ->
              ParseOk ((SPARQL11_Algebra.E_DecimalLit n), (parse_advance ts)))
     | Tok_DECIMAL d ->
         ParseOk ((SPARQL11_Algebra.E_DecimalLit d), (parse_advance ts))
     | Tok_DOUBLE d ->
         ParseOk ((SPARQL11_Algebra.E_DoubleLit d), (parse_advance ts))
     | Tok_STRING s ->
         parse_rdf_literal_expr pm (fuel - Prims.int_one) s
           (parse_advance ts)
     | Tok_IRI i ->
         if RDF_Graph_Executable.is_iri i
         then
           let ts' = parse_advance ts in
           (match parse_peek ts' with
            | Tok_LPAREN ->
                parse_func_call pm (fuel - Prims.int_one) i
                  (parse_advance ts')
            | uu___1 -> ParseOk ((SPARQL11_Algebra.E_IRI i), ts'))
         else ParseErr (Prims.strcat "invalid IRI: " i)
     | Tok_PNAME pn ->
         parse_pname_expr pm (fuel - Prims.int_one) pn (parse_advance ts)
     | Tok_LPAREN ->
         (match parse_expr pm (fuel - Prims.int_one) (parse_advance ts) with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              (match parse_expect Tok_RPAREN ts' with
               | ParseErr uu___1 -> ParseErr "expected ')'"
               | ParseOk ((), ts'') -> ParseOk (e, ts'')))
     | Tok_STR ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Str uu___1) (parse_advance ts)
     | Tok_LANG ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Lang uu___1) (parse_advance ts)
     | Tok_DATATYPE ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Datatype uu___1)
           (parse_advance ts)
     | Tok_IRI_KW ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_IRI_fn uu___1)
           (parse_advance ts)
     | Tok_URI ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_IRI_fn uu___1)
           (parse_advance ts)
     | Tok_ABS ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Abs uu___1) (parse_advance ts)
     | Tok_CEIL ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Ceil uu___1) (parse_advance ts)
     | Tok_FLOOR ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Floor uu___1) (parse_advance ts)
     | Tok_ROUND ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Round uu___1) (parse_advance ts)
     | Tok_STRLEN ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_StrLen uu___1)
           (parse_advance ts)
     | Tok_UCASE ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_UCase uu___1) (parse_advance ts)
     | Tok_LCASE ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_LCase uu___1) (parse_advance ts)
     | Tok_ENCODE_FOR_URI ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_EncodeForUri uu___1)
           (parse_advance ts)
     | Tok_ISIRI ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_IsIRI uu___1) (parse_advance ts)
     | Tok_ISBLANK ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_IsBlank uu___1)
           (parse_advance ts)
     | Tok_ISLITERAL ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_IsLiteral uu___1)
           (parse_advance ts)
     | Tok_ISNUMERIC ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_IsNumeric uu___1)
           (parse_advance ts)
     | Tok_MD5 ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_MD5 uu___1) (parse_advance ts)
     | Tok_SHA1 ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_SHA1 uu___1) (parse_advance ts)
     | Tok_SHA256 ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_SHA256 uu___1)
           (parse_advance ts)
     | Tok_SHA384 ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_SHA384 uu___1)
           (parse_advance ts)
     | Tok_SHA512 ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_SHA512 uu___1)
           (parse_advance ts)
     | Tok_YEAR ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Year uu___1) (parse_advance ts)
     | Tok_MONTH ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Month uu___1) (parse_advance ts)
     | Tok_DAY ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Day uu___1) (parse_advance ts)
     | Tok_HOURS ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Hours uu___1) (parse_advance ts)
     | Tok_MINUTES ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Minutes uu___1)
           (parse_advance ts)
     | Tok_SECONDS ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Seconds uu___1)
           (parse_advance ts)
     | Tok_TIMEZONE ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Timezone uu___1)
           (parse_advance ts)
     | Tok_TZ ->
         parse_b1 pm (fuel - Prims.int_one)
           (fun uu___1 -> SPARQL11_Algebra.E_Tz uu___1) (parse_advance ts)
     | Tok_LANGMATCHES ->
         parse_b2 pm (fuel - Prims.int_one)
           (fun uu___1 uu___2 -> SPARQL11_Algebra.E_SameTerm (uu___1, uu___2))
           (parse_advance ts)
     | Tok_SAMETERM ->
         parse_b2 pm (fuel - Prims.int_one)
           (fun uu___1 uu___2 -> SPARQL11_Algebra.E_SameTerm (uu___1, uu___2))
           (parse_advance ts)
     | Tok_STRSTARTS ->
         parse_b2 pm (fuel - Prims.int_one)
           (fun uu___1 uu___2 ->
              SPARQL11_Algebra.E_StrStarts (uu___1, uu___2))
           (parse_advance ts)
     | Tok_STRENDS ->
         parse_b2 pm (fuel - Prims.int_one)
           (fun uu___1 uu___2 -> SPARQL11_Algebra.E_StrEnds (uu___1, uu___2))
           (parse_advance ts)
     | Tok_CONTAINS ->
         parse_b2 pm (fuel - Prims.int_one)
           (fun uu___1 uu___2 -> SPARQL11_Algebra.E_Contains (uu___1, uu___2))
           (parse_advance ts)
     | Tok_STRBEFORE ->
         parse_b2 pm (fuel - Prims.int_one)
           (fun uu___1 uu___2 ->
              SPARQL11_Algebra.E_StrBefore (uu___1, uu___2))
           (parse_advance ts)
     | Tok_STRAFTER ->
         parse_b2 pm (fuel - Prims.int_one)
           (fun uu___1 uu___2 -> SPARQL11_Algebra.E_StrAfter (uu___1, uu___2))
           (parse_advance ts)
     | Tok_STRDT ->
         parse_b2 pm (fuel - Prims.int_one)
           (fun uu___1 uu___2 -> SPARQL11_Algebra.E_StrDt (uu___1, uu___2))
           (parse_advance ts)
     | Tok_STRLANG ->
         parse_b2 pm (fuel - Prims.int_one)
           (fun uu___1 uu___2 -> SPARQL11_Algebra.E_StrLang (uu___1, uu___2))
           (parse_advance ts)
     | Tok_BOUND -> parse_bound pm (fuel - Prims.int_one) (parse_advance ts)
     | Tok_IF -> parse_if_expr pm (fuel - Prims.int_one) (parse_advance ts)
     | Tok_COALESCE ->
         parse_coalesce pm (fuel - Prims.int_one) (parse_advance ts)
     | Tok_CONCAT ->
         parse_concat pm (fuel - Prims.int_one) (parse_advance ts)
     | Tok_NOW -> ParseOk (SPARQL11_Algebra.E_Now, (parse_advance ts))
     | Tok_RAND -> ParseErr "unsupported: RAND()"
     | Tok_UUID -> ParseErr "unsupported: UUID()"
     | Tok_STRUUID -> ParseErr "unsupported: STRUUID()"
     | Tok_BNODE_KW -> ParseErr "unsupported: BNODE()"
     | Tok_REGEX -> parse_regex pm (fuel - Prims.int_one) (parse_advance ts)
     | Tok_REPLACE ->
         parse_replace pm (fuel - Prims.int_one) (parse_advance ts)
     | Tok_SUBSTR ->
         parse_substr pm (fuel - Prims.int_one) (parse_advance ts)
     | Tok_COUNT ->
         parse_aggregate pm (fuel - Prims.int_one) SPARQL11_Algebra.Agg_Count
           (parse_advance ts)
     | Tok_SUM ->
         parse_aggregate pm (fuel - Prims.int_one) SPARQL11_Algebra.Agg_Sum
           (parse_advance ts)
     | Tok_MIN_KW ->
         parse_aggregate pm (fuel - Prims.int_one) SPARQL11_Algebra.Agg_Min
           (parse_advance ts)
     | Tok_MAX_KW ->
         parse_aggregate pm (fuel - Prims.int_one) SPARQL11_Algebra.Agg_Max
           (parse_advance ts)
     | Tok_AVG ->
         parse_aggregate pm (fuel - Prims.int_one) SPARQL11_Algebra.Agg_Avg
           (parse_advance ts)
     | Tok_SAMPLE ->
         parse_aggregate pm (fuel - Prims.int_one)
           SPARQL11_Algebra.Agg_Sample (parse_advance ts)
     | Tok_GROUP_CONCAT ->
         parse_group_concat pm (fuel - Prims.int_one) (parse_advance ts)
     | Tok_EXISTS ->
         (match parse_group_graph_pattern pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (g, ts') -> ParseOk ((SPARQL11_Algebra.E_Exists g), ts'))
     | Tok_NOT ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_EXISTS ->
              (match parse_group_graph_pattern pm (fuel - Prims.int_one)
                       (parse_advance ts')
               with
               | ParseErr m -> ParseErr m
               | ParseOk (g, ts'') ->
                   ParseOk ((SPARQL11_Algebra.E_NotExists g), ts''))
          | Tok_IN -> ParseOk ((SPARQL11_Algebra.E_BoolLit true), ts)
          | uu___1 -> ParseErr "expected EXISTS or IN after NOT")
     | uu___1 -> ParseErr "unexpected token in expression")
and parse_bound (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts') ->
         (match parse_peek ts' with
          | Tok_VAR v ->
              (match parse_expect Tok_RPAREN (parse_advance ts') with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts'') ->
                   ParseOk ((SPARQL11_Algebra.E_Bound v), ts''))
          | uu___1 -> ParseErr "BOUND expects a variable"))
and parse_if_expr (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts1) ->
         (match parse_expr pm (fuel - Prims.int_one) ts1 with
          | ParseErr m -> ParseErr m
          | ParseOk (e1, ts2) ->
              (match parse_expect Tok_COMMA ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts3) ->
                   (match parse_expr pm (fuel - Prims.int_one) ts3 with
                    | ParseErr m -> ParseErr m
                    | ParseOk (e2, ts4) ->
                        (match parse_expect Tok_COMMA ts4 with
                         | ParseErr m -> ParseErr m
                         | ParseOk ((), ts5) ->
                             (match parse_expr pm (fuel - Prims.int_one) ts5
                              with
                              | ParseErr m -> ParseErr m
                              | ParseOk (e3, ts6) ->
                                  (match parse_expect Tok_RPAREN ts6 with
                                   | ParseErr m -> ParseErr m
                                   | ParseOk ((), ts7) ->
                                       ParseOk
                                         ((SPARQL11_Algebra.E_If (e1, e2, e3)),
                                           ts7))))))))
and parse_coalesce (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts') ->
         (match parse_expr_list pm (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (es, ts'') ->
              (match parse_expect Tok_RPAREN ts'' with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts''') ->
                   ParseOk ((SPARQL11_Algebra.E_Coalesce es), ts'''))))
and parse_concat (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts') ->
         (match parse_expr_list pm (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (es, ts'') ->
              (match parse_expect Tok_RPAREN ts'' with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts''') ->
                   ParseOk ((SPARQL11_Algebra.E_Concat es), ts'''))))
and parse_regex (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts1) ->
         (match parse_expr pm (fuel - Prims.int_one) ts1 with
          | ParseErr m -> ParseErr m
          | ParseOk (e1, ts2) ->
              (match parse_expect Tok_COMMA ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts3) ->
                   (match parse_expr pm (fuel - Prims.int_one) ts3 with
                    | ParseErr m -> ParseErr m
                    | ParseOk (e2, ts4) ->
                        (match parse_peek ts4 with
                         | Tok_COMMA ->
                             (match parse_expr pm (fuel - Prims.int_one)
                                      (parse_advance ts4)
                              with
                              | ParseErr m -> ParseErr m
                              | ParseOk (e3, ts5) ->
                                  (match parse_expect Tok_RPAREN ts5 with
                                   | ParseErr m -> ParseErr m
                                   | ParseOk ((), ts6) ->
                                       ParseOk
                                         ((SPARQL11_Algebra.E_Regex
                                             (e1, e2,
                                               (FStar_Pervasives_Native.Some
                                                  e3))), ts6)))
                         | uu___1 ->
                             (match parse_expect Tok_RPAREN ts4 with
                              | ParseErr m -> ParseErr m
                              | ParseOk ((), ts5) ->
                                  ParseOk
                                    ((SPARQL11_Algebra.E_Regex
                                        (e1, e2,
                                          FStar_Pervasives_Native.None)),
                                      ts5)))))))
and parse_replace (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts1) ->
         (match parse_expr pm (fuel - Prims.int_one) ts1 with
          | ParseErr m -> ParseErr m
          | ParseOk (e1, ts2) ->
              (match parse_expect Tok_COMMA ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts3) ->
                   (match parse_expr pm (fuel - Prims.int_one) ts3 with
                    | ParseErr m -> ParseErr m
                    | ParseOk (e2, ts4) ->
                        (match parse_expect Tok_COMMA ts4 with
                         | ParseErr m -> ParseErr m
                         | ParseOk ((), ts5) ->
                             (match parse_expr pm (fuel - Prims.int_one) ts5
                              with
                              | ParseErr m -> ParseErr m
                              | ParseOk (e3, ts6) ->
                                  (match parse_peek ts6 with
                                   | Tok_COMMA ->
                                       (match parse_expr pm
                                                (fuel - Prims.int_one)
                                                (parse_advance ts6)
                                        with
                                        | ParseErr m -> ParseErr m
                                        | ParseOk (e4, ts7) ->
                                            (match parse_expect Tok_RPAREN
                                                     ts7
                                             with
                                             | ParseErr m -> ParseErr m
                                             | ParseOk ((), ts8) ->
                                                 ParseOk
                                                   ((SPARQL11_Algebra.E_Replace
                                                       (e1, e2, e3,
                                                         (FStar_Pervasives_Native.Some
                                                            e4))), ts8)))
                                   | uu___1 ->
                                       (match parse_expect Tok_RPAREN ts6
                                        with
                                        | ParseErr m -> ParseErr m
                                        | ParseOk ((), ts7) ->
                                            ParseOk
                                              ((SPARQL11_Algebra.E_Replace
                                                  (e1, e2, e3,
                                                    FStar_Pervasives_Native.None)),
                                                ts7)))))))))
and parse_substr (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts1) ->
         (match parse_expr pm (fuel - Prims.int_one) ts1 with
          | ParseErr m -> ParseErr m
          | ParseOk (e1, ts2) ->
              (match parse_expect Tok_COMMA ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts3) ->
                   (match parse_expr pm (fuel - Prims.int_one) ts3 with
                    | ParseErr m -> ParseErr m
                    | ParseOk (e2, ts4) ->
                        (match parse_peek ts4 with
                         | Tok_COMMA ->
                             (match parse_expr pm (fuel - Prims.int_one)
                                      (parse_advance ts4)
                              with
                              | ParseErr m -> ParseErr m
                              | ParseOk (e3, ts5) ->
                                  (match parse_expect Tok_RPAREN ts5 with
                                   | ParseErr m -> ParseErr m
                                   | ParseOk ((), ts6) ->
                                       ParseOk
                                         ((SPARQL11_Algebra.E_Substr
                                             (e1, e2,
                                               (FStar_Pervasives_Native.Some
                                                  e3))), ts6)))
                         | uu___1 ->
                             (match parse_expect Tok_RPAREN ts4 with
                              | ParseErr m -> ParseErr m
                              | ParseOk ((), ts5) ->
                                  ParseOk
                                    ((SPARQL11_Algebra.E_Substr
                                        (e1, e2,
                                          FStar_Pervasives_Native.None)),
                                      ts5)))))))
and parse_aggregate (pm : prefix_map) (fuel : Prims.nat)
  (agg : SPARQL11_Algebra.aggregate_fn) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts1) ->
         let uu___1 =
           match parse_peek ts1 with
           | Tok_DISTINCT -> (true, (parse_advance ts1))
           | uu___2 -> (false, ts1) in
         (match uu___1 with
          | (dist, ts2) ->
              (match parse_peek ts2 with
               | Tok_STAR ->
                   (match parse_expect Tok_RPAREN (parse_advance ts2) with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts3) ->
                        ParseOk
                          ((SPARQL11_Algebra.E_Aggregate
                              (agg, dist, (SPARQL11_Algebra.E_BoolLit true))),
                            ts3))
               | uu___2 ->
                   (match parse_expr pm (fuel - Prims.int_one) ts2 with
                    | ParseErr m -> ParseErr m
                    | ParseOk (e, ts3) ->
                        (match parse_expect Tok_RPAREN ts3 with
                         | ParseErr m -> ParseErr m
                         | ParseOk ((), ts4) ->
                             ParseOk
                               ((SPARQL11_Algebra.E_Aggregate (agg, dist, e)),
                                 ts4))))))
and parse_group_concat (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts1) ->
         let uu___1 =
           match parse_peek ts1 with
           | Tok_DISTINCT -> (true, (parse_advance ts1))
           | uu___2 -> (false, ts1) in
         (match uu___1 with
          | (dist, ts2) ->
              (match parse_expr pm (fuel - Prims.int_one) ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (e, ts3) ->
                   let uu___2 =
                     match parse_peek ts3 with
                     | Tok_SEMI ->
                         let ts3' = parse_advance ts3 in
                         (match parse_peek ts3' with
                          | Tok_SEPARATOR ->
                              let ts3'' = parse_advance ts3' in
                              (match parse_expect Tok_EQ ts3'' with
                               | ParseOk ((), ts3''') ->
                                   (match parse_peek ts3''' with
                                    | Tok_STRING s ->
                                        ((FStar_Pervasives_Native.Some s),
                                          (parse_advance ts3'''))
                                    | uu___3 ->
                                        (FStar_Pervasives_Native.None, ts3))
                               | uu___3 ->
                                   (FStar_Pervasives_Native.None, ts3))
                          | uu___3 -> (FStar_Pervasives_Native.None, ts3))
                     | uu___3 -> (FStar_Pervasives_Native.None, ts3) in
                   (match uu___2 with
                    | (sep, ts4) ->
                        (match parse_expect Tok_RPAREN ts4 with
                         | ParseErr m -> ParseErr m
                         | ParseOk ((), ts5) ->
                             ParseOk
                               ((SPARQL11_Algebra.E_Aggregate
                                   ((SPARQL11_Algebra.Agg_GroupConcat sep),
                                     dist, e)), ts5))))))
and parse_b1 (pm : prefix_map) (fuel : Prims.nat)
  (ctor : SPARQL11_Algebra.expr -> SPARQL11_Algebra.expr) (ts : token_stream)
  : SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts') ->
         (match parse_expr pm (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts'') ->
              (match parse_expect Tok_RPAREN ts'' with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts''') -> ParseOk ((ctor e), ts'''))))
and parse_b2 (pm : prefix_map) (fuel : Prims.nat)
  (ctor :
    SPARQL11_Algebra.expr -> SPARQL11_Algebra.expr -> SPARQL11_Algebra.expr)
  (ts : token_stream) : SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts1) ->
         (match parse_expr pm (fuel - Prims.int_one) ts1 with
          | ParseErr m -> ParseErr m
          | ParseOk (e1, ts2) ->
              (match parse_expect Tok_COMMA ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts3) ->
                   (match parse_expr pm (fuel - Prims.int_one) ts3 with
                    | ParseErr m -> ParseErr m
                    | ParseOk (e2, ts4) ->
                        (match parse_expect Tok_RPAREN ts4 with
                         | ParseErr m -> ParseErr m
                         | ParseOk ((), ts5) -> ParseOk ((ctor e1 e2), ts5))))))
and parse_func_call (pm : prefix_map) (fuel : Prims.nat)
  (iri : RDF_Graph_Executable.wf_iri) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expr_list pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (args, ts') ->
         (match parse_expect Tok_RPAREN ts' with
          | ParseErr m -> ParseErr m
          | ParseOk ((), ts'') ->
              ParseOk ((SPARQL11_Algebra.E_FunctionCall (iri, args)), ts'')))
and parse_pname_expr (pm : prefix_map) (fuel : Prims.nat) (pn : Prims.string)
  (ts : token_stream) : SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match resolve_pname pn pm with
     | FStar_Pervasives_Native.Some iri ->
         if RDF_Graph_Executable.is_iri iri
         then
           (match parse_peek ts with
            | Tok_LPAREN ->
                parse_func_call pm (fuel - Prims.int_one) iri
                  (parse_advance ts)
            | uu___1 -> ParseOk ((SPARQL11_Algebra.E_IRI iri), ts))
         else ParseErr (Prims.strcat "resolved IRI invalid: " iri)
     | FStar_Pervasives_Native.None ->
         ParseErr (Prims.strcat "unresolved prefix: " pn))
and parse_rdf_literal_expr (pm : prefix_map) (fuel : Prims.nat)
  (s : Prims.string) (ts : token_stream) :
  SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_HATHAT ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_IRI dt ->
              if RDF_Graph_Executable.is_iri dt
              then
                (match make_typed_literal s dt with
                 | FStar_Pervasives_Native.Some lit ->
                     ParseOk
                       ((SPARQL11_Algebra.E_Literal lit),
                         (parse_advance ts'))
                 | FStar_Pervasives_Native.None ->
                     ParseErr "invalid typed literal")
              else ParseErr "invalid datatype IRI"
          | Tok_PNAME pn ->
              (match resolve_pname pn pm with
               | FStar_Pervasives_Native.Some dt ->
                   if RDF_Graph_Executable.is_iri dt
                   then
                     (match make_typed_literal s dt with
                      | FStar_Pervasives_Native.Some lit ->
                          ParseOk
                            ((SPARQL11_Algebra.E_Literal lit),
                              (parse_advance ts'))
                      | FStar_Pervasives_Native.None ->
                          ParseErr "invalid typed literal")
                   else ParseErr "invalid datatype IRI"
               | FStar_Pervasives_Native.None ->
                   ParseErr (Prims.strcat "unresolved datatype prefix: " pn))
          | uu___1 -> ParseErr "expected IRI after ^^")
     | Tok_LANGTAG lang ->
         ParseOk
           ((SPARQL11_Algebra.E_Literal (make_lang_literal s lang)),
             (parse_advance ts))
     | uu___1 ->
         ParseOk ((SPARQL11_Algebra.E_Literal (make_plain_literal s)), ts))
and parse_group_graph_pattern (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.group_graph_pattern parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LBRACE ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts') ->
         (match parse_peek ts' with
          | Tok_SELECT ->
              (match parse_select_query pm (fuel - Prims.int_one) ts' with
               | ParseErr m -> ParseErr m
               | ParseOk (q, ts'') ->
                   (match parse_expect Tok_RBRACE ts'' with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts''') ->
                        ParseOk ((SPARQL11_Algebra.GP_SubSelect q), ts''')))
          | Tok_RBRACE ->
              ParseOk (SPARQL11_Algebra.GP_Empty, (parse_advance ts'))
          | uu___1 ->
              (match parse_ggp_body pm (fuel - Prims.int_one)
                       SPARQL11_Algebra.GP_Empty ts'
               with
               | ParseErr m -> ParseErr m
               | ParseOk (g, ts'') ->
                   (match parse_expect Tok_RBRACE ts'' with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts''') -> ParseOk (g, ts''')))))
and parse_ggp_body (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.group_graph_pattern) (ts : token_stream) :
  SPARQL11_Algebra.group_graph_pattern parse_result=
  if fuel = Prims.int_zero
  then ParseOk (acc, ts)
  else
    (match parse_peek ts with
     | Tok_VAR uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___3 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___2 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_IRI uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___3 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___2 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_PNAME uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___3 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___2 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_BNODE uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___3 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___2 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_LBRACKET ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___2 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___1 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_LPAREN ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___2 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___1 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_A ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___2 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___1 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_INTEGER uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___3 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___2 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_DECIMAL uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___3 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___2 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_DOUBLE uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___3 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___2 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_STRING uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___3 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___2 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_TRUE ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___2 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___1 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_FALSE ->
         (match parse_triples_block pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts') ->
              let acc' =
                if (FStar_List_Tot_Base.length triples) = Prims.int_zero
                then acc
                else
                  (match acc with
                   | SPARQL11_Algebra.GP_Empty ->
                       SPARQL11_Algebra.GP_BGP triples
                   | uu___2 ->
                       SPARQL11_Algebra.GP_Join
                         (acc, (SPARQL11_Algebra.GP_BGP triples))) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___1 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_OPTIONAL ->
         (match parse_group_graph_pattern pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (g, ts') ->
              let acc' =
                match acc with
                | SPARQL11_Algebra.GP_Empty ->
                    SPARQL11_Algebra.GP_LeftJoin
                      (SPARQL11_Algebra.GP_Empty, g,
                        (SPARQL11_Algebra.E_BoolLit true))
                | uu___1 ->
                    SPARQL11_Algebra.GP_LeftJoin
                      (acc, g, (SPARQL11_Algebra.E_BoolLit true)) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___1 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_MINUS_KW ->
         (match parse_group_graph_pattern pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (g, ts') ->
              let acc' = SPARQL11_Algebra.GP_Minus (acc, g) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___1 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | Tok_GRAPH ->
         let ts' = parse_advance ts in
         (match parse_graph_name pm (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (gn, ts'') ->
              (match parse_group_graph_pattern pm (fuel - Prims.int_one) ts''
               with
               | ParseErr m -> ParseErr m
               | ParseOk (g, ts''') ->
                   let acc' =
                     match acc with
                     | SPARQL11_Algebra.GP_Empty ->
                         SPARQL11_Algebra.GP_Graph (gn, g)
                     | uu___1 ->
                         SPARQL11_Algebra.GP_Join
                           (acc, (SPARQL11_Algebra.GP_Graph (gn, g))) in
                   let ts'''1 =
                     match parse_peek ts''' with
                     | Tok_DOT -> parse_advance ts'''
                     | uu___1 -> ts''' in
                   parse_ggp_body pm (fuel - Prims.int_one) acc' ts'''1))
     | Tok_SERVICE ->
         let ts' = parse_advance ts in
         let uu___1 =
           match parse_peek ts' with
           | Tok_SILENT -> (true, (parse_advance ts'))
           | uu___2 -> (false, ts') in
         (match uu___1 with
          | (silent, ts'1) ->
              (match parse_service_iri pm (fuel - Prims.int_one) ts'1 with
               | ParseErr m -> ParseErr m
               | ParseOk (siri, ts'') ->
                   (match parse_group_graph_pattern pm (fuel - Prims.int_one)
                            ts''
                    with
                    | ParseErr m -> ParseErr m
                    | ParseOk (g, ts''') ->
                        let acc' =
                          match acc with
                          | SPARQL11_Algebra.GP_Empty ->
                              SPARQL11_Algebra.GP_Service (siri, g, silent)
                          | uu___2 ->
                              SPARQL11_Algebra.GP_Join
                                (acc,
                                  (SPARQL11_Algebra.GP_Service
                                     (siri, g, silent))) in
                        let ts'''1 =
                          match parse_peek ts''' with
                          | Tok_DOT -> parse_advance ts'''
                          | uu___2 -> ts''' in
                        parse_ggp_body pm (fuel - Prims.int_one) acc' ts'''1)))
     | Tok_FILTER ->
         let ts' = parse_advance ts in
         (match parse_filter_expr pm (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts'') ->
              let acc' = SPARQL11_Algebra.GP_Filter (e, acc) in
              let ts''1 =
                match parse_peek ts'' with
                | Tok_DOT -> parse_advance ts''
                | uu___1 -> ts'' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts''1)
     | Tok_BIND ->
         let ts' = parse_advance ts in
         (match parse_expect Tok_LPAREN ts' with
          | ParseErr m -> ParseErr m
          | ParseOk ((), ts'') ->
              (match parse_expr pm (fuel - Prims.int_one) ts'' with
               | ParseErr m -> ParseErr m
               | ParseOk (e, ts''') ->
                   (match parse_expect Tok_AS ts''' with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts4) ->
                        (match parse_peek ts4 with
                         | Tok_VAR v ->
                             (match parse_expect Tok_RPAREN
                                      (parse_advance ts4)
                              with
                              | ParseErr m -> ParseErr m
                              | ParseOk ((), ts5) ->
                                  let acc' =
                                    SPARQL11_Algebra.GP_Bind (e, v, acc) in
                                  let ts51 =
                                    match parse_peek ts5 with
                                    | Tok_DOT -> parse_advance ts5
                                    | uu___1 -> ts5 in
                                  parse_ggp_body pm (fuel - Prims.int_one)
                                    acc' ts51)
                         | uu___1 -> ParseErr "expected variable after AS"))))
     | Tok_VALUES -> ParseErr "unsupported: inline VALUES"
     | Tok_LBRACE ->
         (match parse_group_or_union pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (g, ts') ->
              let acc' =
                match acc with
                | SPARQL11_Algebra.GP_Empty -> g
                | uu___1 -> SPARQL11_Algebra.GP_Join (acc, g) in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___1 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' ts'1)
     | uu___1 -> ParseOk (acc, ts))
and parse_group_or_union (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.group_graph_pattern parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_group_graph_pattern pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (g1, ts') ->
         (match parse_peek ts' with
          | Tok_UNION ->
              (match parse_group_or_union pm (fuel - Prims.int_one)
                       (parse_advance ts')
               with
               | ParseErr m -> ParseErr m
               | ParseOk (g2, ts'') ->
                   ParseOk ((SPARQL11_Algebra.GP_Union (g1, g2)), ts''))
          | uu___1 -> ParseOk (g1, ts')))
and parse_filter_expr (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.expr parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_LPAREN ->
         (match parse_expr pm (fuel - Prims.int_one) (parse_advance ts) with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              (match parse_expect Tok_RPAREN ts' with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts'') -> ParseOk (e, ts'')))
     | Tok_EXISTS -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_NOT -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_STR -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_LANG -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_LANGMATCHES -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_DATATYPE -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_BOUND -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_SAMETERM -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_ISIRI -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_ISBLANK -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_ISLITERAL -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_ISNUMERIC -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_REGEX -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_IF -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | uu___1 -> parse_expr pm (fuel - Prims.int_one) ts)
and parse_graph_name (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream)
  : SPARQL11_Algebra.pattern_term parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v -> ParseOk ((SPARQL11_Algebra.PT_Var v), (parse_advance ts))
     | Tok_IRI i ->
         if RDF_Graph_Executable.is_iri i
         then ParseOk ((SPARQL11_Algebra.PT_IRI i), (parse_advance ts))
         else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
         (match resolve_pname pn pm with
          | FStar_Pervasives_Native.Some iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                ParseOk ((SPARQL11_Algebra.PT_IRI iri), (parse_advance ts))
              else ParseErr "invalid IRI"
          | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
     | uu___1 -> ParseErr "expected IRI or variable for GRAPH")
and parse_service_iri (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : RDF_Graph_Executable.wf_iri parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_IRI i ->
         if RDF_Graph_Executable.is_iri i
         then ParseOk (i, (parse_advance ts))
         else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
         (match resolve_pname pn pm with
          | FStar_Pervasives_Native.Some iri ->
              if RDF_Graph_Executable.is_iri iri
              then ParseOk (iri, (parse_advance ts))
              else ParseErr "invalid IRI"
          | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
     | Tok_VAR uu___1 -> ParseErr "unsupported: variable SERVICE endpoint"
     | uu___1 -> ParseErr "expected IRI for SERVICE")
and parse_subject (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.pattern_subject parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v -> ParseOk ((SPARQL11_Algebra.PS_Var v), (parse_advance ts))
     | Tok_IRI i ->
         if RDF_Graph_Executable.is_iri i
         then ParseOk ((SPARQL11_Algebra.PS_IRI i), (parse_advance ts))
         else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
         (match resolve_pname pn pm with
          | FStar_Pervasives_Native.Some iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                ParseOk ((SPARQL11_Algebra.PS_IRI iri), (parse_advance ts))
              else ParseErr "invalid IRI"
          | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
     | Tok_BNODE b ->
         ParseOk ((SPARQL11_Algebra.PS_BNode b), (parse_advance ts))
     | uu___1 -> ParseErr "expected subject")
and parse_predicate (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream)
  : SPARQL11_Algebra.pattern_term parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v -> ParseOk ((SPARQL11_Algebra.PT_Var v), (parse_advance ts))
     | Tok_A ->
         ParseOk
           ((SPARQL11_Algebra.PT_IRI rdf_type_iri_str), (parse_advance ts))
     | Tok_IRI i ->
         if RDF_Graph_Executable.is_iri i
         then ParseOk ((SPARQL11_Algebra.PT_IRI i), (parse_advance ts))
         else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
         (match resolve_pname pn pm with
          | FStar_Pervasives_Native.Some iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                ParseOk ((SPARQL11_Algebra.PT_IRI iri), (parse_advance ts))
              else ParseErr "invalid IRI"
          | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
     | uu___1 -> ParseErr "expected predicate")
and parse_object (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.pattern_term parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v -> ParseOk ((SPARQL11_Algebra.PT_Var v), (parse_advance ts))
     | Tok_IRI i ->
         if RDF_Graph_Executable.is_iri i
         then ParseOk ((SPARQL11_Algebra.PT_IRI i), (parse_advance ts))
         else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
         (match resolve_pname pn pm with
          | FStar_Pervasives_Native.Some iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                ParseOk ((SPARQL11_Algebra.PT_IRI iri), (parse_advance ts))
              else ParseErr "invalid IRI"
          | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
     | Tok_BNODE b ->
         ParseOk ((SPARQL11_Algebra.PT_BNode b), (parse_advance ts))
     | Tok_STRING s ->
         parse_rdf_literal_pt pm (fuel - Prims.int_one) s (parse_advance ts)
     | Tok_INTEGER n ->
         (match make_typed_literal n
                  "http://www.w3.org/2001/XMLSchema#integer"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk ((SPARQL11_Algebra.PT_Literal lit), (parse_advance ts))
          | FStar_Pervasives_Native.None ->
              ParseErr "invalid integer literal")
     | Tok_DECIMAL d ->
         (match make_typed_literal d
                  "http://www.w3.org/2001/XMLSchema#decimal"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk ((SPARQL11_Algebra.PT_Literal lit), (parse_advance ts))
          | FStar_Pervasives_Native.None ->
              ParseErr "invalid decimal literal")
     | Tok_DOUBLE d ->
         (match make_typed_literal d
                  "http://www.w3.org/2001/XMLSchema#double"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk ((SPARQL11_Algebra.PT_Literal lit), (parse_advance ts))
          | FStar_Pervasives_Native.None -> ParseErr "invalid double literal")
     | Tok_TRUE ->
         (match make_typed_literal "true"
                  "http://www.w3.org/2001/XMLSchema#boolean"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk ((SPARQL11_Algebra.PT_Literal lit), (parse_advance ts))
          | FStar_Pervasives_Native.None ->
              ParseErr "invalid boolean literal")
     | Tok_FALSE ->
         (match make_typed_literal "false"
                  "http://www.w3.org/2001/XMLSchema#boolean"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk ((SPARQL11_Algebra.PT_Literal lit), (parse_advance ts))
          | FStar_Pervasives_Native.None ->
              ParseErr "invalid boolean literal")
     | Tok_A ->
         ParseOk
           ((SPARQL11_Algebra.PT_IRI rdf_type_iri_str), (parse_advance ts))
     | uu___1 -> ParseErr "expected object")
and parse_rdf_literal_pt (pm : prefix_map) (fuel : Prims.nat)
  (s : Prims.string) (ts : token_stream) :
  SPARQL11_Algebra.pattern_term parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_HATHAT ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_IRI dt ->
              if RDF_Graph_Executable.is_iri dt
              then
                (match make_typed_literal s dt with
                 | FStar_Pervasives_Native.Some lit ->
                     ParseOk
                       ((SPARQL11_Algebra.PT_Literal lit),
                         (parse_advance ts'))
                 | FStar_Pervasives_Native.None ->
                     ParseErr "invalid typed literal")
              else ParseErr "invalid datatype IRI"
          | Tok_PNAME pn ->
              (match resolve_pname pn pm with
               | FStar_Pervasives_Native.Some dt ->
                   if RDF_Graph_Executable.is_iri dt
                   then
                     (match make_typed_literal s dt with
                      | FStar_Pervasives_Native.Some lit ->
                          ParseOk
                            ((SPARQL11_Algebra.PT_Literal lit),
                              (parse_advance ts'))
                      | FStar_Pervasives_Native.None ->
                          ParseErr "invalid typed literal")
                   else ParseErr "invalid datatype IRI"
               | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
          | uu___1 -> ParseErr "expected IRI after ^^")
     | Tok_LANGTAG lang ->
         ParseOk
           ((SPARQL11_Algebra.PT_Literal (make_lang_literal s lang)),
             (parse_advance ts))
     | uu___1 ->
         ParseOk ((SPARQL11_Algebra.PT_Literal (make_plain_literal s)), ts))
and parse_object_list (pm : prefix_map) (fuel : Prims.nat)
  (subj : SPARQL11_Algebra.pattern_subject)
  (pred : SPARQL11_Algebra.pattern_term)
  (acc : SPARQL11_Algebra.triple_pattern Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.triple_pattern Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_object pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (obj, ts') ->
         let tp =
           {
             SPARQL11_Algebra.tp_s = subj;
             SPARQL11_Algebra.tp_p = pred;
             SPARQL11_Algebra.tp_o = obj
           } in
         (match parse_peek ts' with
          | Tok_COMMA ->
              parse_object_list pm (fuel - Prims.int_one) subj pred (tp ::
                acc) (parse_advance ts')
          | uu___1 -> ParseOk ((FStar_List_Tot_Base.rev (tp :: acc)), ts')))
and parse_pred_obj_list (pm : prefix_map) (fuel : Prims.nat)
  (subj : SPARQL11_Algebra.pattern_subject)
  (acc : SPARQL11_Algebra.triple_pattern Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.triple_pattern Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_predicate pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (pred, ts') ->
         (match parse_object_list pm (fuel - Prims.int_one) subj pred acc ts'
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts'') ->
              (match parse_peek ts'' with
               | Tok_SEMI ->
                   let ts''' = parse_advance ts'' in
                   (match parse_peek ts''' with
                    | Tok_DOT -> ParseOk (triples, ts''')
                    | Tok_RBRACE -> ParseOk (triples, ts''')
                    | Tok_OPTIONAL -> ParseOk (triples, ts''')
                    | Tok_MINUS_KW -> ParseOk (triples, ts''')
                    | Tok_FILTER -> ParseOk (triples, ts''')
                    | Tok_BIND -> ParseOk (triples, ts''')
                    | Tok_GRAPH -> ParseOk (triples, ts''')
                    | Tok_SERVICE -> ParseOk (triples, ts''')
                    | Tok_VALUES -> ParseOk (triples, ts''')
                    | Tok_UNION -> ParseOk (triples, ts''')
                    | Tok_LBRACE -> ParseOk (triples, ts''')
                    | Tok_RBRACKET -> ParseOk (triples, ts''')
                    | Tok_EOF -> ParseOk (triples, ts''')
                    | uu___1 ->
                        parse_pred_obj_list pm (fuel - Prims.int_one) subj
                          triples ts''')
               | uu___1 -> ParseOk (triples, ts''))))
and parse_triples_block (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.triple_pattern Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.triple_pattern Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk (acc, ts)
  else
    (match parse_subject pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseOk (acc, ts)
     | ParseOk (subj, ts') ->
         (match parse_pred_obj_list pm (fuel - Prims.int_one) subj acc ts'
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples, ts'') ->
              (match parse_peek ts'' with
               | Tok_DOT ->
                   let ts''' = parse_advance ts'' in
                   (match parse_peek ts''' with
                    | Tok_VAR uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_IRI uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_PNAME uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_BNODE uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_LBRACKET ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_LPAREN ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_A ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_INTEGER uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_DECIMAL uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_DOUBLE uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_STRING uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_TRUE ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | Tok_FALSE ->
                        parse_triples_block pm (fuel - Prims.int_one) triples
                          ts'''
                    | uu___1 -> ParseOk (triples, ts'''))
               | uu___1 -> ParseOk (triples, ts''))))
and parse_select_query (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.query parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (let r = parse_prologue pm (fuel - Prims.int_one) ts in
     match r with
     | ParseErr m -> ParseErr m
     | ParseOk ((pm', base), ts') ->
         (match parse_peek ts' with
          | Tok_SELECT ->
              parse_select_body pm' (fuel - Prims.int_one) base ts'
          | Tok_ASK -> parse_ask_body pm' (fuel - Prims.int_one) base ts'
          | Tok_CONSTRUCT -> ParseErr "unsupported: CONSTRUCT queries"
          | Tok_DESCRIBE -> ParseErr "unsupported: DESCRIBE queries"
          | uu___1 -> ParseErr "expected SELECT, ASK, CONSTRUCT, or DESCRIBE"))
and parse_prologue (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  (prefix_map * RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
    parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((pm, FStar_Pervasives_Native.None), ts)
  else
    (match parse_peek ts with
     | Tok_PREFIX ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_PNAME pn ->
              let uu___1 = split_pname pn in
              (match uu___1 with
               | (prefix, uu___2) ->
                   let ts'' = parse_advance ts' in
                   (match parse_peek ts'' with
                    | Tok_IRI iri ->
                        if RDF_Graph_Executable.is_iri iri
                        then
                          parse_prologue ((prefix, iri) :: pm)
                            (fuel - Prims.int_one) (parse_advance ts'')
                        else ParseErr "invalid prefix IRI"
                    | uu___3 -> ParseErr "expected IRI after PREFIX name"))
          | uu___1 -> ParseErr "expected prefix name after PREFIX")
     | Tok_BASE ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_IRI iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                parse_prologue pm (fuel - Prims.int_one) (parse_advance ts')
              else ParseErr "invalid BASE IRI"
          | uu___1 -> ParseErr "expected IRI after BASE")
     | uu___1 -> ParseOk ((pm, FStar_Pervasives_Native.None), ts))
and parse_select_body (pm : prefix_map) (fuel : Prims.nat)
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (ts : token_stream) : SPARQL11_Algebra.query parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (let ts' = parse_advance ts in
     let uu___1 =
       match parse_peek ts' with
       | Tok_DISTINCT -> (true, false, (parse_advance ts'))
       | Tok_REDUCED -> (false, true, (parse_advance ts'))
       | uu___2 -> (false, false, ts') in
     match uu___1 with
     | (dist, red, ts'') ->
         (match parse_select_vars pm (fuel - Prims.int_one) ts'' with
          | ParseErr m -> ParseErr m
          | ParseOk (sel, ts3) ->
              (match parse_skip_from (fuel - Prims.int_one) ts3 with
               | ParseErr m -> ParseErr m
               | ParseOk (ds, ts4) ->
                   let ts41 =
                     match parse_peek ts4 with
                     | Tok_WHERE -> parse_advance ts4
                     | uu___2 -> ts4 in
                   (match parse_group_graph_pattern pm (fuel - Prims.int_one)
                            ts41
                    with
                    | ParseErr m -> ParseErr m
                    | ParseOk (pattern, ts5) ->
                        (match parse_solution_modifier pm
                                 (fuel - Prims.int_one) ts5
                         with
                         | ParseErr m -> ParseErr m
                         | ParseOk (modifier, ts6) ->
                             ParseOk
                               ({
                                  SPARQL11_Algebra.q_base = base;
                                  SPARQL11_Algebra.q_prefixes = pm;
                                  SPARQL11_Algebra.q_form =
                                    (SPARQL11_Algebra.QF_Select sel);
                                  SPARQL11_Algebra.q_dataset = ds;
                                  SPARQL11_Algebra.q_pattern = pattern;
                                  SPARQL11_Algebra.q_group_by =
                                    FStar_Pervasives_Native.None;
                                  SPARQL11_Algebra.q_having =
                                    FStar_Pervasives_Native.None;
                                  SPARQL11_Algebra.q_modifier =
                                    {
                                      SPARQL11_Algebra.sm_order_by =
                                        (modifier.SPARQL11_Algebra.sm_order_by);
                                      SPARQL11_Algebra.sm_distinct = dist;
                                      SPARQL11_Algebra.sm_reduced = red;
                                      SPARQL11_Algebra.sm_offset =
                                        (modifier.SPARQL11_Algebra.sm_offset);
                                      SPARQL11_Algebra.sm_limit =
                                        (modifier.SPARQL11_Algebra.sm_limit)
                                    };
                                  SPARQL11_Algebra.q_values =
                                    FStar_Pervasives_Native.None
                                }, ts6))))))
and parse_ask_body (pm : prefix_map) (fuel : Prims.nat)
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (ts : token_stream) : SPARQL11_Algebra.query parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (let ts' = parse_advance ts in
     match parse_skip_from (fuel - Prims.int_one) ts' with
     | ParseErr m -> ParseErr m
     | ParseOk (ds, ts'') ->
         let ts''1 =
           match parse_peek ts'' with
           | Tok_WHERE -> parse_advance ts''
           | uu___1 -> ts'' in
         (match parse_group_graph_pattern pm (fuel - Prims.int_one) ts''1
          with
          | ParseErr m -> ParseErr m
          | ParseOk (pattern, ts3) ->
              ParseOk
                ({
                   SPARQL11_Algebra.q_base = base;
                   SPARQL11_Algebra.q_prefixes = pm;
                   SPARQL11_Algebra.q_form = SPARQL11_Algebra.QF_Ask;
                   SPARQL11_Algebra.q_dataset = ds;
                   SPARQL11_Algebra.q_pattern = pattern;
                   SPARQL11_Algebra.q_group_by = FStar_Pervasives_Native.None;
                   SPARQL11_Algebra.q_having = FStar_Pervasives_Native.None;
                   SPARQL11_Algebra.q_modifier = default_modifier;
                   SPARQL11_Algebra.q_values = FStar_Pervasives_Native.None
                 }, ts3)))
and parse_select_vars (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.select_clause parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_STAR -> ParseOk (SPARQL11_Algebra.Select_All, (parse_advance ts))
     | uu___1 ->
         (match parse_select_items pm (fuel - Prims.int_one) [] ts with
          | ParseErr m -> ParseErr m
          | ParseOk (items, ts') ->
              if (FStar_List_Tot_Base.length items) = Prims.int_zero
              then ParseErr "expected select variables"
              else ParseOk ((SPARQL11_Algebra.Select_Vars items), ts')))
and parse_select_items (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.select_item Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.select_item Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_VAR v ->
         parse_select_items pm (fuel - Prims.int_one)
           ((SPARQL11_Algebra.SI_Var v) :: acc) (parse_advance ts)
     | Tok_LPAREN ->
         (match parse_expr pm (fuel - Prims.int_one) (parse_advance ts) with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              (match parse_expect Tok_AS ts' with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts'') ->
                   (match parse_peek ts'' with
                    | Tok_VAR v ->
                        (match parse_expect Tok_RPAREN (parse_advance ts'')
                         with
                         | ParseErr m -> ParseErr m
                         | ParseOk ((), ts''') ->
                             parse_select_items pm (fuel - Prims.int_one)
                               ((SPARQL11_Algebra.SI_Expr (e, v)) :: acc)
                               ts''')
                    | uu___1 -> ParseErr "expected variable after AS")))
     | uu___1 -> ParseOk ((FStar_List_Tot_Base.rev acc), ts))
and parse_skip_from (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.dataset_clause Prims.list parse_result=
  if fuel = Prims.int_zero then ParseOk ([], ts) else ParseOk ([], ts)
and skip_group_by_exprs (fuel : Prims.nat) (ts : token_stream) :
  token_stream=
  if fuel = Prims.int_zero
  then ts
  else
    (match parse_peek ts with
     | Tok_VAR uu___1 ->
         skip_group_by_exprs (fuel - Prims.int_one) (parse_advance ts)
     | Tok_LPAREN ->
         skip_group_by_exprs (fuel - Prims.int_one) (parse_advance ts)
     | uu___1 -> ts)
and skip_order_by_exprs (fuel : Prims.nat) (ts : token_stream) :
  token_stream=
  if fuel = Prims.int_zero
  then ts
  else
    (match parse_peek ts with
     | Tok_ASC ->
         skip_order_by_exprs (fuel - Prims.int_one) (parse_advance ts)
     | Tok_DESC ->
         skip_order_by_exprs (fuel - Prims.int_one) (parse_advance ts)
     | Tok_VAR uu___1 ->
         skip_order_by_exprs (fuel - Prims.int_one) (parse_advance ts)
     | Tok_LPAREN ->
         skip_order_by_exprs (fuel - Prims.int_one) (parse_advance ts)
     | uu___1 -> ts)
and skip_having_exprs (fuel : Prims.nat) (ts : token_stream) : token_stream=
  if fuel = Prims.int_zero
  then ts
  else
    (match parse_peek ts with
     | Tok_LPAREN ->
         skip_having_exprs (fuel - Prims.int_one) (parse_advance ts)
     | uu___1 -> ts)
and parse_solution_modifier (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.solution_modifier parse_result=
  if fuel = Prims.int_zero
  then ParseOk (default_modifier, ts)
  else
    (let ts1 =
       match parse_peek ts with
       | Tok_GROUP ->
           let ts' = parse_advance ts in
           (match parse_peek ts' with
            | Tok_BY ->
                skip_group_by_exprs (fuel - Prims.int_one)
                  (parse_advance ts')
            | uu___1 -> ts)
       | uu___1 -> ts in
     let ts2 =
       match parse_peek ts1 with
       | Tok_HAVING ->
           skip_having_exprs (fuel - Prims.int_one) (parse_advance ts1)
       | uu___1 -> ts1 in
     let ts3 =
       match parse_peek ts2 with
       | Tok_ORDER ->
           let ts' = parse_advance ts2 in
           (match parse_peek ts' with
            | Tok_BY ->
                skip_order_by_exprs (fuel - Prims.int_one)
                  (parse_advance ts')
            | uu___1 -> ts2)
       | uu___1 -> ts2 in
     let uu___1 =
       match parse_peek ts3 with
       | Tok_LIMIT ->
           let ts' = parse_advance ts3 in
           (match parse_peek ts' with
            | Tok_INTEGER n ->
                (match parse_int_str n with
                 | FStar_Pervasives_Native.Some i ->
                     ((FStar_Pervasives_Native.Some i), (parse_advance ts'))
                 | FStar_Pervasives_Native.None ->
                     (FStar_Pervasives_Native.None, ts'))
            | uu___2 -> (FStar_Pervasives_Native.None, ts'))
       | uu___2 -> (FStar_Pervasives_Native.None, ts3) in
     match uu___1 with
     | (limit, ts4) ->
         let uu___2 =
           match parse_peek ts4 with
           | Tok_OFFSET ->
               let ts' = parse_advance ts4 in
               (match parse_peek ts' with
                | Tok_INTEGER n ->
                    (match parse_int_str n with
                     | FStar_Pervasives_Native.Some i ->
                         ((FStar_Pervasives_Native.Some i),
                           (parse_advance ts'))
                     | FStar_Pervasives_Native.None ->
                         (FStar_Pervasives_Native.None, ts'))
                | uu___3 -> (FStar_Pervasives_Native.None, ts'))
           | uu___3 -> (FStar_Pervasives_Native.None, ts4) in
         (match uu___2 with
          | (offset, ts5) ->
              ParseOk
                ({
                   SPARQL11_Algebra.sm_order_by =
                     FStar_Pervasives_Native.None;
                   SPARQL11_Algebra.sm_distinct = false;
                   SPARQL11_Algebra.sm_reduced = false;
                   SPARQL11_Algebra.sm_offset = offset;
                   SPARQL11_Algebra.sm_limit = limit
                 }, ts5)))
let parse_sparql (input : Prims.string) :
  SPARQL11_Algebra.query parse_result=
  let tokens = tokenize input in
  parse_select_query [] (Prims.of_int (10000)) tokens
let sse_wrap (tag : Prims.string) (body : Prims.string) : Prims.string=
  Prims.strcat "("
    (Prims.strcat tag (Prims.strcat " " (Prims.strcat body ")")))
let sse_pattern_term (pt : SPARQL11_Algebra.pattern_term) : Prims.string=
  match pt with
  | SPARQL11_Algebra.PT_Var v -> Prims.strcat "?" v
  | SPARQL11_Algebra.PT_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | SPARQL11_Algebra.PT_BNode b -> Prims.strcat "_:" b
  | SPARQL11_Algebra.PT_Literal l ->
      Prims.strcat "\""
        (Prims.strcat l.RDF_Graph_Executable.lexical_form "\"")
let sse_pattern_subject (ps : SPARQL11_Algebra.pattern_subject) :
  Prims.string=
  match ps with
  | SPARQL11_Algebra.PS_Var v -> Prims.strcat "?" v
  | SPARQL11_Algebra.PS_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | SPARQL11_Algebra.PS_BNode b -> Prims.strcat "_:" b
let sse_triple (tp : SPARQL11_Algebra.triple_pattern) : Prims.string=
  sse_wrap "triple"
    (Prims.strcat (sse_pattern_subject tp.SPARQL11_Algebra.tp_s)
       (Prims.strcat " "
          (Prims.strcat (sse_pattern_term tp.SPARQL11_Algebra.tp_p)
             (Prims.strcat " " (sse_pattern_term tp.SPARQL11_Algebra.tp_o)))))
let sse_bgp (patterns : SPARQL11_Algebra.bgp) : Prims.string=
  let triples = FStar_List_Tot_Base.map sse_triple patterns in
  sse_wrap "bgp" (FStar_String.concat "\n    " triples)
let sse_comp_op (op : SPARQL11_Algebra.comp_op) : Prims.string=
  match op with
  | SPARQL11_Algebra.CmpEq -> "="
  | SPARQL11_Algebra.CmpNe -> "!="
  | SPARQL11_Algebra.CmpLt -> "<"
  | SPARQL11_Algebra.CmpGt -> ">"
  | SPARQL11_Algebra.CmpLe -> "<="
  | SPARQL11_Algebra.CmpGe -> ">="
let sse_arith_op (op : SPARQL11_Algebra.arith_op) : Prims.string=
  match op with
  | SPARQL11_Algebra.Add -> "+"
  | SPARQL11_Algebra.Sub -> "-"
  | SPARQL11_Algebra.Mul -> "*"
  | SPARQL11_Algebra.Div -> "/"
let rec sse_expr (e : SPARQL11_Algebra.expr) : Prims.string=
  match e with
  | SPARQL11_Algebra.E_Var v -> Prims.strcat "?" v
  | SPARQL11_Algebra.E_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | SPARQL11_Algebra.E_Literal l ->
      Prims.strcat "\""
        (Prims.strcat l.RDF_Graph_Executable.lexical_form "\"")
  | SPARQL11_Algebra.E_BoolLit b -> if b then "true" else "false"
  | SPARQL11_Algebra.E_NumericLit n -> Prims.string_of_int n
  | SPARQL11_Algebra.E_DecimalLit s -> s
  | SPARQL11_Algebra.E_DoubleLit s -> s
  | SPARQL11_Algebra.E_Arith (op, e1, e2) ->
      sse_wrap (sse_arith_op op)
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_UnaryMinus e1 -> sse_wrap "-" (sse_expr e1)
  | SPARQL11_Algebra.E_UnaryPlus e1 -> sse_wrap "+" (sse_expr e1)
  | SPARQL11_Algebra.E_Compare (op, e1, e2) ->
      sse_wrap (sse_comp_op op)
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_And (e1, e2) ->
      sse_wrap "&&"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_Or (e1, e2) ->
      sse_wrap "||"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_Not e1 -> sse_wrap "!" (sse_expr e1)
  | SPARQL11_Algebra.E_IsIRI e1 -> sse_wrap "isIRI" (sse_expr e1)
  | SPARQL11_Algebra.E_IsBlank e1 -> sse_wrap "isBlank" (sse_expr e1)
  | SPARQL11_Algebra.E_IsLiteral e1 -> sse_wrap "isLiteral" (sse_expr e1)
  | SPARQL11_Algebra.E_IsNumeric e1 -> sse_wrap "isNumeric" (sse_expr e1)
  | SPARQL11_Algebra.E_Str e1 -> sse_wrap "str" (sse_expr e1)
  | SPARQL11_Algebra.E_Lang e1 -> sse_wrap "lang" (sse_expr e1)
  | SPARQL11_Algebra.E_Datatype e1 -> sse_wrap "datatype" (sse_expr e1)
  | SPARQL11_Algebra.E_IRI_fn e1 -> sse_wrap "iri" (sse_expr e1)
  | SPARQL11_Algebra.E_Bound v -> sse_wrap "bound" (Prims.strcat "?" v)
  | SPARQL11_Algebra.E_If (c, t, f) ->
      sse_wrap "if"
        (Prims.strcat (sse_expr c)
           (Prims.strcat " "
              (Prims.strcat (sse_expr t) (Prims.strcat " " (sse_expr f)))))
  | SPARQL11_Algebra.E_Coalesce args ->
      sse_wrap "coalesce" (sse_expr_list args)
  | SPARQL11_Algebra.E_Concat args -> sse_wrap "concat" (sse_expr_list args)
  | SPARQL11_Algebra.E_In (e1, es) ->
      sse_wrap "in"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr_list es)))
  | SPARQL11_Algebra.E_NotIn (e1, es) ->
      sse_wrap "notin"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr_list es)))
  | SPARQL11_Algebra.E_StrLen e1 -> sse_wrap "strlen" (sse_expr e1)
  | SPARQL11_Algebra.E_Substr (e1, e2, FStar_Pervasives_Native.None) ->
      sse_wrap "substr"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_Substr (e1, e2, FStar_Pervasives_Native.Some e3) ->
      sse_wrap "substr"
        (Prims.strcat (sse_expr e1)
           (Prims.strcat " "
              (Prims.strcat (sse_expr e2) (Prims.strcat " " (sse_expr e3)))))
  | SPARQL11_Algebra.E_UCase e1 -> sse_wrap "ucase" (sse_expr e1)
  | SPARQL11_Algebra.E_LCase e1 -> sse_wrap "lcase" (sse_expr e1)
  | SPARQL11_Algebra.E_StrStarts (e1, e2) ->
      sse_wrap "strstarts"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_StrEnds (e1, e2) ->
      sse_wrap "strends"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_Contains (e1, e2) ->
      sse_wrap "contains"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_StrBefore (e1, e2) ->
      sse_wrap "strbefore"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_StrAfter (e1, e2) ->
      sse_wrap "strafter"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_EncodeForUri e1 ->
      sse_wrap "encode_for_uri" (sse_expr e1)
  | SPARQL11_Algebra.E_Replace (e1, e2, e3, FStar_Pervasives_Native.None) ->
      sse_wrap "replace"
        (Prims.strcat (sse_expr e1)
           (Prims.strcat " "
              (Prims.strcat (sse_expr e2) (Prims.strcat " " (sse_expr e3)))))
  | SPARQL11_Algebra.E_Replace (e1, e2, e3, FStar_Pervasives_Native.Some e4)
      ->
      sse_wrap "replace"
        (Prims.strcat (sse_expr e1)
           (Prims.strcat " "
              (Prims.strcat (sse_expr e2)
                 (Prims.strcat " "
                    (Prims.strcat (sse_expr e3)
                       (Prims.strcat " " (sse_expr e4)))))))
  | SPARQL11_Algebra.E_Regex (e1, e2, FStar_Pervasives_Native.None) ->
      sse_wrap "regex"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_Regex (e1, e2, FStar_Pervasives_Native.Some e3) ->
      sse_wrap "regex"
        (Prims.strcat (sse_expr e1)
           (Prims.strcat " "
              (Prims.strcat (sse_expr e2) (Prims.strcat " " (sse_expr e3)))))
  | SPARQL11_Algebra.E_Abs e1 -> sse_wrap "abs" (sse_expr e1)
  | SPARQL11_Algebra.E_Round e1 -> sse_wrap "round" (sse_expr e1)
  | SPARQL11_Algebra.E_Ceil e1 -> sse_wrap "ceil" (sse_expr e1)
  | SPARQL11_Algebra.E_Floor e1 -> sse_wrap "floor" (sse_expr e1)
  | SPARQL11_Algebra.E_MD5 e1 -> sse_wrap "md5" (sse_expr e1)
  | SPARQL11_Algebra.E_SHA1 e1 -> sse_wrap "sha1" (sse_expr e1)
  | SPARQL11_Algebra.E_SHA256 e1 -> sse_wrap "sha256" (sse_expr e1)
  | SPARQL11_Algebra.E_SHA384 e1 -> sse_wrap "sha384" (sse_expr e1)
  | SPARQL11_Algebra.E_SHA512 e1 -> sse_wrap "sha512" (sse_expr e1)
  | SPARQL11_Algebra.E_Now -> "(now)"
  | SPARQL11_Algebra.E_Year e1 -> sse_wrap "year" (sse_expr e1)
  | SPARQL11_Algebra.E_Month e1 -> sse_wrap "month" (sse_expr e1)
  | SPARQL11_Algebra.E_Day e1 -> sse_wrap "day" (sse_expr e1)
  | SPARQL11_Algebra.E_Hours e1 -> sse_wrap "hours" (sse_expr e1)
  | SPARQL11_Algebra.E_Minutes e1 -> sse_wrap "minutes" (sse_expr e1)
  | SPARQL11_Algebra.E_Seconds e1 -> sse_wrap "seconds" (sse_expr e1)
  | SPARQL11_Algebra.E_Timezone e1 -> sse_wrap "timezone" (sse_expr e1)
  | SPARQL11_Algebra.E_Tz e1 -> sse_wrap "tz" (sse_expr e1)
  | SPARQL11_Algebra.E_SameTerm (e1, e2) ->
      sse_wrap "sameTerm"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_StrDt (e1, e2) ->
      sse_wrap "strdt"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_StrLang (e1, e2) ->
      sse_wrap "strlang"
        (Prims.strcat (sse_expr e1) (Prims.strcat " " (sse_expr e2)))
  | SPARQL11_Algebra.E_Exists ggp -> sse_wrap "exists" (sse_ggp ggp)
  | SPARQL11_Algebra.E_NotExists ggp -> sse_wrap "notexists" (sse_ggp ggp)
  | SPARQL11_Algebra.E_Aggregate (agg, distinct, e1) ->
      sse_wrap "agg" (sse_expr e1)
  | SPARQL11_Algebra.E_FunctionCall (iri, args) ->
      sse_wrap (Prims.strcat "call " iri) (sse_expr_list args)
and sse_expr_list (es : SPARQL11_Algebra.expr Prims.list) : Prims.string=
  match es with
  | [] -> ""
  | e::[] -> sse_expr e
  | e::rest ->
      Prims.strcat (sse_expr e) (Prims.strcat " " (sse_expr_list rest))
and sse_path (pp : SPARQL11_Algebra.property_path) : Prims.string=
  match pp with
  | SPARQL11_Algebra.PP_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | SPARQL11_Algebra.PP_Inverse p -> sse_wrap "reverse" (sse_path p)
  | SPARQL11_Algebra.PP_Sequence (p1, p2) ->
      sse_wrap "seq"
        (Prims.strcat (sse_path p1) (Prims.strcat " " (sse_path p2)))
  | SPARQL11_Algebra.PP_Alternative (p1, p2) ->
      sse_wrap "alt"
        (Prims.strcat (sse_path p1) (Prims.strcat " " (sse_path p2)))
  | SPARQL11_Algebra.PP_ZeroOrMore p -> sse_wrap "path*" (sse_path p)
  | SPARQL11_Algebra.PP_OneOrMore p -> sse_wrap "path+" (sse_path p)
  | SPARQL11_Algebra.PP_ZeroOrOne p -> sse_wrap "path?" (sse_path p)
  | SPARQL11_Algebra.PP_NegatedSet ps ->
      sse_wrap "notoneof" (sse_path_list ps)
and sse_path_list (ps : SPARQL11_Algebra.property_path Prims.list) :
  Prims.string=
  match ps with
  | [] -> ""
  | p::[] -> sse_path p
  | p::rest ->
      Prims.strcat (sse_path p) (Prims.strcat " " (sse_path_list rest))
and sse_ggp (ggp : SPARQL11_Algebra.group_graph_pattern) : Prims.string=
  match ggp with
  | SPARQL11_Algebra.GP_Empty -> "(table unit)"
  | SPARQL11_Algebra.GP_BGP patterns -> sse_bgp patterns
  | SPARQL11_Algebra.GP_Join (g1, g2) ->
      sse_wrap "join"
        (Prims.strcat (sse_ggp g1) (Prims.strcat "\n  " (sse_ggp g2)))
  | SPARQL11_Algebra.GP_LeftJoin (g1, g2, cond) ->
      sse_wrap "leftjoin"
        (Prims.strcat (sse_ggp g1)
           (Prims.strcat "\n  "
              (Prims.strcat (sse_ggp g2)
                 (Prims.strcat "\n  " (sse_expr cond)))))
  | SPARQL11_Algebra.GP_Filter (e, g) ->
      sse_wrap "filter"
        (Prims.strcat (sse_expr e) (Prims.strcat "\n  " (sse_ggp g)))
  | SPARQL11_Algebra.GP_Union (g1, g2) ->
      sse_wrap "union"
        (Prims.strcat (sse_ggp g1) (Prims.strcat "\n  " (sse_ggp g2)))
  | SPARQL11_Algebra.GP_Graph (term, g) ->
      sse_wrap "graph"
        (Prims.strcat (sse_pattern_term term)
           (Prims.strcat "\n  " (sse_ggp g)))
  | SPARQL11_Algebra.GP_Minus (g1, g2) ->
      sse_wrap "minus"
        (Prims.strcat (sse_ggp g1) (Prims.strcat "\n  " (sse_ggp g2)))
  | SPARQL11_Algebra.GP_Bind (e, v, g) ->
      sse_wrap "extend"
        (Prims.strcat "(?"
           (Prims.strcat v
              (Prims.strcat " "
                 (Prims.strcat (sse_expr e)
                    (Prims.strcat ")\n  " (sse_ggp g))))))
  | SPARQL11_Algebra.GP_Values (vars, rows) ->
      sse_wrap "table" (sse_vars vars)
  | SPARQL11_Algebra.GP_Service (iri, g, silent) ->
      sse_wrap "service"
        (Prims.strcat (if silent then "SILENT " else "")
           (Prims.strcat "<"
              (Prims.strcat iri (Prims.strcat ">\n  " (sse_ggp g)))))
  | SPARQL11_Algebra.GP_SubSelect q -> sse_query q
  | SPARQL11_Algebra.GP_PropertyPath (s, pp, o) ->
      sse_wrap "path"
        (Prims.strcat (sse_pattern_subject s)
           (Prims.strcat " "
              (Prims.strcat (sse_path pp)
                 (Prims.strcat " " (sse_pattern_term o)))))
and sse_vars (vs : SPARQL11_Algebra.var_name Prims.list) : Prims.string=
  match vs with
  | [] -> ""
  | v::[] -> Prims.strcat "?" v
  | v::rest ->
      Prims.strcat "?" (Prims.strcat v (Prims.strcat " " (sse_vars rest)))
and sse_select_item (si : SPARQL11_Algebra.select_item) : Prims.string=
  match si with
  | SPARQL11_Algebra.SI_Var v -> Prims.strcat "?" v
  | SPARQL11_Algebra.SI_Expr (e, v) ->
      sse_wrap "as" (Prims.strcat (sse_expr e) (Prims.strcat " ?" v))
and sse_select_items (items : SPARQL11_Algebra.select_item Prims.list) :
  Prims.string=
  match items with
  | [] -> ""
  | i::[] -> sse_select_item i
  | i::rest ->
      Prims.strcat (sse_select_item i)
        (Prims.strcat " " (sse_select_items rest))
and sse_query (q : SPARQL11_Algebra.query) : Prims.string=
  let form =
    match q.SPARQL11_Algebra.q_form with
    | SPARQL11_Algebra.QF_Select (SPARQL11_Algebra.Select_All) ->
        "(project *"
    | SPARQL11_Algebra.QF_Select (SPARQL11_Algebra.Select_Vars items) ->
        Prims.strcat "(project (" (Prims.strcat (sse_select_items items) ")")
    | SPARQL11_Algebra.QF_Ask -> "(ask"
    | SPARQL11_Algebra.QF_Construct uu___ -> "(construct"
    | SPARQL11_Algebra.QF_Describe uu___ -> "(describe" in
  let body = sse_ggp q.SPARQL11_Algebra.q_pattern in
  let modifiers =
    Prims.strcat
      (match (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by
       with
       | FStar_Pervasives_Native.None -> ""
       | FStar_Pervasives_Native.Some uu___ -> "\n  (order ...)")
      (Prims.strcat
         (if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct
          then "\n  (distinct)"
          else "")
         (match (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit
          with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some n ->
              Prims.strcat "\n  (slice _ "
                (Prims.strcat (Prims.string_of_int n) ")"))) in
  Prims.strcat form
    (Prims.strcat "\n  " (Prims.strcat body (Prims.strcat modifiers ")")))
