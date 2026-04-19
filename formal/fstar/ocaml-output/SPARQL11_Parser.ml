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
  | Tok_FROM 
  | Tok_NAMED 
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
  | Tok_LOAD 
  | Tok_CLEAR 
  | Tok_DROP 
  | Tok_CREATE 
  | Tok_ADD 
  | Tok_MOVE 
  | Tok_COPY 
  | Tok_INSERT 
  | Tok_DELETE 
  | Tok_DATA 
  | Tok_INTO 
  | Tok_TO 
  | Tok_WITH 
  | Tok_USING 
  | Tok_DEFAULT 
  | Tok_ALL 
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
let uu___is_Tok_FROM (projectee : token) : Prims.bool=
  match projectee with | Tok_FROM -> true | uu___ -> false
let uu___is_Tok_NAMED (projectee : token) : Prims.bool=
  match projectee with | Tok_NAMED -> true | uu___ -> false
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
let uu___is_Tok_LOAD (projectee : token) : Prims.bool=
  match projectee with | Tok_LOAD -> true | uu___ -> false
let uu___is_Tok_CLEAR (projectee : token) : Prims.bool=
  match projectee with | Tok_CLEAR -> true | uu___ -> false
let uu___is_Tok_DROP (projectee : token) : Prims.bool=
  match projectee with | Tok_DROP -> true | uu___ -> false
let uu___is_Tok_CREATE (projectee : token) : Prims.bool=
  match projectee with | Tok_CREATE -> true | uu___ -> false
let uu___is_Tok_ADD (projectee : token) : Prims.bool=
  match projectee with | Tok_ADD -> true | uu___ -> false
let uu___is_Tok_MOVE (projectee : token) : Prims.bool=
  match projectee with | Tok_MOVE -> true | uu___ -> false
let uu___is_Tok_COPY (projectee : token) : Prims.bool=
  match projectee with | Tok_COPY -> true | uu___ -> false
let uu___is_Tok_INSERT (projectee : token) : Prims.bool=
  match projectee with | Tok_INSERT -> true | uu___ -> false
let uu___is_Tok_DELETE (projectee : token) : Prims.bool=
  match projectee with | Tok_DELETE -> true | uu___ -> false
let uu___is_Tok_DATA (projectee : token) : Prims.bool=
  match projectee with | Tok_DATA -> true | uu___ -> false
let uu___is_Tok_INTO (projectee : token) : Prims.bool=
  match projectee with | Tok_INTO -> true | uu___ -> false
let uu___is_Tok_TO (projectee : token) : Prims.bool=
  match projectee with | Tok_TO -> true | uu___ -> false
let uu___is_Tok_WITH (projectee : token) : Prims.bool=
  match projectee with | Tok_WITH -> true | uu___ -> false
let uu___is_Tok_USING (projectee : token) : Prims.bool=
  match projectee with | Tok_USING -> true | uu___ -> false
let uu___is_Tok_DEFAULT (projectee : token) : Prims.bool=
  match projectee with | Tok_DEFAULT -> true | uu___ -> false
let uu___is_Tok_ALL (projectee : token) : Prims.bool=
  match projectee with | Tok_ALL -> true | uu___ -> false
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
let char_to_string (c : FStar_Char.char) : Prims.string=
  FStar_String.string_of_list [c]
let is_hex_digit (c : FStar_Char.char) : Prims.bool=
  let code = char_code c in
  (((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))) ||
     ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x46)))))
    || ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x66))))
let hex_value (c : FStar_Char.char) : Prims.nat=
  let code = char_code c in
  if (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
  then code - (Prims.of_int (0x30))
  else
    if (code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x46)))
    then (code - (Prims.of_int (0x41))) + (Prims.of_int (10))
    else
      if (code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x66)))
      then (code - (Prims.of_int (0x61))) + (Prims.of_int (10))
      else Prims.int_zero
let utf8_of_codepoint (cp_z : Prims.nat) : Prims.string =
  let cp = Z.to_int cp_z in
  let open Stdlib in
  if cp < 0x80 then String.make 1 (Char.chr cp)
  else if cp < 0x800 then
    let b0 = 0xC0 lor (cp lsr 6) in
    let b1 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 2 in
    Bytes.set s 0 (Char.chr b0); Bytes.set s 1 (Char.chr b1);
    Bytes.to_string s
  else if cp < 0x10000 then
    let b0 = 0xE0 lor (cp lsr 12) in
    let b1 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b2 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 3 in
    Bytes.set s 0 (Char.chr b0); Bytes.set s 1 (Char.chr b1); Bytes.set s 2 (Char.chr b2);
    Bytes.to_string s
  else
    let b0 = 0xF0 lor (cp lsr 18) in
    let b1 = 0x80 lor ((cp lsr 12) land 0x3F) in
    let b2 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b3 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 4 in
    Bytes.set s 0 (Char.chr b0); Bytes.set s 1 (Char.chr b1);
    Bytes.set s 2 (Char.chr b2); Bytes.set s 3 (Char.chr b3);
    Bytes.to_string s
let process_iri_escapes (s : Prims.string) : Prims.string =
  let open Stdlib in
  (* Process backslash-u and backslash-U escapes in IRI strings *)
  let len = String.length s in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if !i + 1 < len && s.[!i] = '\\' then begin
      let next = s.[!i + 1] in
      if next = 'u' && !i + 5 < len then begin
        let hex = String.sub s (!i + 2) 4 in
        (try let cp = int_of_string ("0x" ^ hex) in
             Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with _ -> Buffer.add_string buf (String.sub s !i 6));
        i := !i + 6
      end else if next = 'U' && !i + 9 < len then begin
        let hex = String.sub s (!i + 2) 8 in
        (try let cp = int_of_string ("0x" ^ hex) in
             Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with _ -> Buffer.add_string buf (String.sub s !i 10));
        i := !i + 10
      end else begin
        Buffer.add_char buf s.[!i];
        i := !i + 1
      end
    end else begin
      Buffer.add_char buf s.[!i];
      i := !i + 1
    end
  done;
  Buffer.contents buf
let process_string_escapes (s : Prims.string) : Prims.string =
  let open Stdlib in
  (* Process string escape sequences: backslash-t, -n, -r, etc. *)
  let len = String.length s in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if !i + 1 < len && s.[!i] = '\\' then begin
      let next = s.[!i + 1] in
      if next = 't' then (Buffer.add_char buf '\t'; i := !i + 2)
      else if next = 'n' then (Buffer.add_char buf '\n'; i := !i + 2)
      else if next = 'r' then (Buffer.add_char buf '\r'; i := !i + 2)
      else if next = '\\' then (Buffer.add_char buf '\\'; i := !i + 2)
      else if next = '"' then (Buffer.add_char buf '"'; i := !i + 2)
      else if next = '\'' then (Buffer.add_char buf '\''; i := !i + 2)
      else if next = 'b' then (Buffer.add_char buf '\008'; i := !i + 2)
      else if next = 'f' then (Buffer.add_char buf '\012'; i := !i + 2)
      else if next = 'u' && !i + 5 < len then begin
        let hex = String.sub s (!i + 2) 4 in
        (try let cp = int_of_string ("0x" ^ hex) in
             if cp >= 0xD800 && cp <= 0xDFFF then
               failwith "invalid Unicode codepoint: surrogate"
             else
               Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with Failure msg -> raise (Failure msg)
            | _ -> Buffer.add_string buf (String.sub s !i 6));
        i := !i + 6
      end else if next = 'U' && !i + 9 < len then begin
        let hex = String.sub s (!i + 2) 8 in
        (try let cp = int_of_string ("0x" ^ hex) in
             if cp >= 0xD800 && cp <= 0xDFFF then
               failwith "invalid Unicode codepoint: surrogate"
             else
               Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with Failure msg -> raise (Failure msg)
            | _ -> Buffer.add_string buf (String.sub s !i 10));
        i := !i + 10
      end else begin
        Buffer.add_char buf s.[!i];
        i := !i + 1
      end
    end else begin
      Buffer.add_char buf s.[!i];
      i := !i + 1
    end
  done;
  Buffer.contents buf
let rec find_char_pos (input : Prims.string) (p : pos) (target : Prims.nat) :
  pos FStar_Pervasives_Native.option=
  if at_end input p
  then FStar_Pervasives_Native.None
  else
    if (char_code (peek_char input p)) = target
    then FStar_Pervasives_Native.Some p
    else find_char_pos input (p + Prims.int_one) target
let rec trim_trailing_dots (input : Prims.string) (start : pos)
  (end_pos : pos) : pos=
  if (end_pos = Prims.int_zero) || (end_pos <= start)
  then start
  else
    if
      (char_code (char_at input (end_pos - Prims.int_one))) =
        (Prims.of_int (0x2E))
    then
      (if
         ((end_pos >= (Prims.of_int (2))) &&
            ((end_pos - (Prims.of_int (2))) >= start))
           &&
           ((char_code (char_at input (end_pos - (Prims.of_int (2))))) =
              (Prims.of_int (0x5C)))
       then end_pos
       else trim_trailing_dots input start (end_pos - Prims.int_one))
    else end_pos
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
let rec scan_iri_end (input : Prims.string) (p : pos) : pos=
  if at_end input p
  then p
  else
    (let c = peek_char input p in
     if (char_code c) = (Prims.of_int (0x3E))
     then p
     else
       if (char_code c) = (Prims.of_int (0x5C))
       then
         (if at_end input (p + Prims.int_one)
          then p + Prims.int_one
          else scan_iri_end input (p + (Prims.of_int (2))))
       else scan_iri_end input (p + Prims.int_one))
let safe_sub (a : Prims.int) (b : Prims.int) : Prims.nat=
  if a >= b then a - b else Prims.int_zero
(* Resolve a potentially relative IRI against the current BASE.
   If the IRI is already absolute (passes is_iri), return it unchanged.
   Otherwise, try resolving against the global current_base_iri_ref. *)
let resolve_tok_iri (i : Prims.string) : Prims.string =
  if RDF_Graph_Executable.is_iri i then i
  else match !(SPARQL11_Algebra.current_base_iri_ref) with
    | Some base -> SPARQL11_Algebra.resolve_iri base i
    | None -> i

let scan_iri (input : Prims.string) (p : pos) : (Prims.string * pos)=
  let end_p = scan_iri_end input p in
  let len = if end_p >= p then end_p - p else Prims.int_zero in
  let raw = substring input p len in
  let processed = process_iri_escapes raw in
  if at_end input end_p
  then (processed, end_p)
  else (processed, (end_p + Prims.int_one))
let rec scan_short_string_end (input : Prims.string) (p : pos)
  (q_code : Prims.nat) : pos=
  if at_end input p
  then p
  else
    (let c = peek_char input p in
     if (char_code c) = q_code
     then p
     else
       if (char_code c) = (Prims.of_int (0x5C))
       then
         (if at_end input (p + Prims.int_one)
          then p + Prims.int_one
          else scan_short_string_end input (p + (Prims.of_int (2))) q_code)
       else scan_short_string_end input (p + Prims.int_one) q_code)
let rec scan_long_string_end (input : Prims.string) (p : pos)
  (q_code : Prims.nat) : pos=
  if at_end input p
  then p
  else
    (let c = peek_char input p in
     if
       (((((char_code c) = q_code) &&
            (Prims.op_Negation (at_end input (p + Prims.int_one))))
           && ((char_code (peek_char input (p + Prims.int_one))) = q_code))
          && (Prims.op_Negation (at_end input (p + (Prims.of_int (2))))))
         && ((char_code (peek_char input (p + (Prims.of_int (2))))) = q_code)
     then p
     else
       if (char_code c) = (Prims.of_int (0x5C))
       then
         (if at_end input (p + Prims.int_one)
          then p + Prims.int_one
          else scan_long_string_end input (p + (Prims.of_int (2))) q_code)
       else scan_long_string_end input (p + Prims.int_one) q_code)
let scan_string (input : Prims.string) (p : pos) : (Prims.string * pos)=
  let q = peek_char input p in
  let q_code = char_code q in
  let is_long =
    (((Prims.op_Negation (at_end input (p + Prims.int_one))) &&
        ((char_code (peek_char input (p + Prims.int_one))) = q_code))
       && (Prims.op_Negation (at_end input (p + (Prims.of_int (2))))))
      && ((char_code (peek_char input (p + (Prims.of_int (2))))) = q_code) in
  if is_long
  then
    let p_start = p + (Prims.of_int (3)) in
    let end_p = scan_long_string_end input p_start q_code in
    let raw = substring input p_start (safe_sub end_p p_start) in
    ((process_string_escapes raw), (end_p + (Prims.of_int (3))))
  else
    (let p_start = p + Prims.int_one in
     let end_p = scan_short_string_end input p_start q_code in
     let raw = substring input p_start (safe_sub end_p p_start) in
     ((process_string_escapes raw), (end_p + Prims.int_one)))
let rec scan_pn_chars_end (input : Prims.string) (p : pos) : pos=
  if at_end input p
  then p
  else
    if is_pn_char (peek_char input p)
    then scan_pn_chars_end input (p + Prims.int_one)
    else p
let rec scan_pn_local_end (input : Prims.string) (p : pos) : pos=
  if at_end input p
  then p
  else
    (let c = peek_char input p in
     if
       ((is_pn_char c) || ((char_code c) = (Prims.of_int (0x3A)))) ||
         ((char_code c) = (Prims.of_int (0x25)))
     then scan_pn_local_end input (p + Prims.int_one)
     else
       if (char_code c) = (Prims.of_int (0x5C))
       then
         (if at_end input (p + Prims.int_one)
          then p
          else
            if is_pn_local_esc (peek_char input (p + Prims.int_one))
            then scan_pn_local_end input (p + (Prims.of_int (2)))
            else p)
       else p)
let keyword_of_upper (upper : Prims.string) (original : Prims.string) :
  token=
  if streq upper "SELECT"
  then Tok_SELECT
  else
    if streq upper "ASK"
    then Tok_ASK
    else
      if streq upper "CONSTRUCT"
      then Tok_CONSTRUCT
      else
        if streq upper "DESCRIBE"
        then Tok_DESCRIBE
        else
          if streq upper "WHERE"
          then Tok_WHERE
          else
            if streq upper "PREFIX"
            then Tok_PREFIX
            else
              if streq upper "BASE"
              then Tok_BASE
              else
                if streq upper "OPTIONAL"
                then Tok_OPTIONAL
                else
                  if streq upper "UNION"
                  then Tok_UNION
                  else
                    if streq upper "MINUS"
                    then Tok_MINUS_KW
                    else
                      if streq upper "FILTER"
                      then Tok_FILTER
                      else
                        if streq upper "BIND"
                        then Tok_BIND
                        else
                          if streq upper "VALUES"
                          then Tok_VALUES
                          else
                            if streq upper "GRAPH"
                            then Tok_GRAPH
                            else
                              if streq upper "SERVICE"
                              then Tok_SERVICE
                              else
                                if streq upper "SILENT"
                                then Tok_SILENT
                                else
                                  if streq upper "EXISTS"
                                  then Tok_EXISTS
                                  else
                                    if streq upper "NOT"
                                    then Tok_NOT
                                    else
                                      if streq upper "AS"
                                      then Tok_AS
                                      else
                                        if streq upper "DISTINCT"
                                        then Tok_DISTINCT
                                        else
                                          if streq upper "REDUCED"
                                          then Tok_REDUCED
                                          else
                                            if streq upper "ORDER"
                                            then Tok_ORDER
                                            else
                                              if streq upper "BY"
                                              then Tok_BY
                                              else
                                                if streq upper "ASC"
                                                then Tok_ASC
                                                else
                                                  if streq upper "DESC"
                                                  then Tok_DESC
                                                  else
                                                    if streq upper "GROUP"
                                                    then Tok_GROUP
                                                    else
                                                      if streq upper "HAVING"
                                                      then Tok_HAVING
                                                      else
                                                        if
                                                          streq upper "LIMIT"
                                                        then Tok_LIMIT
                                                        else
                                                          if
                                                            streq upper
                                                              "OFFSET"
                                                          then Tok_OFFSET
                                                          else
                                                            if
                                                              streq upper
                                                                "FROM"
                                                            then Tok_FROM
                                                            else
                                                              if
                                                                streq upper
                                                                  "NAMED"
                                                              then Tok_NAMED
                                                              else
                                                                if
                                                                  streq upper
                                                                    "IN"
                                                                then Tok_IN
                                                                else
                                                                  if
                                                                    streq
                                                                    upper
                                                                    "TRUE"
                                                                  then
                                                                    Tok_TRUE
                                                                  else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "FALSE"
                                                                    then
                                                                    Tok_FALSE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "UNDEF"
                                                                    then
                                                                    Tok_UNDEF
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper "A"
                                                                    then
                                                                    Tok_A
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "STR"
                                                                    then
                                                                    Tok_STR
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "LANG"
                                                                    then
                                                                    Tok_LANG
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "LANGMATCHES"
                                                                    then
                                                                    Tok_LANGMATCHES
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "DATATYPE"
                                                                    then
                                                                    Tok_DATATYPE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "BOUND"
                                                                    then
                                                                    Tok_BOUND
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "IF"
                                                                    then
                                                                    Tok_IF
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "IRI"
                                                                    then
                                                                    Tok_IRI_KW
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "URI"
                                                                    then
                                                                    Tok_URI
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "BNODE"
                                                                    then
                                                                    Tok_BNODE_KW
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "RAND"
                                                                    then
                                                                    Tok_RAND
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "ABS"
                                                                    then
                                                                    Tok_ABS
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "CEIL"
                                                                    then
                                                                    Tok_CEIL
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "FLOOR"
                                                                    then
                                                                    Tok_FLOOR
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "ROUND"
                                                                    then
                                                                    Tok_ROUND
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "CONCAT"
                                                                    then
                                                                    Tok_CONCAT
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "STRLEN"
                                                                    then
                                                                    Tok_STRLEN
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "UCASE"
                                                                    then
                                                                    Tok_UCASE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "LCASE"
                                                                    then
                                                                    Tok_LCASE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "ENCODE_FOR_URI"
                                                                    then
                                                                    Tok_ENCODE_FOR_URI
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "CONTAINS"
                                                                    then
                                                                    Tok_CONTAINS
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "STRSTARTS"
                                                                    then
                                                                    Tok_STRSTARTS
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "STRENDS"
                                                                    then
                                                                    Tok_STRENDS
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "STRBEFORE"
                                                                    then
                                                                    Tok_STRBEFORE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "STRAFTER"
                                                                    then
                                                                    Tok_STRAFTER
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "REPLACE"
                                                                    then
                                                                    Tok_REPLACE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "REGEX"
                                                                    then
                                                                    Tok_REGEX
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SUBSTR"
                                                                    then
                                                                    Tok_SUBSTR
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SUBSTRING"
                                                                    then
                                                                    Tok_SUBSTR
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "ISIRI"
                                                                    then
                                                                    Tok_ISIRI
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "ISURI"
                                                                    then
                                                                    Tok_ISIRI
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "ISBLANK"
                                                                    then
                                                                    Tok_ISBLANK
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "ISLITERAL"
                                                                    then
                                                                    Tok_ISLITERAL
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "ISNUMERIC"
                                                                    then
                                                                    Tok_ISNUMERIC
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SAMETERM"
                                                                    then
                                                                    Tok_SAMETERM
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "STRDT"
                                                                    then
                                                                    Tok_STRDT
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "STRLANG"
                                                                    then
                                                                    Tok_STRLANG
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "COUNT"
                                                                    then
                                                                    Tok_COUNT
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SUM"
                                                                    then
                                                                    Tok_SUM
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "MIN"
                                                                    then
                                                                    Tok_MIN_KW
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "MAX"
                                                                    then
                                                                    Tok_MAX_KW
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "AVG"
                                                                    then
                                                                    Tok_AVG
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "GROUP_CONCAT"
                                                                    then
                                                                    Tok_GROUP_CONCAT
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SAMPLE"
                                                                    then
                                                                    Tok_SAMPLE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SEPARATOR"
                                                                    then
                                                                    Tok_SEPARATOR
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "COALESCE"
                                                                    then
                                                                    Tok_COALESCE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "NOW"
                                                                    then
                                                                    Tok_NOW
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "UUID"
                                                                    then
                                                                    Tok_UUID
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "STRUUID"
                                                                    then
                                                                    Tok_STRUUID
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "YEAR"
                                                                    then
                                                                    Tok_YEAR
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "MONTH"
                                                                    then
                                                                    Tok_MONTH
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "DAY"
                                                                    then
                                                                    Tok_DAY
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "HOURS"
                                                                    then
                                                                    Tok_HOURS
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "MINUTES"
                                                                    then
                                                                    Tok_MINUTES
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SECONDS"
                                                                    then
                                                                    Tok_SECONDS
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "TIMEZONE"
                                                                    then
                                                                    Tok_TIMEZONE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "TZ"
                                                                    then
                                                                    Tok_TZ
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "MD5"
                                                                    then
                                                                    Tok_MD5
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SHA1"
                                                                    then
                                                                    Tok_SHA1
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SHA256"
                                                                    then
                                                                    Tok_SHA256
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SHA384"
                                                                    then
                                                                    Tok_SHA384
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "SHA512"
                                                                    then
                                                                    Tok_SHA512
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "LOAD"
                                                                    then
                                                                    Tok_LOAD
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "CLEAR"
                                                                    then
                                                                    Tok_CLEAR
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "DROP"
                                                                    then
                                                                    Tok_DROP
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "CREATE"
                                                                    then
                                                                    Tok_CREATE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "ADD"
                                                                    then
                                                                    Tok_ADD
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "MOVE"
                                                                    then
                                                                    Tok_MOVE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "COPY"
                                                                    then
                                                                    Tok_COPY
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "INSERT"
                                                                    then
                                                                    Tok_INSERT
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "DELETE"
                                                                    then
                                                                    Tok_DELETE
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "DATA"
                                                                    then
                                                                    Tok_DATA
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "INTO"
                                                                    then
                                                                    Tok_INTO
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "TO"
                                                                    then
                                                                    Tok_TO
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "WITH"
                                                                    then
                                                                    Tok_WITH
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "USING"
                                                                    then
                                                                    Tok_USING
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "DEFAULT"
                                                                    then
                                                                    Tok_DEFAULT
                                                                    else
                                                                    if
                                                                    streq
                                                                    upper
                                                                    "ALL"
                                                                    then
                                                                    Tok_ALL
                                                                    else
                                                                    Tok_PNAME
                                                                    original
let scan_pname_or_keyword (input : Prims.string) (p : pos) : lex_result=
  let p1 = scan_pn_chars_end input p in
  if
    (Prims.op_Negation (at_end input p1)) &&
      ((char_code (peek_char input p1)) = (Prims.of_int (0x3A)))
  then
    let p2 = scan_pn_local_end input (p1 + Prims.int_one) in
    let p21 = trim_trailing_dots input p p2 in
    ((Tok_PNAME (substring input p (safe_sub p21 p))), p21)
  else
    (let word = substring input p (safe_sub p1 p) in
     ((keyword_of_upper (string_upper word) word), p1))
let rec scan_digits_end (input : Prims.string) (p : pos) : pos=
  if at_end input p
  then p
  else
    if is_digit (peek_char input p)
    then scan_digits_end input (p + Prims.int_one)
    else p
let scan_number (input : Prims.string) (p : pos) : lex_result=
  let p1 = scan_digits_end input p in
  let has_dot =
    (((Prims.op_Negation (at_end input p1)) &&
        ((char_code (peek_char input p1)) = (Prims.of_int (0x2E))))
       && (Prims.op_Negation (at_end input (p1 + Prims.int_one))))
      && (is_digit (peek_char input (p1 + Prims.int_one))) in
  let p2 = if has_dot then scan_digits_end input (p1 + Prims.int_one) else p1 in
  let has_exp =
    (Prims.op_Negation (at_end input p2)) &&
      (((char_code (peek_char input p2)) = (Prims.of_int (0x65))) ||
         ((char_code (peek_char input p2)) = (Prims.of_int (0x45)))) in
  let p3 =
    if has_exp
    then
      let pe = p2 + Prims.int_one in
      let pe1 =
        if
          (Prims.op_Negation (at_end input pe)) &&
            (((char_code (peek_char input pe)) = (Prims.of_int (0x2B))) ||
               ((char_code (peek_char input pe)) = (Prims.of_int (0x2D))))
        then pe + Prims.int_one
        else pe in
      scan_digits_end input pe1
    else p2 in
  let text = substring input p (safe_sub p3 p) in
  if has_exp
  then ((Tok_DOUBLE text), p3)
  else if has_dot then ((Tok_DECIMAL text), p3) else ((Tok_INTEGER text), p3)
let rec scan_bnode_chars_end (input : Prims.string) (p : pos) : pos=
  if at_end input p
  then p
  else
    if is_pn_char (peek_char input p)
    then scan_bnode_chars_end input (p + Prims.int_one)
    else p
let scan_bnode_label (input : Prims.string) (p : pos) : (Prims.string * pos)=
  let p' = scan_bnode_chars_end input p in
  let p'1 = trim_trailing_dots input p p' in
  ((substring input p (safe_sub p'1 p)), p'1)
let rec scan_var_chars_end (input : Prims.string) (p : pos) : pos=
  if at_end input p
  then p
  else
    (let c = peek_char input p in
     if (is_alnum c) || ((char_code c) = (Prims.of_int (0x5F)))
     then scan_var_chars_end input (p + Prims.int_one)
     else p)
let scan_var_name (input : Prims.string) (p : pos) : (Prims.string * pos)=
  let p' = scan_var_chars_end input p in
  ((substring input p (safe_sub p' p)), p')
let rec scan_langtag_chars_end (input : Prims.string) (p : pos) : pos=
  if at_end input p
  then p
  else
    (let c = peek_char input p in
     if (is_alnum c) || ((char_code c) = (Prims.of_int (0x2D)))
     then scan_langtag_chars_end input (p + Prims.int_one)
     else p)
let scan_langtag (input : Prims.string) (p : pos) : (Prims.string * pos)=
  let p' = scan_langtag_chars_end input p in
  ((substring input p (safe_sub p' p)), p')
let rec has_gt_before_terminator (input : Prims.string) (p : pos) :
  Prims.bool=
  if at_end input p
  then false
  else
    (let code = char_code (peek_char input p) in
     if code = (Prims.of_int (0x3E))
     then true
     else
       if
         (((is_ws (peek_char input p)) || (code = (Prims.of_int (0x29)))) ||
            (code = (Prims.of_int (0x7D))))
           || (code = (Prims.of_int (0x5D)))
       then false
       else has_gt_before_terminator input (p + Prims.int_one))
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
          if at_end input (p1 + Prims.int_one)
          then (Tok_LT, (p1 + Prims.int_one))
          else
            (let next_code = char_code (peek_char input (p1 + Prims.int_one)) in
             if
               (((((((next_code >= (Prims.of_int (0x41))) &&
                       (next_code <= (Prims.of_int (0x5A))))
                      ||
                      ((next_code >= (Prims.of_int (0x61))) &&
                         (next_code <= (Prims.of_int (0x7A)))))
                     || (next_code = (Prims.of_int (0x3E))))
                    || (next_code = (Prims.of_int (0x5F))))
                   || (next_code = (Prims.of_int (0x2F))))
                  || (next_code = (Prims.of_int (0x23))))
                 ||
                 (((next_code = (Prims.of_int (0x3F))) ||
                     (next_code = (Prims.of_int (0x24))))
                    && (has_gt_before_terminator input (p1 + Prims.int_one)))
             then
               let uu___3 = scan_iri input (p1 + Prims.int_one) in
               match uu___3 with | (iri, p') -> ((Tok_IRI iri), p')
             else (Tok_LT, (p1 + Prims.int_one))))
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
let resolve_relative_iri_token
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (tok : token) : token=
  match tok with
  | Tok_IRI iri ->
      (match if RDF_Graph_Executable.is_iri iri
             then FStar_Pervasives_Native.Some iri
             else SPARQL11_Algebra.resolve_query_iri base iri
       with
       | FStar_Pervasives_Native.Some abs -> Tok_IRI abs
       | FStar_Pervasives_Native.None -> tok)
  | uu___ -> tok
let rec resolve_relative_iri_tokens
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (ts : token_stream) : token_stream=
  match ts with
  | [] -> []
  | t::rest -> (resolve_relative_iri_token base t) ::
      (resolve_relative_iri_tokens base rest)
type verb_or_path =
  | VSimple of SPARQL11_Algebra.pattern_term 
  | VPath of SPARQL11_Algebra.property_path 
let uu___is_VSimple (projectee : verb_or_path) : Prims.bool=
  match projectee with | VSimple _0 -> true | uu___ -> false
let __proj__VSimple__item___0 (projectee : verb_or_path) :
  SPARQL11_Algebra.pattern_term= match projectee with | VSimple _0 -> _0
let uu___is_VPath (projectee : verb_or_path) : Prims.bool=
  match projectee with | VPath _0 -> true | uu___ -> false
let __proj__VPath__item___0 (projectee : verb_or_path) :
  SPARQL11_Algebra.property_path= match projectee with | VPath _0 -> _0
type modifier_result =
  (SPARQL11_Algebra.solution_modifier * SPARQL11_Algebra.group_condition
    Prims.list FStar_Pervasives_Native.option *
    SPARQL11_Algebra.having_condition Prims.list
    FStar_Pervasives_Native.option)
let rec tokenize_loop (input : Prims.string) (p : pos)
  (acc : token Prims.list) (fuel : Prims.nat) : token Prims.list=
  if fuel = Prims.int_zero
  then FStar_List_Tot_Base.rev (Tok_EOF :: acc)
  else
    if p > (FStar_String.strlen input)
    then FStar_List_Tot_Base.rev (Tok_EOF :: acc)
    else
      (let uu___2 = next_token input p in
       match uu___2 with
       | (tok, p') ->
           (match tok with
            | Tok_EOF -> FStar_List_Tot_Base.rev (Tok_EOF :: acc)
            | uu___3 ->
                if p' <= p
                then FStar_List_Tot_Base.rev (Tok_EOF :: acc)
                else
                  tokenize_loop input p' (tok :: acc) (fuel - Prims.int_one)))
let tokenize (input : Prims.string) : token Prims.list=
  tokenize_loop input Prims.int_zero []
    ((FStar_String.strlen input) + Prims.int_one)
let parse_ok (v : 'a) (ts : token_stream) : 'a parse_result= ParseOk (v, ts)
let parse_err (msg : Prims.string) : 'a parse_result= ParseErr msg
let parse_bind (p : 'a parse_result)
  (f : 'a -> token_stream -> 'b parse_result) : 'b parse_result=
  match p with | ParseOk (v, ts) -> f v ts | ParseErr msg -> ParseErr msg
let parse_peek (ts : token_stream) : token=
  match ts with | [] -> Tok_EOF | t::uu___ -> t
let parse_advance (ts : token_stream) : token_stream=
  match ts with | [] -> [] | uu___::rest -> rest
let token_eq (t1 : token) (t2 : token) : Prims.bool= t1 = t2
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
  match find_char_pos pn Prims.int_zero (Prims.of_int (0x3A)) with
  | FStar_Pervasives_Native.Some i ->
      ((substring pn Prims.int_zero i),
        (substring pn (i + Prims.int_one)
           (safe_sub (FStar_String.strlen pn) (i + Prims.int_one))))
  | FStar_Pervasives_Native.None -> (pn, "")
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
         let ri = resolve_tok_iri i in
         if RDF_Graph_Executable.is_iri ri
         then
           let ts' = parse_advance ts in
           (match parse_peek ts' with
            | Tok_LPAREN ->
                parse_func_call pm (fuel - Prims.int_one) ri
                  (parse_advance ts')
            | uu___1 -> ParseOk ((SPARQL11_Algebra.E_IRI ri), ts'))
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
         let ts' = parse_advance ts in
         (match parse_expect Tok_LPAREN ts' with
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
                              | ParseOk ((), ts5) ->
                                  ParseOk
                                    ((SPARQL11_Algebra.E_FunctionCall
                                        ("http://www.w3.org/2005/xpath-functions#langMatches",
                                          [e1; e2])), ts5))))))
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
     | Tok_NOW ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_LPAREN ->
              let ts'' = parse_advance ts' in
              (match parse_expect Tok_RPAREN ts'' with
               | ParseErr uu___1 -> ParseErr "expected ')' after NOW("
               | ParseOk ((), ts''') ->
                   ParseOk (SPARQL11_Algebra.E_Now, ts'''))
          | uu___1 -> ParseOk (SPARQL11_Algebra.E_Now, ts'))
     | Tok_RAND ->
         let ts' = parse_advance ts in
         (match parse_expect Tok_LPAREN ts' with
          | ParseErr e -> ParseErr e
          | ParseOk ((), ts'') ->
              (match parse_expect Tok_RPAREN ts'' with
               | ParseErr uu___1 -> ParseErr "expected ')' after RAND("
               | ParseOk ((), ts''') ->
                   ParseOk
                     ((SPARQL11_Algebra.E_FunctionCall
                         ("http://www.w3.org/2005/xpath-functions#rand", [])),
                       ts''')))
     | Tok_UUID ->
         let ts' = parse_advance ts in
         (match parse_expect Tok_LPAREN ts' with
          | ParseErr e -> ParseErr e
          | ParseOk ((), ts'') ->
              (match parse_expect Tok_RPAREN ts'' with
               | ParseErr uu___1 -> ParseErr "expected ')' after UUID("
               | ParseOk ((), ts''') ->
                   ParseOk
                     ((SPARQL11_Algebra.E_FunctionCall
                         ("http://www.w3.org/2005/xpath-functions#uuid", [])),
                       ts''')))
     | Tok_STRUUID ->
         let ts' = parse_advance ts in
         (match parse_expect Tok_LPAREN ts' with
          | ParseErr e -> ParseErr e
          | ParseOk ((), ts'') ->
              (match parse_expect Tok_RPAREN ts'' with
               | ParseErr uu___1 -> ParseErr "expected ')' after STRUUID("
               | ParseOk ((), ts''') ->
                   ParseOk
                     ((SPARQL11_Algebra.E_FunctionCall
                         ("http://www.w3.org/2005/xpath-functions#struuid",
                           [])), ts''')))
     | Tok_BNODE_KW ->
         let ts' = parse_advance ts in
         (match parse_expect Tok_LPAREN ts' with
          | ParseErr e -> ParseErr e
          | ParseOk ((), ts'') ->
              (match parse_peek ts'' with
               | Tok_RPAREN ->
                   let ts''' = parse_advance ts'' in
                   ParseOk
                     ((SPARQL11_Algebra.E_FunctionCall
                         ("http://www.w3.org/2005/xpath-functions#bnode", [])),
                       ts''')
               | uu___1 ->
                   (match parse_expr pm (fuel - Prims.int_one) ts'' with
                    | ParseErr e -> ParseErr e
                    | ParseOk (arg, ts''') ->
                        (match parse_expect Tok_RPAREN ts''' with
                         | ParseErr uu___2 ->
                             ParseErr "expected ')' after BNODE(expr"
                         | ParseOk ((), ts4) ->
                             ParseOk
                               ((SPARQL11_Algebra.E_FunctionCall
                                   ("http://www.w3.org/2005/xpath-functions#bnode",
                                     [arg])), ts4)))))
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
              let dt = resolve_tok_iri dt in
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
                       SPARQL11_Algebra.GP_Empty [] false ts'
               with
               | ParseErr m -> ParseErr m
               | ParseOk (g, ts'') ->
                   (match parse_expect Tok_RBRACE ts'' with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts''') -> ParseOk (g, ts''')))))
and is_local_labeled_bnode_id (b : Prims.string) : Prims.bool=
  let prefix = "_:bnode_" in
  let plen = FStar_String.strlen prefix in
  let blen = FStar_String.strlen b in
  if blen < plen
  then true
  else Prims.op_Negation (streq (substring b Prims.int_zero plen) prefix)
and local_string_mem (x : Prims.string) (xs : Prims.string Prims.list) :
  Prims.bool=
  match xs with
  | [] -> false
  | y::ys -> (streq x y) || (local_string_mem x ys)
and local_string_add_unique (x : Prims.string) (xs : Prims.string Prims.list)
  : Prims.string Prims.list= if local_string_mem x xs then xs else x :: xs
and local_string_union (xs : Prims.string Prims.list)
  (ys : Prims.string Prims.list) : Prims.string Prims.list=
  match xs with
  | [] -> ys
  | x::rest -> local_string_union rest (local_string_add_unique x ys)
and local_string_overlaps (xs : Prims.string Prims.list)
  (ys : Prims.string Prims.list) : Prims.bool=
  match xs with
  | [] -> false
  | x::rest -> (local_string_mem x ys) || (local_string_overlaps rest ys)
and local_bnodes_in_pattern_subject (ps : SPARQL11_Algebra.pattern_subject) :
  Prims.string Prims.list=
  match ps with
  | SPARQL11_Algebra.PS_BNode b ->
      if is_local_labeled_bnode_id b then [b] else []
  | uu___ -> []
and local_bnodes_in_pattern_term (pt : SPARQL11_Algebra.pattern_term) :
  Prims.string Prims.list=
  match pt with
  | SPARQL11_Algebra.PT_BNode b ->
      if is_local_labeled_bnode_id b then [b] else []
  | uu___ -> []
and local_bnodes_in_triple_pattern (tp : SPARQL11_Algebra.triple_pattern) :
  Prims.string Prims.list=
  local_string_union
    (local_bnodes_in_pattern_subject tp.SPARQL11_Algebra.tp_s)
    (local_string_union
       (local_bnodes_in_pattern_term tp.SPARQL11_Algebra.tp_p)
       (local_bnodes_in_pattern_term tp.SPARQL11_Algebra.tp_o))
and local_bnodes_in_bgp (bgp : SPARQL11_Algebra.bgp) :
  Prims.string Prims.list=
  match bgp with
  | [] -> []
  | tp::rest ->
      local_string_union (local_bnodes_in_triple_pattern tp)
        (local_bnodes_in_bgp rest)
and ggp_labeled_bnodes (g : SPARQL11_Algebra.group_graph_pattern) :
  Prims.string Prims.list=
  match g with
  | SPARQL11_Algebra.GP_BGP bgp -> local_bnodes_in_bgp bgp
  | SPARQL11_Algebra.GP_PropertyPath (ps, uu___, pt) ->
      local_string_union (local_bnodes_in_pattern_subject ps)
        (local_bnodes_in_pattern_term pt)
  | SPARQL11_Algebra.GP_Join (g1, g2) ->
      local_string_union (ggp_labeled_bnodes g1) (ggp_labeled_bnodes g2)
  | SPARQL11_Algebra.GP_Union (g1, g2) ->
      local_string_union (ggp_labeled_bnodes g1) (ggp_labeled_bnodes g2)
  | SPARQL11_Algebra.GP_Minus (g1, g2) ->
      local_string_union (ggp_labeled_bnodes g1) (ggp_labeled_bnodes g2)
  | SPARQL11_Algebra.GP_LeftJoin (g1, g2, uu___) ->
      local_string_union (ggp_labeled_bnodes g1) (ggp_labeled_bnodes g2)
  | SPARQL11_Algebra.GP_Filter (uu___, g1) -> ggp_labeled_bnodes g1
  | SPARQL11_Algebra.GP_Graph (uu___, g1) -> ggp_labeled_bnodes g1
  | SPARQL11_Algebra.GP_Bind (uu___, uu___1, g1) -> ggp_labeled_bnodes g1
  | SPARQL11_Algebra.GP_Service (uu___, g1, uu___1) -> ggp_labeled_bnodes g1
  | SPARQL11_Algebra.GP_SubSelect q ->
      ggp_labeled_bnodes q.SPARQL11_Algebra.q_pattern
  | SPARQL11_Algebra.GP_Values (uu___, uu___1) -> []
  | SPARQL11_Algebra.GP_Empty -> []
and parse_ggp_body (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.group_graph_pattern)
  (filters : SPARQL11_Algebra.expr Prims.list) (cross_scope : Prims.bool)
  (ts : token_stream) : SPARQL11_Algebra.group_graph_pattern parse_result=
  if fuel = Prims.int_zero
  then
    let g =
      FStar_List_Tot_Base.fold_left
        (fun g1 e -> SPARQL11_Algebra.GP_Filter (e, g1)) acc filters in
    ParseOk (g, ts)
  else
    (match parse_peek ts with
     | Tok_VAR uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_IRI uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_PNAME uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_BNODE uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_LBRACKET ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_LPAREN ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_A ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_INTEGER uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_DECIMAL uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_DOUBLE uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_STRING uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_TRUE ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
     | Tok_FALSE ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr m -> ParseErr m
          | ParseOk (triples_ggp, ts') ->
              if
                cross_scope &&
                  (local_string_overlaps (ggp_labeled_bnodes acc)
                     (ggp_labeled_bnodes triples_ggp))
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' = ggp_join acc triples_ggp in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters false
                   ts'))
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
              parse_ggp_body pm (fuel - Prims.int_one) acc' filters true ts'1)
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
              parse_ggp_body pm (fuel - Prims.int_one) acc' filters true ts'1)
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
                   parse_ggp_body pm (fuel - Prims.int_one) acc' filters true
                     ts'''1))
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
                        parse_ggp_body pm (fuel - Prims.int_one) acc' filters
                          true ts'''1)))
     | Tok_FILTER ->
         let ts' = parse_advance ts in
         (match parse_filter_expr pm (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts'') ->
              let ts''1 =
                match parse_peek ts'' with
                | Tok_DOT -> parse_advance ts''
                | uu___1 -> ts'' in
              parse_ggp_body pm (fuel - Prims.int_one) acc (e :: filters)
                cross_scope ts''1)
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
                             if SPARQL11_Algebra.ggp_has_var v acc
                             then ParseErr "BIND variable already in scope"
                             else
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
                                      | uu___2 -> ts5 in
                                    parse_ggp_body pm (fuel - Prims.int_one)
                                      acc' filters cross_scope ts51)
                         | uu___1 -> ParseErr "expected variable after AS"))))
     | Tok_VALUES ->
         (match parse_values_clause pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (g, ts') ->
              let acc' = ggp_join acc g in
              let ts'1 =
                match parse_peek ts' with
                | Tok_DOT -> parse_advance ts'
                | uu___1 -> ts' in
              parse_ggp_body pm (fuel - Prims.int_one) acc' filters
                cross_scope ts'1)
     | Tok_LBRACE ->
         (match parse_group_or_union pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (g, ts') ->
              if
                local_string_overlaps (ggp_labeled_bnodes acc)
                  (ggp_labeled_bnodes g)
              then
                ParseErr "blank node label reused across nested group scope"
              else
                (let acc' =
                   match acc with
                   | SPARQL11_Algebra.GP_Empty -> g
                   | uu___2 -> SPARQL11_Algebra.GP_Join (acc, g) in
                 let ts'1 =
                   match parse_peek ts' with
                   | Tok_DOT -> parse_advance ts'
                   | uu___2 -> ts' in
                 parse_ggp_body pm (fuel - Prims.int_one) acc' filters true
                   ts'1))
     | uu___1 ->
         let g =
           FStar_List_Tot_Base.fold_left
             (fun g1 e -> SPARQL11_Algebra.GP_Filter (e, g1)) acc filters in
         ParseOk (g, ts))
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
     | Tok_IRI_KW -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_URI -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_BNODE_KW -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_RAND -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_ABS -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_CEIL -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_FLOOR -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_ROUND -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_CONCAT -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_STRLEN -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_UCASE -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_LCASE -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_ENCODE_FOR_URI -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_CONTAINS -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_STRSTARTS -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_STRENDS -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_STRBEFORE -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_STRAFTER -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_REPLACE -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_SUBSTR -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_STRDT -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_STRLANG -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_COALESCE -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_NOW -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_UUID -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_STRUUID -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_YEAR -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_MONTH -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_DAY -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_HOURS -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_MINUTES -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_SECONDS -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_TIMEZONE -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_TZ -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_MD5 -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_SHA1 -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_SHA256 -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_SHA384 -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | Tok_SHA512 -> parse_primary_expr pm (fuel - Prims.int_one) ts
     | uu___1 -> ParseErr "expected '(' or built-in call after FILTER")
and parse_graph_name (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream)
  : SPARQL11_Algebra.pattern_term parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v -> ParseOk ((SPARQL11_Algebra.PT_Var v), (parse_advance ts))
     | Tok_IRI i ->
         let ri = resolve_tok_iri i in
         if RDF_Graph_Executable.is_iri ri
         then ParseOk ((SPARQL11_Algebra.PT_IRI ri), (parse_advance ts))
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
         let ri = resolve_tok_iri i in
         if RDF_Graph_Executable.is_iri ri
         then ParseOk (ri, (parse_advance ts))
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
and parse_data_value (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream)
  :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_UNDEF ->
         ParseOk (FStar_Pervasives_Native.None, (parse_advance ts))
     | Tok_IRI i ->
         let ri = resolve_tok_iri i in
         if RDF_Graph_Executable.is_iri ri
         then
           ParseOk
             ((FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI ri)),
               (parse_advance ts))
         else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
         (match resolve_pname pn pm with
          | FStar_Pervasives_Native.Some iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                ParseOk
                  ((FStar_Pervasives_Native.Some
                      (RDF_Graph_Executable.T_IRI iri)), (parse_advance ts))
              else ParseErr "invalid IRI"
          | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
     | Tok_STRING s ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_HATHAT ->
              let ts'' = parse_advance ts' in
              (match parse_peek ts'' with
               | Tok_IRI dt ->
                   if RDF_Graph_Executable.is_iri dt
                   then
                     (match make_typed_literal s dt with
                      | FStar_Pervasives_Native.Some lit ->
                          ParseOk
                            ((FStar_Pervasives_Native.Some
                                (RDF_Graph_Executable.T_Literal lit)),
                              (parse_advance ts''))
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
                                 ((FStar_Pervasives_Native.Some
                                     (RDF_Graph_Executable.T_Literal lit)),
                                   (parse_advance ts''))
                           | FStar_Pervasives_Native.None ->
                               ParseErr "invalid typed literal")
                        else ParseErr "invalid datatype IRI"
                    | FStar_Pervasives_Native.None ->
                        ParseErr "unresolved prefix")
               | uu___1 -> ParseErr "expected IRI after ^^")
          | Tok_LANGTAG lang ->
              ParseOk
                ((FStar_Pervasives_Native.Some
                    (RDF_Graph_Executable.T_Literal
                       (make_lang_literal s lang))), (parse_advance ts'))
          | uu___1 ->
              ParseOk
                ((FStar_Pervasives_Native.Some
                    (RDF_Graph_Executable.T_Literal (make_plain_literal s))),
                  ts'))
     | Tok_INTEGER n ->
         (match make_typed_literal n
                  "http://www.w3.org/2001/XMLSchema#integer"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk
                ((FStar_Pervasives_Native.Some
                    (RDF_Graph_Executable.T_Literal lit)),
                  (parse_advance ts))
          | FStar_Pervasives_Native.None -> ParseErr "invalid integer")
     | Tok_DECIMAL d ->
         (match make_typed_literal d
                  "http://www.w3.org/2001/XMLSchema#decimal"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk
                ((FStar_Pervasives_Native.Some
                    (RDF_Graph_Executable.T_Literal lit)),
                  (parse_advance ts))
          | FStar_Pervasives_Native.None -> ParseErr "invalid decimal")
     | Tok_DOUBLE d ->
         (match make_typed_literal d
                  "http://www.w3.org/2001/XMLSchema#double"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk
                ((FStar_Pervasives_Native.Some
                    (RDF_Graph_Executable.T_Literal lit)),
                  (parse_advance ts))
          | FStar_Pervasives_Native.None -> ParseErr "invalid double")
     | Tok_TRUE ->
         (match make_typed_literal "true"
                  "http://www.w3.org/2001/XMLSchema#boolean"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk
                ((FStar_Pervasives_Native.Some
                    (RDF_Graph_Executable.T_Literal lit)),
                  (parse_advance ts))
          | FStar_Pervasives_Native.None -> ParseErr "invalid boolean")
     | Tok_FALSE ->
         (match make_typed_literal "false"
                  "http://www.w3.org/2001/XMLSchema#boolean"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk
                ((FStar_Pervasives_Native.Some
                    (RDF_Graph_Executable.T_Literal lit)),
                  (parse_advance ts))
          | FStar_Pervasives_Native.None -> ParseErr "invalid boolean")
     | uu___1 -> ParseErr "expected data value or UNDEF")
and parse_values_row (pm : prefix_map) (fuel : Prims.nat)
  (n_vars : Prims.nat) (ts : token_stream) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list
    parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_expect Tok_LPAREN ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((), ts') ->
         parse_values_row_items pm (fuel - Prims.int_one) n_vars [] ts')
and parse_values_row_items (pm : prefix_map) (fuel : Prims.nat)
  (remaining : Prims.nat)
  (acc :
    RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list)
  (ts : token_stream) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list
    parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_RPAREN ->
         ParseOk ((FStar_List_Tot_Base.rev acc), (parse_advance ts))
     | uu___1 ->
         (match parse_data_value pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (v, ts') ->
              parse_values_row_items pm (fuel - Prims.int_one)
                (if remaining > Prims.int_zero
                 then remaining - Prims.int_one
                 else Prims.int_zero) (v :: acc) ts'))
and parse_values_rows (pm : prefix_map) (fuel : Prims.nat)
  (n_vars : Prims.nat)
  (acc :
    RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list
      Prims.list)
  (ts : token_stream) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list
    Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_LPAREN ->
         (match parse_values_row pm (fuel - Prims.int_one) n_vars ts with
          | ParseErr m -> ParseErr m
          | ParseOk (row, ts') ->
              parse_values_rows pm (fuel - Prims.int_one) n_vars (row :: acc)
                ts')
     | uu___1 -> ParseOk ((FStar_List_Tot_Base.rev acc), ts))
and parse_values_vars (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.var_name Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.var_name Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_VAR v ->
         parse_values_vars (fuel - Prims.int_one) (v :: acc)
           (parse_advance ts)
     | uu___1 -> ParseOk ((FStar_List_Tot_Base.rev acc), ts))
and parse_values_clause (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.group_graph_pattern parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v ->
         let ts' = parse_advance ts in
         (match parse_expect Tok_LBRACE ts' with
          | ParseErr m -> ParseErr m
          | ParseOk ((), ts'') ->
              (match parse_single_var_values pm (fuel - Prims.int_one) []
                       ts''
               with
               | ParseErr m -> ParseErr m
               | ParseOk (vals, ts''') ->
                   (match parse_expect Tok_RBRACE ts''' with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts4) ->
                        let rows =
                          FStar_List_Tot_Base.map (fun v1 -> [v1]) vals in
                        ParseOk
                          ((SPARQL11_Algebra.GP_Values ([v], rows)), ts4))))
     | Tok_LPAREN ->
         let ts' = parse_advance ts in
         (match parse_values_vars (fuel - Prims.int_one) [] ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (vars, ts'') ->
              (match parse_expect Tok_RPAREN ts'' with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts''') ->
                   (match parse_expect Tok_LBRACE ts''' with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts4) ->
                        (match parse_values_rows pm (fuel - Prims.int_one)
                                 (FStar_List_Tot_Base.length vars) [] ts4
                         with
                         | ParseErr m -> ParseErr m
                         | ParseOk (rows, ts5) ->
                             (match parse_expect Tok_RBRACE ts5 with
                              | ParseErr m -> ParseErr m
                              | ParseOk ((), ts6) ->
                                  let vars_len =
                                    FStar_List_Tot_Base.length vars in
                                  let check_row row =
                                    (FStar_List_Tot_Base.length row) =
                                      vars_len in
                                  if
                                    FStar_List_Tot_Base.for_all check_row
                                      rows
                                  then
                                    ParseOk
                                      ((SPARQL11_Algebra.GP_Values
                                          (vars, rows)), ts6)
                                  else
                                    ParseErr
                                      "VALUES row has wrong number of terms")))))
     | uu___1 -> ParseErr "expected variable or '(' after VALUES")
and parse_single_var_values (pm : prefix_map) (fuel : Prims.nat)
  (acc :
    RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list)
  (ts : token_stream) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list
    parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_RBRACE -> ParseOk ((FStar_List_Tot_Base.rev acc), ts)
     | uu___1 ->
         (match parse_data_value pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (v, ts') ->
              parse_single_var_values pm (fuel - Prims.int_one) (v :: acc)
                ts'))
and pattern_term_to_subject (pt : SPARQL11_Algebra.pattern_term) :
  SPARQL11_Algebra.pattern_subject FStar_Pervasives_Native.option=
  match pt with
  | SPARQL11_Algebra.PT_Var v ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_Var v)
  | SPARQL11_Algebra.PT_IRI i ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_IRI i)
  | SPARQL11_Algebra.PT_BNode b ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.PS_BNode b)
  | SPARQL11_Algebra.PT_Literal uu___ -> FStar_Pervasives_Native.None
and parse_subject_with_extras (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) :
  (SPARQL11_Algebra.pattern_subject * SPARQL11_Algebra.group_graph_pattern *
    Prims.bool) parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v ->
         ParseOk
           (((SPARQL11_Algebra.PS_Var v), SPARQL11_Algebra.GP_Empty, false),
             (parse_advance ts))
     | Tok_IRI i ->
         let ri = resolve_tok_iri i in
         if RDF_Graph_Executable.is_iri ri
         then
           ParseOk
             (((SPARQL11_Algebra.PS_IRI ri), SPARQL11_Algebra.GP_Empty, false),
               (parse_advance ts))
         else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
         (match resolve_pname pn pm with
          | FStar_Pervasives_Native.Some iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                ParseOk
                  (((SPARQL11_Algebra.PS_IRI iri), SPARQL11_Algebra.GP_Empty,
                     false), (parse_advance ts))
              else ParseErr "invalid IRI"
          | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
     | Tok_BNODE b ->
         ParseOk
           (((SPARQL11_Algebra.PS_BNode b), SPARQL11_Algebra.GP_Empty, false),
             (parse_advance ts))
     | Tok_LBRACKET ->
         let bnode_id = fresh_bnode_id ts in
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_RBRACKET ->
              ParseOk
                (((SPARQL11_Algebra.PS_BNode bnode_id),
                   SPARQL11_Algebra.GP_Empty, false), (parse_advance ts'))
          | uu___1 ->
              let bnode_subj = SPARQL11_Algebra.PS_BNode bnode_id in
              (match parse_pred_obj_list pm (fuel - Prims.int_one) bnode_subj
                       SPARQL11_Algebra.GP_Empty ts'
               with
               | ParseErr m -> ParseErr m
               | ParseOk (extra_triples, ts'') ->
                   (match parse_expect Tok_RBRACKET ts'' with
                    | ParseErr uu___2 ->
                        ParseErr
                          "expected ']' after blank node property list"
                    | ParseOk ((), ts''') ->
                        ParseOk
                          (((SPARQL11_Algebra.PS_BNode bnode_id),
                             extra_triples, false), ts'''))))
     | Tok_LPAREN ->
         (match parse_collection pm (fuel - Prims.int_one) (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk ((pt, extras), ts') ->
              (match pattern_term_to_subject pt with
               | FStar_Pervasives_Native.Some subj ->
                   ParseOk ((subj, extras, false), ts')
               | FStar_Pervasives_Native.None ->
                   ParseErr "collection cannot be used as subject"))
     | uu___1 -> ParseErr "expected subject")
and parse_subject (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.pattern_subject parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_subject_with_extras pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((subj, uu___1, uu___2), ts') -> ParseOk (subj, ts'))
and parse_path_alternative (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.property_path parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_path_sequence pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (p1, ts') ->
         parse_path_alt_rest pm (fuel - Prims.int_one) p1 ts')
and parse_path_alt_rest (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.property_path) (ts : token_stream) :
  SPARQL11_Algebra.property_path parse_result=
  if fuel = Prims.int_zero
  then ParseOk (acc, ts)
  else
    (match parse_peek ts with
     | Tok_PIPE ->
         (match parse_path_sequence pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (p2, ts') ->
              parse_path_alt_rest pm (fuel - Prims.int_one)
                (SPARQL11_Algebra.PP_Alternative (acc, p2)) ts')
     | uu___1 -> ParseOk (acc, ts))
and parse_path_sequence (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.property_path parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_path_elt_or_inverse pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (p1, ts') ->
         parse_path_seq_rest pm (fuel - Prims.int_one) p1 ts')
and parse_path_seq_rest (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.property_path) (ts : token_stream) :
  SPARQL11_Algebra.property_path parse_result=
  if fuel = Prims.int_zero
  then ParseOk (acc, ts)
  else
    (match parse_peek ts with
     | Tok_SLASH ->
         (match parse_path_elt_or_inverse pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (p2, ts') ->
              parse_path_seq_rest pm (fuel - Prims.int_one)
                (SPARQL11_Algebra.PP_Sequence (acc, p2)) ts')
     | uu___1 -> ParseOk (acc, ts))
and parse_path_elt_or_inverse (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.property_path parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_CARET ->
         (match parse_path_elt pm (fuel - Prims.int_one) (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (p, ts') ->
              ParseOk ((SPARQL11_Algebra.PP_Inverse p), ts'))
     | uu___1 -> parse_path_elt pm (fuel - Prims.int_one) ts)
and parse_path_elt (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.property_path parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_path_primary pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (p, ts') ->
         (match parse_peek ts' with
          | Tok_STAR ->
              ParseOk
                ((SPARQL11_Algebra.PP_ZeroOrMore p), (parse_advance ts'))
          | Tok_PLUS ->
              ParseOk
                ((SPARQL11_Algebra.PP_OneOrMore p), (parse_advance ts'))
          | Tok_QMARK ->
              ParseOk
                ((SPARQL11_Algebra.PP_ZeroOrOne p), (parse_advance ts'))
          | uu___1 -> ParseOk (p, ts')))
and parse_path_primary (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.property_path parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_IRI i ->
         let ri = resolve_tok_iri i in
         if RDF_Graph_Executable.is_iri ri
         then ParseOk ((SPARQL11_Algebra.PP_IRI ri), (parse_advance ts))
         else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
         (match resolve_pname pn pm with
          | FStar_Pervasives_Native.Some iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                ParseOk ((SPARQL11_Algebra.PP_IRI iri), (parse_advance ts))
              else ParseErr "invalid IRI"
          | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
     | Tok_A ->
         ParseOk
           ((SPARQL11_Algebra.PP_IRI rdf_type_iri_str), (parse_advance ts))
     | Tok_BANG ->
         parse_path_negated pm (fuel - Prims.int_one) (parse_advance ts)
     | Tok_LPAREN ->
         (match parse_path_alternative pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (p, ts') ->
              (match parse_expect Tok_RPAREN ts' with
               | ParseErr uu___1 -> ParseErr "expected ')' after path"
               | ParseOk ((), ts'') -> ParseOk (p, ts'')))
     | uu___1 -> ParseErr "expected path primary")
and parse_path_negated (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.property_path parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_LPAREN ->
         (match parse_path_one_in_set_list pm (fuel - Prims.int_one)
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (ps, ts') ->
              (match parse_expect Tok_RPAREN ts' with
               | ParseErr uu___1 ->
                   ParseErr "expected ')' in negated path set"
               | ParseOk ((), ts'') ->
                   ParseOk ((SPARQL11_Algebra.PP_NegatedSet ps), ts'')))
     | uu___1 ->
         (match parse_path_one_in_set pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (p, ts') ->
              ParseOk ((SPARQL11_Algebra.PP_NegatedSet [p]), ts')))
and parse_path_one_in_set (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.property_path parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_IRI i ->
         let ri = resolve_tok_iri i in
         if RDF_Graph_Executable.is_iri ri
         then ParseOk ((SPARQL11_Algebra.PP_IRI ri), (parse_advance ts))
         else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
         (match resolve_pname pn pm with
          | FStar_Pervasives_Native.Some iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                ParseOk ((SPARQL11_Algebra.PP_IRI iri), (parse_advance ts))
              else ParseErr "invalid IRI"
          | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
     | Tok_A ->
         ParseOk
           ((SPARQL11_Algebra.PP_IRI rdf_type_iri_str), (parse_advance ts))
     | Tok_CARET ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_IRI i ->
              let ri = resolve_tok_iri i in
              if RDF_Graph_Executable.is_iri ri
              then
                ParseOk
                  ((SPARQL11_Algebra.PP_Inverse (SPARQL11_Algebra.PP_IRI ri)),
                    (parse_advance ts'))
              else ParseErr "invalid IRI"
          | Tok_PNAME pn ->
              (match resolve_pname pn pm with
               | FStar_Pervasives_Native.Some iri ->
                   if RDF_Graph_Executable.is_iri iri
                   then
                     ParseOk
                       ((SPARQL11_Algebra.PP_Inverse
                           (SPARQL11_Algebra.PP_IRI iri)),
                         (parse_advance ts'))
                   else ParseErr "invalid IRI"
               | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
          | Tok_A ->
              ParseOk
                ((SPARQL11_Algebra.PP_Inverse
                    (SPARQL11_Algebra.PP_IRI rdf_type_iri_str)),
                  (parse_advance ts'))
          | uu___1 -> ParseErr "expected IRI or 'a' after ^ in negated set")
     | uu___1 -> ParseErr "expected path element in negated set")
and parse_path_one_in_set_list (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) :
  SPARQL11_Algebra.property_path Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ([], ts)
  else
    (match parse_path_one_in_set pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (p, ts') ->
         (match parse_peek ts' with
          | Tok_PIPE ->
              (match parse_path_one_in_set_list pm (fuel - Prims.int_one)
                       (parse_advance ts')
               with
               | ParseErr m -> ParseErr m
               | ParseOk (ps, ts'') -> ParseOk ((p :: ps), ts''))
          | uu___1 -> ParseOk ([p], ts')))
and parse_verb (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  verb_or_path parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v ->
         ParseOk ((VSimple (SPARQL11_Algebra.PT_Var v)), (parse_advance ts))
     | uu___1 ->
         (match parse_path_alternative pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (pp, ts') ->
              (match pp with
               | SPARQL11_Algebra.PP_IRI iri ->
                   ParseOk ((VSimple (SPARQL11_Algebra.PT_IRI iri)), ts')
               | uu___2 -> ParseOk ((VPath pp), ts'))))
and fresh_bnode_id (ts : token_stream) : Prims.string=
  Prims.strcat "_:bnode_"
    (Prims.string_of_int (FStar_List_Tot_Base.length ts))
and parse_signed_numeric_literal_pt (sign : Prims.string) (ts : token_stream)
  : SPARQL11_Algebra.pattern_term parse_result=
  match parse_peek ts with
  | Tok_INTEGER n ->
      (match make_typed_literal (Prims.strcat sign n)
               "http://www.w3.org/2001/XMLSchema#integer"
       with
       | FStar_Pervasives_Native.Some lit ->
           ParseOk ((SPARQL11_Algebra.PT_Literal lit), (parse_advance ts))
       | FStar_Pervasives_Native.None -> ParseErr "invalid integer literal")
  | Tok_DECIMAL d ->
      (match make_typed_literal (Prims.strcat sign d)
               "http://www.w3.org/2001/XMLSchema#decimal"
       with
       | FStar_Pervasives_Native.Some lit ->
           ParseOk ((SPARQL11_Algebra.PT_Literal lit), (parse_advance ts))
       | FStar_Pervasives_Native.None -> ParseErr "invalid decimal literal")
  | Tok_DOUBLE d ->
      (match make_typed_literal (Prims.strcat sign d)
               "http://www.w3.org/2001/XMLSchema#double"
       with
       | FStar_Pervasives_Native.Some lit ->
           ParseOk ((SPARQL11_Algebra.PT_Literal lit), (parse_advance ts))
       | FStar_Pervasives_Native.None -> ParseErr "invalid double literal")
  | uu___ -> ParseErr "expected signed numeric literal"
and parse_object_with_extras (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) :
  (SPARQL11_Algebra.pattern_term * SPARQL11_Algebra.group_graph_pattern)
    parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v ->
         ParseOk
           (((SPARQL11_Algebra.PT_Var v), SPARQL11_Algebra.GP_Empty),
             (parse_advance ts))
     | Tok_IRI i ->
         let ri = resolve_tok_iri i in
         if RDF_Graph_Executable.is_iri ri
         then
           ParseOk
             (((SPARQL11_Algebra.PT_IRI ri), SPARQL11_Algebra.GP_Empty),
               (parse_advance ts))
         else ParseErr "invalid IRI"
     | Tok_PNAME pn ->
         (match resolve_pname pn pm with
          | FStar_Pervasives_Native.Some iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                ParseOk
                  (((SPARQL11_Algebra.PT_IRI iri), SPARQL11_Algebra.GP_Empty),
                    (parse_advance ts))
              else ParseErr "invalid IRI"
          | FStar_Pervasives_Native.None -> ParseErr "unresolved prefix")
     | Tok_BNODE b ->
         ParseOk
           (((SPARQL11_Algebra.PT_BNode b), SPARQL11_Algebra.GP_Empty),
             (parse_advance ts))
     | Tok_STRING s ->
         (match parse_rdf_literal_pt pm (fuel - Prims.int_one) s
                  (parse_advance ts)
          with
          | ParseErr m -> ParseErr m
          | ParseOk (pt, ts') ->
              ParseOk ((pt, SPARQL11_Algebra.GP_Empty), ts'))
     | Tok_INTEGER n ->
         (match make_typed_literal n
                  "http://www.w3.org/2001/XMLSchema#integer"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk
                (((SPARQL11_Algebra.PT_Literal lit),
                   SPARQL11_Algebra.GP_Empty), (parse_advance ts))
          | FStar_Pervasives_Native.None ->
              ParseErr "invalid integer literal")
     | Tok_DECIMAL d ->
         (match make_typed_literal d
                  "http://www.w3.org/2001/XMLSchema#decimal"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk
                (((SPARQL11_Algebra.PT_Literal lit),
                   SPARQL11_Algebra.GP_Empty), (parse_advance ts))
          | FStar_Pervasives_Native.None ->
              ParseErr "invalid decimal literal")
     | Tok_DOUBLE d ->
         (match make_typed_literal d
                  "http://www.w3.org/2001/XMLSchema#double"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk
                (((SPARQL11_Algebra.PT_Literal lit),
                   SPARQL11_Algebra.GP_Empty), (parse_advance ts))
          | FStar_Pervasives_Native.None -> ParseErr "invalid double literal")
     | Tok_TRUE ->
         (match make_typed_literal "true"
                  "http://www.w3.org/2001/XMLSchema#boolean"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk
                (((SPARQL11_Algebra.PT_Literal lit),
                   SPARQL11_Algebra.GP_Empty), (parse_advance ts))
          | FStar_Pervasives_Native.None ->
              ParseErr "invalid boolean literal")
     | Tok_FALSE ->
         (match make_typed_literal "false"
                  "http://www.w3.org/2001/XMLSchema#boolean"
          with
          | FStar_Pervasives_Native.Some lit ->
              ParseOk
                (((SPARQL11_Algebra.PT_Literal lit),
                   SPARQL11_Algebra.GP_Empty), (parse_advance ts))
          | FStar_Pervasives_Native.None ->
              ParseErr "invalid boolean literal")
     | Tok_PLUS ->
         (match parse_signed_numeric_literal_pt "+" (parse_advance ts) with
          | ParseOk (pt, ts') ->
              ParseOk ((pt, SPARQL11_Algebra.GP_Empty), ts')
          | ParseErr m -> ParseErr m)
     | Tok_MINUS_OP ->
         (match parse_signed_numeric_literal_pt "-" (parse_advance ts) with
          | ParseOk (pt, ts') ->
              ParseOk ((pt, SPARQL11_Algebra.GP_Empty), ts')
          | ParseErr m -> ParseErr m)
     | Tok_A ->
         ParseOk
           (((SPARQL11_Algebra.PT_IRI rdf_type_iri_str),
              SPARQL11_Algebra.GP_Empty), (parse_advance ts))
     | Tok_LBRACKET ->
         let bnode_id = fresh_bnode_id ts in
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_RBRACKET ->
              ParseOk
                (((SPARQL11_Algebra.PT_BNode bnode_id),
                   SPARQL11_Algebra.GP_Empty), (parse_advance ts'))
          | uu___1 ->
              let bnode_subj = SPARQL11_Algebra.PS_BNode bnode_id in
              (match parse_pred_obj_list pm (fuel - Prims.int_one) bnode_subj
                       SPARQL11_Algebra.GP_Empty ts'
               with
               | ParseErr m -> ParseErr m
               | ParseOk (extra_triples, ts'') ->
                   (match parse_expect Tok_RBRACKET ts'' with
                    | ParseErr uu___2 ->
                        ParseErr
                          "expected ']' after blank node property list"
                    | ParseOk ((), ts''') ->
                        ParseOk
                          (((SPARQL11_Algebra.PT_BNode bnode_id),
                             extra_triples), ts'''))))
     | Tok_LPAREN ->
         parse_collection pm (fuel - Prims.int_one) (parse_advance ts)
     | uu___1 -> ParseErr "expected object")
and parse_collection (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream)
  :
  (SPARQL11_Algebra.pattern_term * SPARQL11_Algebra.group_graph_pattern)
    parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_RPAREN ->
         ParseOk
           (((SPARQL11_Algebra.PT_IRI
                "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"),
              SPARQL11_Algebra.GP_Empty), (parse_advance ts))
     | uu___1 ->
         (match parse_object_with_extras pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk ((item, item_extras), ts') ->
              let bnode_id = fresh_bnode_id ts in
              let bnode_subj = SPARQL11_Algebra.PS_BNode bnode_id in
              (match parse_collection pm (fuel - Prims.int_one) ts' with
               | ParseErr m -> ParseErr m
               | ParseOk ((rest_term, rest_extras), ts'') ->
                   let first_triple =
                     {
                       SPARQL11_Algebra.tp_s = bnode_subj;
                       SPARQL11_Algebra.tp_p =
                         (SPARQL11_Algebra.PT_IRI
                            "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
                       SPARQL11_Algebra.tp_o = item
                     } in
                   let rest_triple =
                     {
                       SPARQL11_Algebra.tp_s = bnode_subj;
                       SPARQL11_Algebra.tp_p =
                         (SPARQL11_Algebra.PT_IRI
                            "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
                       SPARQL11_Algebra.tp_o = rest_term
                     } in
                   let triples =
                     SPARQL11_Algebra.GP_BGP [first_triple; rest_triple] in
                   let all_extras =
                     ggp_join (ggp_join triples item_extras) rest_extras in
                   ParseOk
                     (((SPARQL11_Algebra.PT_BNode bnode_id), all_extras),
                       ts''))))
and parse_object (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream) :
  SPARQL11_Algebra.pattern_term parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_object_with_extras pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((pt, uu___1), ts') -> ParseOk (pt, ts'))
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
              let dt = resolve_tok_iri dt in
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
and ggp_join (a : SPARQL11_Algebra.group_graph_pattern)
  (b : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.group_graph_pattern=
  match a with
  | SPARQL11_Algebra.GP_Empty -> b
  | uu___ ->
      (match b with
       | SPARQL11_Algebra.GP_Empty -> a
       | uu___1 -> SPARQL11_Algebra.GP_Join (a, b))
and ggp_add_triple (acc : SPARQL11_Algebra.group_graph_pattern)
  (tp : SPARQL11_Algebra.triple_pattern) :
  SPARQL11_Algebra.group_graph_pattern=
  match acc with
  | SPARQL11_Algebra.GP_BGP ts ->
      SPARQL11_Algebra.GP_BGP (FStar_List_Tot_Base.op_At ts [tp])
  | SPARQL11_Algebra.GP_Empty -> SPARQL11_Algebra.GP_BGP [tp]
  | uu___ -> SPARQL11_Algebra.GP_Join (acc, (SPARQL11_Algebra.GP_BGP [tp]))
and ggp_add_pp (acc : SPARQL11_Algebra.group_graph_pattern)
  (s : SPARQL11_Algebra.pattern_subject)
  (pp : SPARQL11_Algebra.property_path) (o : SPARQL11_Algebra.pattern_term) :
  SPARQL11_Algebra.group_graph_pattern=
  ggp_join acc (SPARQL11_Algebra.GP_PropertyPath (s, pp, o))
and parse_object_list_simple (pm : prefix_map) (fuel : Prims.nat)
  (subj : SPARQL11_Algebra.pattern_subject)
  (pred : SPARQL11_Algebra.pattern_term)
  (acc : SPARQL11_Algebra.group_graph_pattern) (ts : token_stream) :
  SPARQL11_Algebra.group_graph_pattern parse_result=
  if fuel = Prims.int_zero
  then ParseOk (acc, ts)
  else
    (match parse_object_with_extras pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((obj, extras), ts') ->
         let acc' =
           ggp_add_triple acc
             {
               SPARQL11_Algebra.tp_s = subj;
               SPARQL11_Algebra.tp_p = pred;
               SPARQL11_Algebra.tp_o = obj
             } in
         let acc'1 = ggp_join acc' extras in
         (match parse_peek ts' with
          | Tok_COMMA ->
              parse_object_list_simple pm (fuel - Prims.int_one) subj pred
                acc'1 (parse_advance ts')
          | uu___1 -> ParseOk (acc'1, ts')))
and parse_object_list_path (pm : prefix_map) (fuel : Prims.nat)
  (subj : SPARQL11_Algebra.pattern_subject)
  (pp : SPARQL11_Algebra.property_path)
  (acc : SPARQL11_Algebra.group_graph_pattern) (ts : token_stream) :
  SPARQL11_Algebra.group_graph_pattern parse_result=
  if fuel = Prims.int_zero
  then ParseOk (acc, ts)
  else
    (match parse_object_with_extras pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk ((obj, extras), ts') ->
         let acc' = ggp_add_pp acc subj pp obj in
         let acc'1 = ggp_join acc' extras in
         (match parse_peek ts' with
          | Tok_COMMA ->
              parse_object_list_path pm (fuel - Prims.int_one) subj pp acc'1
                (parse_advance ts')
          | uu___1 -> ParseOk (acc'1, ts')))
and parse_pred_obj_list (pm : prefix_map) (fuel : Prims.nat)
  (subj : SPARQL11_Algebra.pattern_subject)
  (acc : SPARQL11_Algebra.group_graph_pattern) (ts : token_stream) :
  SPARQL11_Algebra.group_graph_pattern parse_result=
  if fuel = Prims.int_zero
  then ParseOk (acc, ts)
  else
    (match parse_verb pm (fuel - Prims.int_one) ts with
     | ParseErr m -> ParseErr m
     | ParseOk (verb, ts') ->
         let r =
           match verb with
           | VSimple pred ->
               parse_object_list_simple pm (fuel - Prims.int_one) subj pred
                 acc ts'
           | VPath pp ->
               parse_object_list_path pm (fuel - Prims.int_one) subj pp acc
                 ts' in
         (match r with
          | ParseErr m -> ParseErr m
          | ParseOk (acc', ts'') ->
              (match parse_peek ts'' with
               | Tok_SEMI ->
                   let ts''' = parse_advance ts'' in
                   (match parse_peek ts''' with
                    | Tok_DOT -> ParseOk (acc', ts''')
                    | Tok_RBRACE -> ParseOk (acc', ts''')
                    | Tok_OPTIONAL -> ParseOk (acc', ts''')
                    | Tok_MINUS_KW -> ParseOk (acc', ts''')
                    | Tok_FILTER -> ParseOk (acc', ts''')
                    | Tok_BIND -> ParseOk (acc', ts''')
                    | Tok_GRAPH -> ParseOk (acc', ts''')
                    | Tok_SERVICE -> ParseOk (acc', ts''')
                    | Tok_VALUES -> ParseOk (acc', ts''')
                    | Tok_UNION -> ParseOk (acc', ts''')
                    | Tok_LBRACE -> ParseOk (acc', ts''')
                    | Tok_RBRACKET -> ParseOk (acc', ts''')
                    | Tok_EOF -> ParseOk (acc', ts''')
                    | uu___1 ->
                        parse_pred_obj_list pm (fuel - Prims.int_one) subj
                          acc' ts''')
               | uu___1 -> ParseOk (acc', ts''))))
and parse_triples_block (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.group_graph_pattern) (ts : token_stream) :
  SPARQL11_Algebra.group_graph_pattern parse_result=
  if fuel = Prims.int_zero
  then ParseOk (acc, ts)
  else
    (match parse_subject_with_extras pm (fuel - Prims.int_one) ts with
     | ParseErr m ->
         (match acc with
          | SPARQL11_Algebra.GP_Empty -> ParseErr m
          | uu___1 -> ParseOk (acc, ts))
     | ParseOk ((subj, subj_extras, pred_obj_optional), ts') ->
         let acc0 = ggp_join acc subj_extras in
         let r =
           match parse_pred_obj_list pm (fuel - Prims.int_one) subj acc0 ts'
           with
           | ParseOk (acc', ts'') -> ParseOk (acc', ts'')
           | ParseErr uu___1 ->
               if pred_obj_optional
               then ParseOk (acc0, ts')
               else ParseErr "expected predicate-object list" in
         (match r with
          | ParseErr m -> ParseErr m
          | ParseOk (acc', ts'') ->
              (match parse_peek ts'' with
               | Tok_DOT ->
                   let ts''' = parse_advance ts'' in
                   (match parse_peek ts''' with
                    | Tok_VAR uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_IRI uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_PNAME uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_BNODE uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_LBRACKET ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_LPAREN ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_A ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_INTEGER uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_DECIMAL uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_DOUBLE uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_STRING uu___1 ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_TRUE ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | Tok_FALSE ->
                        parse_triples_block pm (fuel - Prims.int_one) acc'
                          ts'''
                    | uu___1 -> ParseOk (acc', ts'''))
               | Tok_VAR uu___1 -> ParseErr "expected dot between triples"
               | Tok_IRI uu___1 -> ParseErr "expected dot between triples"
               | Tok_PNAME uu___1 -> ParseErr "expected dot between triples"
               | Tok_BNODE uu___1 -> ParseErr "expected dot between triples"
               | Tok_LBRACKET -> ParseErr "expected dot between triples"
               | Tok_LPAREN -> ParseErr "expected dot between triples"
               | Tok_A -> ParseErr "expected dot between triples"
               | Tok_INTEGER uu___1 ->
                   ParseErr "expected dot between triples"
               | Tok_DECIMAL uu___1 ->
                   ParseErr "expected dot between triples"
               | Tok_DOUBLE uu___1 -> ParseErr "expected dot between triples"
               | Tok_STRING uu___1 -> ParseErr "expected dot between triples"
               | Tok_TRUE -> ParseErr "expected dot between triples"
               | Tok_FALSE -> ParseErr "expected dot between triples"
               | uu___1 -> ParseOk (acc', ts''))))
and parse_select_query (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.query parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (let r =
       parse_prologue pm FStar_Pervasives_Native.None (fuel - Prims.int_one)
         ts in
     match r with
     | ParseErr m -> ParseErr m
     | ParseOk ((pm', base), ts') ->
         let ts'' = resolve_relative_iri_tokens base ts' in
         (match parse_peek ts'' with
          | Tok_SELECT ->
              parse_select_body pm' (fuel - Prims.int_one) base ts''
          | Tok_ASK -> parse_ask_body pm' (fuel - Prims.int_one) base ts''
          | Tok_CONSTRUCT ->
              parse_construct_body pm' (fuel - Prims.int_one) base ts''
          | Tok_DESCRIBE -> ParseErr "unsupported: DESCRIBE queries"
          | uu___1 -> ParseErr "expected SELECT, ASK, CONSTRUCT, or DESCRIBE"))
and parse_prologue (pm : prefix_map)
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (fuel : Prims.nat) (ts : token_stream) :
  (prefix_map * RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
    parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((pm, base), ts)
  else
    (match parse_peek ts with
     | Tok_PREFIX ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_PNAME pn ->
              let uu___1 = split_pname pn in
              (match uu___1 with
               | (prefix, local) ->
                   if (FStar_String.strlen local) > Prims.int_zero
                   then
                     ParseErr
                       "invalid PREFIX name (must be prefix: with no local part)"
                   else
                     (let ts'' = parse_advance ts' in
                      match parse_peek ts'' with
                      | Tok_IRI iri ->
                          (match if RDF_Graph_Executable.is_iri iri
                                 then FStar_Pervasives_Native.Some iri
                                 else
                                   SPARQL11_Algebra.resolve_query_iri base
                                     iri
                           with
                           | FStar_Pervasives_Native.Some abs ->
                               parse_prologue ((prefix, abs) :: pm) base
                                 (fuel - Prims.int_one) (parse_advance ts'')
                           | FStar_Pervasives_Native.None ->
                               ParseErr "invalid prefix IRI")
                      | uu___3 -> ParseErr "expected IRI after PREFIX name"))
          | uu___1 -> ParseErr "expected prefix name after PREFIX")
     | Tok_BASE ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_IRI iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                parse_prologue pm (FStar_Pervasives_Native.Some iri)
                  (fuel - Prims.int_one) (parse_advance ts')
              else ParseErr "invalid BASE IRI"
          | uu___1 -> ParseErr "expected IRI after BASE")
     | uu___1 -> ParseOk ((pm, base), ts))
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
                         | ParseOk ((modifier, gb, hv), ts6) ->
                             if
                               (SPARQL11_Algebra.uu___is_Select_All sel) &&
                                 (FStar_Pervasives_Native.uu___is_Some gb)
                             then
                               ParseErr "SELECT * not allowed with GROUP BY"
                             else
                               if
                                 (FStar_Pervasives_Native.uu___is_Some gb) &&
                                   ((let gcs =
                                       FStar_Pervasives_Native.__proj__Some__item__v
                                         gb in
                                     let is_grouped v =
                                       Prims.op_Negation
                                         (FStar_List_Tot_Base.for_all
                                            (fun gc ->
                                               match gc with
                                               | SPARQL11_Algebra.GC_Var gv
                                                   ->
                                                   Prims.op_Negation
                                                     (streq gv v)
                                               | SPARQL11_Algebra.GC_Expr
                                                   (uu___3,
                                                    FStar_Pervasives_Native.Some
                                                    gv)
                                                   ->
                                                   Prims.op_Negation
                                                     (streq gv v)
                                               | uu___3 -> true) gcs) in
                                     match sel with
                                     | SPARQL11_Algebra.Select_Vars items ->
                                         Prims.op_Negation
                                           (FStar_List_Tot_Base.for_all
                                              (fun item ->
                                                 match item with
                                                 | SPARQL11_Algebra.SI_Var v
                                                     -> is_grouped v
                                                 | SPARQL11_Algebra.SI_Expr
                                                     (e, uu___3) ->
                                                     Prims.op_Negation
                                                       (SPARQL11_Algebra.expr_has_ungrouped_var
                                                          is_grouped e))
                                              items)
                                     | uu___3 -> false))
                               then
                                 ParseErr
                                   "SELECT projects ungrouped variable"
                               else
                                 if
                                   (FStar_Pervasives_Native.uu___is_None gb)
                                     &&
                                     ((match sel with
                                       | SPARQL11_Algebra.Select_Vars items
                                           ->
                                           let has_agg =
                                             Prims.op_Negation
                                               (FStar_List_Tot_Base.for_all
                                                  (fun item ->
                                                     match item with
                                                     | SPARQL11_Algebra.SI_Expr
                                                         (SPARQL11_Algebra.E_Aggregate
                                                          (uu___4, uu___5,
                                                           uu___6),
                                                          uu___7)
                                                         -> false
                                                     | uu___4 -> true) items) in
                                           let has_ungrouped =
                                             Prims.op_Negation
                                               (FStar_List_Tot_Base.for_all
                                                  (fun item ->
                                                     match item with
                                                     | SPARQL11_Algebra.SI_Var
                                                         uu___4 -> false
                                                     | SPARQL11_Algebra.SI_Expr
                                                         (e, uu___4) ->
                                                         Prims.op_Negation
                                                           (SPARQL11_Algebra.expr_has_ungrouped_var
                                                              (fun uu___5 ->
                                                                 false) e))
                                                  items) in
                                           has_agg && has_ungrouped
                                       | uu___4 -> false))
                                 then
                                   ParseErr
                                     "SELECT projects ungrouped variable"
                                 else
                                   if
                                     (match sel with
                                      | SPARQL11_Algebra.Select_Vars items ->
                                          Prims.op_Negation
                                            (FStar_List_Tot_Base.for_all
                                               (fun item ->
                                                  match item with
                                                  | SPARQL11_Algebra.SI_Expr
                                                      (uu___5, v) ->
                                                      Prims.op_Negation
                                                        (SPARQL11_Algebra.ggp_has_var
                                                           v pattern)
                                                  | uu___5 -> true) items)
                                      | uu___5 -> false)
                                   then
                                     ParseErr
                                       "SELECT expression aliases variable already in scope"
                                   else
                                     (let uu___6 =
                                        match parse_peek ts6 with
                                        | Tok_VALUES ->
                                            (match parse_values_clause pm
                                                     (fuel - Prims.int_one)
                                                     (parse_advance ts6)
                                             with
                                             | ParseOk
                                                 (SPARQL11_Algebra.GP_Values
                                                  (vars, rows), ts'1)
                                                 ->
                                                 ((FStar_Pervasives_Native.Some
                                                     (vars, rows)), ts'1)
                                             | uu___7 ->
                                                 (FStar_Pervasives_Native.None,
                                                   ts6))
                                        | uu___7 ->
                                            (FStar_Pervasives_Native.None,
                                              ts6) in
                                      match uu___6 with
                                      | (vals, ts7) ->
                                          ParseOk
                                            ({
                                               SPARQL11_Algebra.q_base = base;
                                               SPARQL11_Algebra.q_prefixes =
                                                 pm;
                                               SPARQL11_Algebra.q_form =
                                                 (SPARQL11_Algebra.QF_Select
                                                    sel);
                                               SPARQL11_Algebra.q_dataset =
                                                 ds;
                                               SPARQL11_Algebra.q_pattern =
                                                 ((match vals with
                                                   | FStar_Pervasives_Native.Some
                                                       (vars, rows) ->
                                                       ggp_join pattern
                                                         (SPARQL11_Algebra.GP_Values
                                                            (vars, rows))
                                                   | FStar_Pervasives_Native.None
                                                       -> pattern));
                                               SPARQL11_Algebra.q_group_by =
                                                 gb;
                                               SPARQL11_Algebra.q_having = hv;
                                               SPARQL11_Algebra.q_modifier =
                                                 {
                                                   SPARQL11_Algebra.sm_order_by
                                                     =
                                                     (modifier.SPARQL11_Algebra.sm_order_by);
                                                   SPARQL11_Algebra.sm_distinct
                                                     = dist;
                                                   SPARQL11_Algebra.sm_reduced
                                                     = red;
                                                   SPARQL11_Algebra.sm_offset
                                                     =
                                                     (modifier.SPARQL11_Algebra.sm_offset);
                                                   SPARQL11_Algebra.sm_limit
                                                     =
                                                     (modifier.SPARQL11_Algebra.sm_limit)
                                                 };
                                               SPARQL11_Algebra.q_values =
                                                 FStar_Pervasives_Native.None
                                             }, ts7)))))))
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
and is_basic_pattern (p : SPARQL11_Algebra.group_graph_pattern) : Prims.bool=
  match p with
  | SPARQL11_Algebra.GP_BGP uu___ -> true
  | SPARQL11_Algebra.GP_Empty -> true
  | SPARQL11_Algebra.GP_PropertyPath (uu___, uu___1, uu___2) -> true
  | SPARQL11_Algebra.GP_Join (p1, p2) ->
      (is_basic_pattern p1) && (is_basic_pattern p2)
  | uu___ -> false
and parse_construct_body (pm : prefix_map) (fuel : Prims.nat)
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (ts : token_stream) : SPARQL11_Algebra.query parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (let ts' = parse_advance ts in
     match parse_peek ts' with
     | Tok_WHERE ->
         (match parse_skip_from (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (ds, ts'') ->
              let ts''1 =
                match parse_peek ts'' with
                | Tok_WHERE -> parse_advance ts''
                | uu___1 -> ts'' in
              (match parse_group_graph_pattern pm (fuel - Prims.int_one)
                       ts''1
               with
               | ParseErr m -> ParseErr m
               | ParseOk (pattern, ts''') ->
                   if Prims.op_Negation (is_basic_pattern pattern)
                   then
                     ParseErr
                       "CONSTRUCT WHERE short form only allows basic graph patterns"
                   else
                     (match parse_solution_modifier pm (fuel - Prims.int_one)
                              ts'''
                      with
                      | ParseErr m -> ParseErr m
                      | ParseOk ((modifier, gb, hv), ts4) ->
                          ParseOk
                            ({
                               SPARQL11_Algebra.q_base = base;
                               SPARQL11_Algebra.q_prefixes = pm;
                               SPARQL11_Algebra.q_form =
                                 (SPARQL11_Algebra.QF_Construct []);
                               SPARQL11_Algebra.q_dataset = ds;
                               SPARQL11_Algebra.q_pattern = pattern;
                               SPARQL11_Algebra.q_group_by = gb;
                               SPARQL11_Algebra.q_having = hv;
                               SPARQL11_Algebra.q_modifier = modifier;
                               SPARQL11_Algebra.q_values =
                                 FStar_Pervasives_Native.None
                             }, ts4))))
     | Tok_FROM ->
         (match parse_skip_from (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (ds, ts'') ->
              let ts''1 =
                match parse_peek ts'' with
                | Tok_WHERE -> parse_advance ts''
                | uu___1 -> ts'' in
              (match parse_group_graph_pattern pm (fuel - Prims.int_one)
                       ts''1
               with
               | ParseErr m -> ParseErr m
               | ParseOk (pattern, ts''') ->
                   if Prims.op_Negation (is_basic_pattern pattern)
                   then
                     ParseErr
                       "CONSTRUCT WHERE short form only allows basic graph patterns"
                   else
                     (match parse_solution_modifier pm (fuel - Prims.int_one)
                              ts'''
                      with
                      | ParseErr m -> ParseErr m
                      | ParseOk ((modifier, gb, hv), ts4) ->
                          ParseOk
                            ({
                               SPARQL11_Algebra.q_base = base;
                               SPARQL11_Algebra.q_prefixes = pm;
                               SPARQL11_Algebra.q_form =
                                 (SPARQL11_Algebra.QF_Construct []);
                               SPARQL11_Algebra.q_dataset = ds;
                               SPARQL11_Algebra.q_pattern = pattern;
                               SPARQL11_Algebra.q_group_by = gb;
                               SPARQL11_Algebra.q_having = hv;
                               SPARQL11_Algebra.q_modifier = modifier;
                               SPARQL11_Algebra.q_values =
                                 FStar_Pervasives_Native.None
                             }, ts4))))
     | Tok_LBRACE ->
         (match parse_group_graph_pattern pm (fuel - Prims.int_one) ts' with
          | ParseErr m -> ParseErr m
          | ParseOk (_template, ts'') ->
              let ts''1 =
                match parse_peek ts'' with
                | Tok_WHERE -> parse_advance ts''
                | uu___1 -> ts'' in
              (match parse_group_graph_pattern pm (fuel - Prims.int_one)
                       ts''1
               with
               | ParseErr m -> ParseErr m
               | ParseOk (pattern, ts''') ->
                   (match parse_solution_modifier pm (fuel - Prims.int_one)
                            ts'''
                    with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((modifier, gb, hv), ts4) ->
                        ParseOk
                          ({
                             SPARQL11_Algebra.q_base = base;
                             SPARQL11_Algebra.q_prefixes = pm;
                             SPARQL11_Algebra.q_form =
                               (SPARQL11_Algebra.QF_Construct []);
                             SPARQL11_Algebra.q_dataset = [];
                             SPARQL11_Algebra.q_pattern = pattern;
                             SPARQL11_Algebra.q_group_by = gb;
                             SPARQL11_Algebra.q_having = hv;
                             SPARQL11_Algebra.q_modifier = modifier;
                             SPARQL11_Algebra.q_values =
                               FStar_Pervasives_Native.None
                           }, ts4))))
     | uu___1 -> ParseErr "expected WHERE or '{' after CONSTRUCT")
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
and select_item_var (item : SPARQL11_Algebra.select_item) :
  SPARQL11_Algebra.var_name=
  match item with
  | SPARQL11_Algebra.SI_Var v -> v
  | SPARQL11_Algebra.SI_Expr (uu___, v) -> v
and select_items_has_var (v : SPARQL11_Algebra.var_name)
  (items : SPARQL11_Algebra.select_item Prims.list) : Prims.bool=
  match items with
  | [] -> false
  | item::rest ->
      (streq (select_item_var item) v) || (select_items_has_var v rest)
and parse_select_items (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.select_item Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.select_item Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_VAR v ->
         if select_items_has_var v acc
         then ParseErr "duplicate variable in SELECT"
         else
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
                        if select_items_has_var v acc
                        then ParseErr "duplicate variable in SELECT"
                        else
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
  if fuel = Prims.int_zero
  then ParseOk ([], ts)
  else
    (match parse_peek ts with
     | Tok_FROM ->
         let ts' = parse_advance ts in
         (match parse_peek ts' with
          | Tok_NAMED ->
              let ts'' = parse_advance ts' in
              (match parse_peek ts'' with
               | Tok_IRI uu___1 ->
                   parse_skip_from (fuel - Prims.int_one)
                     (parse_advance ts'')
               | Tok_PNAME uu___1 ->
                   parse_skip_from (fuel - Prims.int_one)
                     (parse_advance ts'')
               | uu___1 -> ParseErr "expected IRI after FROM NAMED")
          | Tok_IRI uu___1 ->
              parse_skip_from (fuel - Prims.int_one) (parse_advance ts')
          | Tok_PNAME uu___1 ->
              parse_skip_from (fuel - Prims.int_one) (parse_advance ts')
          | uu___1 -> ParseErr "expected IRI or NAMED after FROM")
     | uu___1 -> ParseOk ([], ts))
and parse_group_condition (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.group_condition parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_VAR v -> ParseOk ((SPARQL11_Algebra.GC_Var v), (parse_advance ts))
     | Tok_LPAREN ->
         (match parse_expr pm (fuel - Prims.int_one) (parse_advance ts) with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              (match parse_peek ts' with
               | Tok_AS ->
                   let ts'' = parse_advance ts' in
                   (match parse_peek ts'' with
                    | Tok_VAR v ->
                        (match parse_expect Tok_RPAREN (parse_advance ts'')
                         with
                         | ParseErr m -> ParseErr m
                         | ParseOk ((), ts''') ->
                             ParseOk
                               ((SPARQL11_Algebra.GC_Expr
                                   (e, (FStar_Pervasives_Native.Some v))),
                                 ts'''))
                    | uu___1 -> ParseErr "expected variable after AS")
               | Tok_RPAREN ->
                   ParseOk
                     ((SPARQL11_Algebra.GC_Expr
                         (e, FStar_Pervasives_Native.None)),
                       (parse_advance ts'))
               | uu___1 -> ParseErr "expected ')' or AS in GROUP BY"))
     | uu___1 ->
         (match parse_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              ParseOk ((SPARQL11_Algebra.GC_BuiltIn e), ts')))
and parse_group_by_list (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.group_condition Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.group_condition Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_VAR uu___1 ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_LPAREN ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_STR ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_LANG ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_LANGMATCHES ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_DATATYPE ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_BOUND ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_IF ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_IRI_KW ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_URI ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_CONCAT ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_STRLEN ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_UCASE ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_LCASE ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_ENCODE_FOR_URI ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_CONTAINS ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_STRSTARTS ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_STRENDS ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_STRBEFORE ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_STRAFTER ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_REPLACE ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_REGEX ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_SUBSTR ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_ABS ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_CEIL ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_FLOOR ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_ROUND ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_ISIRI ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_ISBLANK ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_ISLITERAL ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_ISNUMERIC ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_SAMETERM ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_COALESCE ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_IRI uu___1 ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | Tok_PNAME uu___1 ->
         (match parse_group_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (gc, ts') ->
              parse_group_by_list pm (fuel - Prims.int_one) (gc :: acc) ts')
     | uu___1 -> ParseOk ((FStar_List_Tot_Base.rev acc), ts))
and parse_order_condition (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.order_condition parse_result=
  if fuel = Prims.int_zero
  then ParseErr "recursion limit"
  else
    (match parse_peek ts with
     | Tok_ASC ->
         let ts' = parse_advance ts in
         (match parse_expect Tok_LPAREN ts' with
          | ParseErr uu___1 ->
              (match parse_expr pm (fuel - Prims.int_one) ts' with
               | ParseErr m -> ParseErr m
               | ParseOk (e, ts'') ->
                   ParseOk ((SPARQL11_Algebra.OC_Asc e), ts''))
          | ParseOk ((), ts'') ->
              (match parse_expr pm (fuel - Prims.int_one) ts'' with
               | ParseErr m -> ParseErr m
               | ParseOk (e, ts''') ->
                   (match parse_expect Tok_RPAREN ts''' with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts4) ->
                        ParseOk ((SPARQL11_Algebra.OC_Asc e), ts4))))
     | Tok_DESC ->
         let ts' = parse_advance ts in
         (match parse_expect Tok_LPAREN ts' with
          | ParseErr uu___1 ->
              (match parse_expr pm (fuel - Prims.int_one) ts' with
               | ParseErr m -> ParseErr m
               | ParseOk (e, ts'') ->
                   ParseOk ((SPARQL11_Algebra.OC_Desc e), ts''))
          | ParseOk ((), ts'') ->
              (match parse_expr pm (fuel - Prims.int_one) ts'' with
               | ParseErr m -> ParseErr m
               | ParseOk (e, ts''') ->
                   (match parse_expect Tok_RPAREN ts''' with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts4) ->
                        ParseOk ((SPARQL11_Algebra.OC_Desc e), ts4))))
     | Tok_VAR v ->
         ParseOk
           ((SPARQL11_Algebra.OC_Asc (SPARQL11_Algebra.E_Var v)),
             (parse_advance ts))
     | Tok_LPAREN ->
         (match parse_expr pm (fuel - Prims.int_one) (parse_advance ts) with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              (match parse_expect Tok_RPAREN ts' with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts'') ->
                   ParseOk ((SPARQL11_Algebra.OC_Asc e), ts'')))
     | uu___1 ->
         (match parse_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') -> ParseOk ((SPARQL11_Algebra.OC_Asc e), ts')))
and parse_order_by_list (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.order_condition Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.order_condition Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_ASC ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_DESC ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_VAR uu___1 ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_LPAREN ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_IRI uu___1 ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_PNAME uu___1 ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_STR ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_LANG ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_LANGMATCHES ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_DATATYPE ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_BOUND ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_IF ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_IRI_KW ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_URI ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_CONCAT ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_ISIRI ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_ISBLANK ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_ISLITERAL ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_ISNUMERIC ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_SAMETERM ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | Tok_COALESCE ->
         (match parse_order_condition pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (oc, ts') ->
              parse_order_by_list pm (fuel - Prims.int_one) (oc :: acc) ts')
     | uu___1 -> ParseOk ((FStar_List_Tot_Base.rev acc), ts))
and parse_having_list (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.expr Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.expr Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_LPAREN ->
         (match parse_expr pm (fuel - Prims.int_one) (parse_advance ts) with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              (match parse_expect Tok_RPAREN ts' with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts'') ->
                   parse_having_list pm (fuel - Prims.int_one) (e :: acc)
                     ts''))
     | Tok_STR ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_LANG ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_LANGMATCHES ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_DATATYPE ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_BOUND ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_IF ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_IRI_KW ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_URI ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_CONCAT ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_ISIRI ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_ISBLANK ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_ISLITERAL ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_ISNUMERIC ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_SAMETERM ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_COALESCE ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_EXISTS ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_NOT ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | Tok_REGEX ->
         (match parse_primary_expr pm (fuel - Prims.int_one) ts with
          | ParseErr m -> ParseErr m
          | ParseOk (e, ts') ->
              parse_having_list pm (fuel - Prims.int_one) (e :: acc) ts')
     | uu___1 -> ParseOk ((FStar_List_Tot_Base.rev acc), ts))
and parse_solution_modifier (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : modifier_result parse_result=
  if fuel = Prims.int_zero
  then
    ParseOk
      ((default_modifier, FStar_Pervasives_Native.None,
         FStar_Pervasives_Native.None), ts)
  else
    (let uu___1 =
       match parse_peek ts with
       | Tok_GROUP ->
           let ts' = parse_advance ts in
           (match parse_peek ts' with
            | Tok_BY ->
                (match parse_group_by_list pm (fuel - Prims.int_one) []
                         (parse_advance ts')
                 with
                 | ParseOk (conds, ts'') ->
                     ((FStar_Pervasives_Native.Some conds), ts'')
                 | ParseErr uu___2 -> (FStar_Pervasives_Native.None, ts))
            | uu___2 -> (FStar_Pervasives_Native.None, ts))
       | uu___2 -> (FStar_Pervasives_Native.None, ts) in
     match uu___1 with
     | (gb, ts1) ->
         let uu___2 =
           match parse_peek ts1 with
           | Tok_HAVING ->
               (match parse_having_list pm (fuel - Prims.int_one) []
                        (parse_advance ts1)
                with
                | ParseOk (conds, ts') ->
                    ((FStar_Pervasives_Native.Some conds), ts')
                | ParseErr uu___3 -> (FStar_Pervasives_Native.None, ts1))
           | uu___3 -> (FStar_Pervasives_Native.None, ts1) in
         (match uu___2 with
          | (hv, ts2) ->
              let uu___3 =
                match parse_peek ts2 with
                | Tok_ORDER ->
                    let ts' = parse_advance ts2 in
                    (match parse_peek ts' with
                     | Tok_BY ->
                         (match parse_order_by_list pm (fuel - Prims.int_one)
                                  [] (parse_advance ts')
                          with
                          | ParseOk (conds, ts'') ->
                              ((FStar_Pervasives_Native.Some conds), ts'')
                          | ParseErr uu___4 ->
                              (FStar_Pervasives_Native.None, ts2))
                     | uu___4 -> (FStar_Pervasives_Native.None, ts2))
                | uu___4 -> (FStar_Pervasives_Native.None, ts2) in
              (match uu___3 with
               | (ob, ts3) ->
                   let uu___4 =
                     match parse_peek ts3 with
                     | Tok_LIMIT ->
                         let ts' = parse_advance ts3 in
                         (match parse_peek ts' with
                          | Tok_INTEGER n ->
                              (match parse_int_str n with
                               | FStar_Pervasives_Native.Some i ->
                                   ((FStar_Pervasives_Native.Some i),
                                     (parse_advance ts'))
                               | FStar_Pervasives_Native.None ->
                                   (FStar_Pervasives_Native.None, ts'))
                          | uu___5 -> (FStar_Pervasives_Native.None, ts'))
                     | uu___5 -> (FStar_Pervasives_Native.None, ts3) in
                   (match uu___4 with
                    | (limit, ts4) ->
                        let uu___5 =
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
                               | uu___6 ->
                                   (FStar_Pervasives_Native.None, ts'))
                          | uu___6 -> (FStar_Pervasives_Native.None, ts4) in
                        (match uu___5 with
                         | (offset, ts5) ->
                             let modifier =
                               {
                                 SPARQL11_Algebra.sm_order_by = ob;
                                 SPARQL11_Algebra.sm_distinct = false;
                                 SPARQL11_Algebra.sm_reduced = false;
                                 SPARQL11_Algebra.sm_offset = offset;
                                 SPARQL11_Algebra.sm_limit = limit
                               } in
                             ParseOk ((modifier, gb, hv), ts5))))))
let rec tokens_only_eof (ts : token_stream) : Prims.bool=
  match ts with
  | [] -> true
  | (Tok_EOF)::rest -> tokens_only_eof rest
  | uu___ -> false
let starts_with_string (s : Prims.string) (prefix : Prims.string) :
  Prims.bool=
  let ls = FStar_String.strlen s in
  let lp = FStar_String.strlen prefix in
  (lp <= ls) && ((substring s Prims.int_zero lp) = prefix)
let is_labeled_bnode_id (b : Prims.string) : Prims.bool=
  Prims.op_Negation (starts_with_string b "_:bnode_")
let rec string_mem (x : Prims.string) (xs : Prims.string Prims.list) :
  Prims.bool=
  match xs with | [] -> false | y::ys -> (streq x y) || (string_mem x ys)
let rec string_add_unique (x : Prims.string) (xs : Prims.string Prims.list) :
  Prims.string Prims.list= if string_mem x xs then xs else x :: xs
let rec string_union (xs : Prims.string Prims.list)
  (ys : Prims.string Prims.list) : Prims.string Prims.list=
  match xs with
  | [] -> ys
  | x::rest -> string_union rest (string_add_unique x ys)
let rec string_overlaps (xs : Prims.string Prims.list)
  (ys : Prims.string Prims.list) : Prims.bool=
  match xs with
  | [] -> false
  | x::rest -> (string_mem x ys) || (string_overlaps rest ys)
let bnodes_in_pattern_subject (ps : SPARQL11_Algebra.pattern_subject) :
  Prims.string Prims.list=
  match ps with
  | SPARQL11_Algebra.PS_BNode b -> if is_labeled_bnode_id b then [b] else []
  | uu___ -> []
let bnodes_in_pattern_term (pt : SPARQL11_Algebra.pattern_term) :
  Prims.string Prims.list=
  match pt with
  | SPARQL11_Algebra.PT_BNode b -> if is_labeled_bnode_id b then [b] else []
  | uu___ -> []
let bnodes_in_triple_pattern (tp : SPARQL11_Algebra.triple_pattern) :
  Prims.string Prims.list=
  string_union (bnodes_in_pattern_subject tp.SPARQL11_Algebra.tp_s)
    (string_union (bnodes_in_pattern_term tp.SPARQL11_Algebra.tp_p)
       (bnodes_in_pattern_term tp.SPARQL11_Algebra.tp_o))
let bnodes_in_property_path_pattern (ps : SPARQL11_Algebra.pattern_subject)
  (pt : SPARQL11_Algebra.pattern_term) : Prims.string Prims.list=
  string_union (bnodes_in_pattern_subject ps) (bnodes_in_pattern_term pt)
let rec bnodes_in_bgp (bgp : SPARQL11_Algebra.bgp) : Prims.string Prims.list=
  match bgp with
  | [] -> []
  | tp::rest ->
      string_union (bnodes_in_triple_pattern tp) (bnodes_in_bgp rest)
let rec preserves_bgp_scope (p : SPARQL11_Algebra.group_graph_pattern) :
  Prims.bool=
  match p with
  | SPARQL11_Algebra.GP_BGP uu___ -> true
  | SPARQL11_Algebra.GP_PropertyPath (uu___, uu___1, uu___2) -> true
  | SPARQL11_Algebra.GP_Filter (uu___, p1) -> preserves_bgp_scope p1
  | SPARQL11_Algebra.GP_Bind (uu___, uu___1, p1) -> preserves_bgp_scope p1
  | SPARQL11_Algebra.GP_Values (uu___, uu___1) -> true
  | SPARQL11_Algebra.GP_Empty -> true
  | SPARQL11_Algebra.GP_Join (p1, p2) ->
      (preserves_bgp_scope p1) && (preserves_bgp_scope p2)
  | uu___ -> false
let rec validate_bnode_scope_pattern
  (p : SPARQL11_Algebra.group_graph_pattern) :
  (Prims.bool * Prims.string Prims.list)=
  match p with
  | SPARQL11_Algebra.GP_BGP bgp -> (true, (bnodes_in_bgp bgp))
  | SPARQL11_Algebra.GP_PropertyPath (ps, uu___, pt) ->
      (true, (bnodes_in_property_path_pattern ps pt))
  | SPARQL11_Algebra.GP_Filter (e, p1) ->
      let uu___ = validate_bnode_scope_pattern p1 in
      (match uu___ with
       | (ok1, b1) ->
           let uu___1 = validate_bnode_scope_expr e in
           (match uu___1 with | (ok2, uu___2) -> ((ok1 && ok2), b1)))
  | SPARQL11_Algebra.GP_Bind (e, uu___, p1) ->
      let uu___1 = validate_bnode_scope_pattern p1 in
      (match uu___1 with
       | (ok1, b1) ->
           let uu___2 = validate_bnode_scope_expr e in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), b1)))
  | SPARQL11_Algebra.GP_Values (uu___, uu___1) -> (true, [])
  | SPARQL11_Algebra.GP_Empty -> (true, [])
  | SPARQL11_Algebra.GP_Join (p1, p2) ->
      let uu___ = validate_bnode_scope_pattern p1 in
      (match uu___ with
       | (ok1, b1) ->
           let uu___1 = validate_bnode_scope_pattern p2 in
           (match uu___1 with
            | (ok2, b2) ->
                let allow_overlap =
                  (preserves_bgp_scope p1) && (preserves_bgp_scope p2) in
                (((ok1 && ok2) &&
                    (allow_overlap ||
                       (Prims.op_Negation (string_overlaps b1 b2)))),
                  (string_union b1 b2))))
  | SPARQL11_Algebra.GP_Union (p1, p2) ->
      let uu___ = validate_bnode_scope_pattern p1 in
      (match uu___ with
       | (ok1, b1) ->
           let uu___1 = validate_bnode_scope_pattern p2 in
           (match uu___1 with
            | (ok2, b2) ->
                (((ok1 && ok2) && (Prims.op_Negation (string_overlaps b1 b2))),
                  (string_union b1 b2))))
  | SPARQL11_Algebra.GP_Minus (p1, p2) ->
      let uu___ = validate_bnode_scope_pattern p1 in
      (match uu___ with
       | (ok1, b1) ->
           let uu___1 = validate_bnode_scope_pattern p2 in
           (match uu___1 with
            | (ok2, b2) ->
                (((ok1 && ok2) && (Prims.op_Negation (string_overlaps b1 b2))),
                  (string_union b1 b2))))
  | SPARQL11_Algebra.GP_LeftJoin (p1, p2, e) ->
      let uu___ = validate_bnode_scope_pattern p1 in
      (match uu___ with
       | (ok1, b1) ->
           let uu___1 = validate_bnode_scope_pattern p2 in
           (match uu___1 with
            | (ok2, b2) ->
                let uu___2 = validate_bnode_scope_expr e in
                (match uu___2 with
                 | (ok3, uu___3) ->
                     ((((ok1 && ok2) && ok3) &&
                         (Prims.op_Negation (string_overlaps b1 b2))),
                       (string_union b1 b2)))))
  | SPARQL11_Algebra.GP_Graph (uu___, p1) -> validate_bnode_scope_pattern p1
  | SPARQL11_Algebra.GP_Service (uu___, p1, uu___1) ->
      validate_bnode_scope_pattern p1
  | SPARQL11_Algebra.GP_SubSelect q -> validate_bnode_scope_query q
and validate_bnode_scope_expr (e : SPARQL11_Algebra.expr) :
  (Prims.bool * Prims.string Prims.list)=
  match e with
  | SPARQL11_Algebra.E_Exists p -> validate_bnode_scope_pattern p
  | SPARQL11_Algebra.E_NotExists p -> validate_bnode_scope_pattern p
  | SPARQL11_Algebra.E_Arith (uu___, e1, e2) ->
      let uu___1 = validate_bnode_scope_expr e1 in
      (match uu___1 with
       | (ok1, uu___2) ->
           let uu___3 = validate_bnode_scope_expr e2 in
           (match uu___3 with | (ok2, uu___4) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_Compare (uu___, e1, e2) ->
      let uu___1 = validate_bnode_scope_expr e1 in
      (match uu___1 with
       | (ok1, uu___2) ->
           let uu___3 = validate_bnode_scope_expr e2 in
           (match uu___3 with | (ok2, uu___4) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_And (e1, e2) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_Or (e1, e2) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_StrDt (e1, e2) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_StrLang (e1, e2) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_StrStarts (e1, e2) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_StrEnds (e1, e2) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_Contains (e1, e2) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_StrBefore (e1, e2) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_StrAfter (e1, e2) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_SameTerm (e1, e2) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with | (ok2, uu___3) -> ((ok1 && ok2), [])))
  | SPARQL11_Algebra.E_Not e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_UnaryPlus e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_UnaryMinus e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_IsIRI e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_IsBlank e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_IsLiteral e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_IsNumeric e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Str e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Lang e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Datatype e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_IRI_fn e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_StrLen e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_UCase e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_LCase e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_EncodeForUri e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Abs e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Round e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Ceil e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Floor e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_MD5 e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_SHA1 e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_SHA256 e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_SHA384 e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_SHA512 e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Year e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Month e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Day e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Hours e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Minutes e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Seconds e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Timezone e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Tz e1 -> validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Aggregate (uu___, uu___1, e1) ->
      validate_bnode_scope_expr e1
  | SPARQL11_Algebra.E_Substr (e1, e2, e3) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with
            | (ok2, uu___3) ->
                let uu___4 =
                  match e3 with
                  | FStar_Pervasives_Native.None -> (true, [])
                  | FStar_Pervasives_Native.Some ef ->
                      validate_bnode_scope_expr ef in
                (match uu___4 with
                 | (ok3, uu___5) -> (((ok1 && ok2) && ok3), []))))
  | SPARQL11_Algebra.E_If (e1, e2, e3) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with
            | (ok2, uu___3) ->
                let uu___4 = validate_bnode_scope_expr e3 in
                (match uu___4 with
                 | (ok3, uu___5) -> (((ok1 && ok2) && ok3), []))))
  | SPARQL11_Algebra.E_Coalesce es -> ((validate_bnode_scope_exprs es), [])
  | SPARQL11_Algebra.E_Concat es -> ((validate_bnode_scope_exprs es), [])
  | SPARQL11_Algebra.E_FunctionCall (uu___, es) ->
      ((validate_bnode_scope_exprs es), [])
  | SPARQL11_Algebra.E_In (e1, es) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let ok_rest = validate_bnode_scope_exprs es in
           ((ok1 && ok_rest), []))
  | SPARQL11_Algebra.E_NotIn (e1, es) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let ok_rest = validate_bnode_scope_exprs es in
           ((ok1 && ok_rest), []))
  | SPARQL11_Algebra.E_Replace (e1, e2, e3, flags) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with
            | (ok2, uu___3) ->
                let uu___4 = validate_bnode_scope_expr e3 in
                (match uu___4 with
                 | (ok3, uu___5) ->
                     let uu___6 =
                       match flags with
                       | FStar_Pervasives_Native.None -> (true, [])
                       | FStar_Pervasives_Native.Some ef ->
                           validate_bnode_scope_expr ef in
                     (match uu___6 with
                      | (ok4, uu___7) -> ((((ok1 && ok2) && ok3) && ok4), [])))))
  | SPARQL11_Algebra.E_Regex (e1, e2, flags) ->
      let uu___ = validate_bnode_scope_expr e1 in
      (match uu___ with
       | (ok1, uu___1) ->
           let uu___2 = validate_bnode_scope_expr e2 in
           (match uu___2 with
            | (ok2, uu___3) ->
                let uu___4 =
                  match flags with
                  | FStar_Pervasives_Native.None -> (true, [])
                  | FStar_Pervasives_Native.Some ef ->
                      validate_bnode_scope_expr ef in
                (match uu___4 with
                 | (ok3, uu___5) -> (((ok1 && ok2) && ok3), []))))
  | uu___ -> (true, [])
and validate_bnode_scope_exprs (es : SPARQL11_Algebra.expr Prims.list) :
  Prims.bool=
  match es with
  | [] -> true
  | ex::rest ->
      let uu___ = validate_bnode_scope_expr ex in
      (match uu___ with
       | (ok, uu___1) -> ok && (validate_bnode_scope_exprs rest))
and validate_bnode_scope_query (q : SPARQL11_Algebra.query) :
  (Prims.bool * Prims.string Prims.list)=
  validate_bnode_scope_pattern q.SPARQL11_Algebra.q_pattern
let validate_bnode_scope_top (q : SPARQL11_Algebra.query) : Prims.bool=
  FStar_Pervasives_Native.fst (validate_bnode_scope_query q)
let parse_sparql (input : Prims.string) :
  SPARQL11_Algebra.query parse_result=
  let tokens = tokenize input in
  match parse_select_query [] (Prims.of_int (10000)) tokens with
  | ParseOk (q, rest) ->
      if Prims.op_Negation (tokens_only_eof rest)
      then ParseErr "unexpected tokens after query"
      else
        if Prims.op_Negation (validate_bnode_scope_top q)
        then ParseErr "blank node label reused across graph-pattern scope"
        else ParseOk (q, rest)
  | ParseErr msg -> ParseErr msg
let parse_iri_ref (pm : prefix_map) (ts : token_stream) :
  RDF_Graph_Executable.wf_iri parse_result=
  match parse_peek ts with
  | Tok_IRI i ->
      let ri = resolve_tok_iri i in
      if RDF_Graph_Executable.is_iri ri
      then ParseOk (ri, (parse_advance ts))
      else ParseErr "invalid IRI"
  | Tok_PNAME pn ->
      (match resolve_pname pn pm with
       | FStar_Pervasives_Native.Some iri ->
           if RDF_Graph_Executable.is_iri iri
           then ParseOk (iri, (parse_advance ts))
           else ParseErr "invalid IRI resolved from PNAME"
       | FStar_Pervasives_Native.None -> ParseErr "unresolved PNAME prefix")
  | uu___ -> ParseErr "expected IRI or prefixed name"
let parse_graph_ref_graph_only (pm : prefix_map) (ts : token_stream) :
  SPARQL11_Algebra.graph_ref parse_result=
  match parse_peek ts with
  | Tok_GRAPH ->
      let ts' = parse_advance ts in
      (match parse_iri_ref pm ts' with
       | ParseErr m -> ParseErr m
       | ParseOk (i, ts'') -> ParseOk ((SPARQL11_Algebra.GR_Graph i), ts''))
  | uu___ -> ParseErr "expected GRAPH <iri>"
let parse_graph_ref_all (pm : prefix_map) (ts : token_stream) :
  SPARQL11_Algebra.graph_ref parse_result=
  match parse_peek ts with
  | Tok_DEFAULT -> ParseOk (SPARQL11_Algebra.GR_Default, (parse_advance ts))
  | Tok_NAMED -> ParseOk (SPARQL11_Algebra.GR_Named, (parse_advance ts))
  | Tok_ALL -> ParseOk (SPARQL11_Algebra.GR_All, (parse_advance ts))
  | Tok_GRAPH -> parse_graph_ref_graph_only pm ts
  | uu___ -> ParseErr "expected DEFAULT, NAMED, ALL, or GRAPH <iri>"
let parse_graph_or_default (pm : prefix_map) (ts : token_stream) :
  SPARQL11_Algebra.graph_ref parse_result=
  match parse_peek ts with
  | Tok_DEFAULT -> ParseOk (SPARQL11_Algebra.GR_Default, (parse_advance ts))
  | Tok_GRAPH ->
      let ts' = parse_advance ts in
      (match parse_iri_ref pm ts' with
       | ParseErr m -> ParseErr m
       | ParseOk (i, ts'') -> ParseOk ((SPARQL11_Algebra.GR_Graph i), ts''))
  | Tok_IRI uu___ ->
      (match parse_iri_ref pm ts with
       | ParseErr m -> ParseErr m
       | ParseOk (i, ts'') -> ParseOk ((SPARQL11_Algebra.GR_Graph i), ts''))
  | Tok_PNAME uu___ ->
      (match parse_iri_ref pm ts with
       | ParseErr m -> ParseErr m
       | ParseOk (i, ts'') -> ParseOk ((SPARQL11_Algebra.GR_Graph i), ts''))
  | uu___ -> ParseErr "expected DEFAULT or [GRAPH] <iri>"
let parse_silent (ts : token_stream) : (Prims.bool * token_stream)=
  match parse_peek ts with
  | Tok_SILENT -> (true, (parse_advance ts))
  | uu___ -> (false, ts)
let rec gp_has_var (g : SPARQL11_Algebra.group_graph_pattern) : Prims.bool=
  match g with
  | SPARQL11_Algebra.GP_BGP bgp -> bgp_has_any_var bgp
  | SPARQL11_Algebra.GP_Empty -> false
  | SPARQL11_Algebra.GP_Join (a, b) -> (gp_has_var a) || (gp_has_var b)
  | SPARQL11_Algebra.GP_Graph (gt, inner) ->
      (match gt with | SPARQL11_Algebra.PT_Var uu___ -> true | uu___ -> false)
        || (gp_has_var inner)
  | SPARQL11_Algebra.GP_PropertyPath (uu___, uu___1, uu___2) -> true
  | SPARQL11_Algebra.GP_LeftJoin (a, b, uu___) ->
      (gp_has_var a) || (gp_has_var b)
  | SPARQL11_Algebra.GP_Union (a, b) -> (gp_has_var a) || (gp_has_var b)
  | SPARQL11_Algebra.GP_Minus (a, b) -> (gp_has_var a) || (gp_has_var b)
  | SPARQL11_Algebra.GP_Filter (uu___, inner) -> gp_has_var inner
  | SPARQL11_Algebra.GP_Bind (uu___, uu___1, inner) -> gp_has_var inner
  | SPARQL11_Algebra.GP_Values (uu___, uu___1) -> true
  | SPARQL11_Algebra.GP_Service (uu___, uu___1, uu___2) -> true
  | SPARQL11_Algebra.GP_SubSelect uu___ -> true
and bgp_has_any_var (b : SPARQL11_Algebra.bgp) : Prims.bool=
  match b with
  | [] -> false
  | tp::rest ->
      (((match tp.SPARQL11_Algebra.tp_s with
         | SPARQL11_Algebra.PS_Var uu___ -> true
         | uu___ -> false) ||
          (match tp.SPARQL11_Algebra.tp_p with
           | SPARQL11_Algebra.PT_Var uu___ -> true
           | uu___ -> false))
         ||
         (match tp.SPARQL11_Algebra.tp_o with
          | SPARQL11_Algebra.PT_Var uu___ -> true
          | uu___ -> false))
        || (bgp_has_any_var rest)
let rec gp_has_bnode (g : SPARQL11_Algebra.group_graph_pattern) : Prims.bool=
  match g with
  | SPARQL11_Algebra.GP_BGP bgp -> bgp_has_any_bnode bgp
  | SPARQL11_Algebra.GP_Empty -> false
  | SPARQL11_Algebra.GP_Join (a, b) -> (gp_has_bnode a) || (gp_has_bnode b)
  | SPARQL11_Algebra.GP_Graph (uu___, inner) -> gp_has_bnode inner
  | SPARQL11_Algebra.GP_PropertyPath (ps, uu___, po) ->
      (match ps with
       | SPARQL11_Algebra.PS_BNode uu___1 -> true
       | uu___1 -> false) ||
        ((match po with
          | SPARQL11_Algebra.PT_BNode uu___1 -> true
          | uu___1 -> false))
  | SPARQL11_Algebra.GP_LeftJoin (a, b, uu___) ->
      (gp_has_bnode a) || (gp_has_bnode b)
  | SPARQL11_Algebra.GP_Union (a, b) -> (gp_has_bnode a) || (gp_has_bnode b)
  | SPARQL11_Algebra.GP_Minus (a, b) -> (gp_has_bnode a) || (gp_has_bnode b)
  | SPARQL11_Algebra.GP_Filter (uu___, inner) -> gp_has_bnode inner
  | SPARQL11_Algebra.GP_Bind (uu___, uu___1, inner) -> gp_has_bnode inner
  | SPARQL11_Algebra.GP_Values (uu___, uu___1) -> false
  | SPARQL11_Algebra.GP_Service (uu___, inner, uu___1) -> gp_has_bnode inner
  | SPARQL11_Algebra.GP_SubSelect uu___ -> false
and bgp_has_any_bnode (b : SPARQL11_Algebra.bgp) : Prims.bool=
  match b with
  | [] -> false
  | tp::rest ->
      (((match tp.SPARQL11_Algebra.tp_s with
         | SPARQL11_Algebra.PS_BNode uu___ -> true
         | uu___ -> false) ||
          (match tp.SPARQL11_Algebra.tp_p with
           | SPARQL11_Algebra.PT_BNode uu___ -> true
           | uu___ -> false))
         ||
         (match tp.SPARQL11_Algebra.tp_o with
          | SPARQL11_Algebra.PT_BNode uu___ -> true
          | uu___ -> false))
        || (bgp_has_any_bnode rest)
let rec gp_has_nested_graph_under_graph
  (g : SPARQL11_Algebra.group_graph_pattern) : Prims.bool=
  match g with
  | SPARQL11_Algebra.GP_Graph (uu___, inner) -> gp_has_graph_anywhere inner
  | SPARQL11_Algebra.GP_Join (a, b) ->
      (gp_has_nested_graph_under_graph a) ||
        (gp_has_nested_graph_under_graph b)
  | uu___ -> false
and gp_has_graph_anywhere (g : SPARQL11_Algebra.group_graph_pattern) :
  Prims.bool=
  match g with
  | SPARQL11_Algebra.GP_Graph (uu___, uu___1) -> true
  | SPARQL11_Algebra.GP_Join (a, b) ->
      (gp_has_graph_anywhere a) || (gp_has_graph_anywhere b)
  | SPARQL11_Algebra.GP_Filter (uu___, inner) -> gp_has_graph_anywhere inner
  | SPARQL11_Algebra.GP_Bind (uu___, uu___1, inner) ->
      gp_has_graph_anywhere inner
  | uu___ -> false
let rec parse_quad_block (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.group_graph_pattern) (ts : token_stream) :
  SPARQL11_Algebra.group_graph_pattern parse_result=
  if fuel = Prims.int_zero
  then ParseOk (acc, ts)
  else
    (match parse_peek ts with
     | Tok_RBRACE -> ParseOk (acc, ts)
     | Tok_GRAPH ->
         let ts1 = parse_advance ts in
         (match parse_iri_ref pm ts1 with
          | ParseErr m -> ParseErr m
          | ParseOk (g_iri, ts2) ->
              (match parse_expect Tok_LBRACE ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk ((), ts3) ->
                   (match parse_peek ts3 with
                    | Tok_RBRACE ->
                        let acc' =
                          ggp_join acc
                            (SPARQL11_Algebra.GP_Graph
                               ((SPARQL11_Algebra.PT_IRI g_iri),
                                 SPARQL11_Algebra.GP_Empty)) in
                        let ts4 = parse_advance ts3 in
                        let ts41 =
                          match parse_peek ts4 with
                          | Tok_DOT -> parse_advance ts4
                          | uu___1 -> ts4 in
                        parse_quad_block pm (fuel - Prims.int_one) acc' ts41
                    | uu___1 ->
                        (match parse_triples_block pm (fuel - Prims.int_one)
                                 SPARQL11_Algebra.GP_Empty ts3
                         with
                         | ParseErr m -> ParseErr m
                         | ParseOk (inner, ts4) ->
                             (match parse_expect Tok_RBRACE ts4 with
                              | ParseErr m -> ParseErr m
                              | ParseOk ((), ts5) ->
                                  let acc' =
                                    ggp_join acc
                                      (SPARQL11_Algebra.GP_Graph
                                         ((SPARQL11_Algebra.PT_IRI g_iri),
                                           inner)) in
                                  let ts51 =
                                    match parse_peek ts5 with
                                    | Tok_DOT -> parse_advance ts5
                                    | uu___2 -> ts5 in
                                  parse_quad_block pm (fuel - Prims.int_one)
                                    acc' ts51)))))
     | uu___1 ->
         (match parse_triples_block pm (fuel - Prims.int_one)
                  SPARQL11_Algebra.GP_Empty ts
          with
          | ParseErr uu___2 -> ParseOk (acc, ts)
          | ParseOk (triples, ts') ->
              let acc' = ggp_join acc triples in
              parse_quad_block pm (fuel - Prims.int_one) acc' ts'))
let parse_quad_data (pm : prefix_map) (fuel : Prims.nat) (ts : token_stream)
  : SPARQL11_Algebra.group_graph_pattern parse_result=
  match parse_expect Tok_LBRACE ts with
  | ParseErr m -> ParseErr m
  | ParseOk ((), ts') ->
      (match parse_quad_block pm fuel SPARQL11_Algebra.GP_Empty ts' with
       | ParseErr m -> ParseErr m
       | ParseOk (g, ts'') ->
           (match parse_expect Tok_RBRACE ts'' with
            | ParseErr m -> ParseErr m
            | ParseOk ((), ts''') -> ParseOk (g, ts''')))
let parse_update_prologue (pm : prefix_map)
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (ts : token_stream) :
  (prefix_map * RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
    parse_result=
  parse_prologue pm base (Prims.of_int (1000)) ts
let rec parse_single_update_op (pm : prefix_map) (fuel : Prims.nat)
  (ts : token_stream) : SPARQL11_Algebra.update_op parse_result=
  if fuel = Prims.int_zero
  then ParseErr "update op recursion limit"
  else
    (match parse_peek ts with
     | Tok_LOAD ->
         let ts1 = parse_advance ts in
         let uu___1 = parse_silent ts1 in
         (match uu___1 with
          | (silent, ts2) ->
              (match parse_iri_ref pm ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (src, ts3) ->
                   (match parse_peek ts3 with
                    | Tok_INTO ->
                        let ts4 = parse_advance ts3 in
                        (match parse_expect Tok_GRAPH ts4 with
                         | ParseErr m -> ParseErr m
                         | ParseOk ((), ts5) ->
                             (match parse_iri_ref pm ts5 with
                              | ParseErr m -> ParseErr m
                              | ParseOk (dst, ts6) ->
                                  ParseOk
                                    ((SPARQL11_Algebra.U_Load
                                        (silent, src,
                                          (FStar_Pervasives_Native.Some dst))),
                                      ts6)))
                    | uu___2 ->
                        ParseOk
                          ((SPARQL11_Algebra.U_Load
                              (silent, src, FStar_Pervasives_Native.None)),
                            ts3))))
     | Tok_CLEAR ->
         let ts1 = parse_advance ts in
         let uu___1 = parse_silent ts1 in
         (match uu___1 with
          | (silent, ts2) ->
              (match parse_graph_ref_all pm ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (gr, ts3) ->
                   ParseOk ((SPARQL11_Algebra.U_Clear (silent, gr)), ts3)))
     | Tok_DROP ->
         let ts1 = parse_advance ts in
         let uu___1 = parse_silent ts1 in
         (match uu___1 with
          | (silent, ts2) ->
              (match parse_graph_ref_all pm ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (gr, ts3) ->
                   ParseOk ((SPARQL11_Algebra.U_Drop (silent, gr)), ts3)))
     | Tok_CREATE ->
         let ts1 = parse_advance ts in
         let uu___1 = parse_silent ts1 in
         (match uu___1 with
          | (silent, ts2) ->
              (match parse_graph_ref_graph_only pm ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (gr, ts3) ->
                   (match gr with
                    | SPARQL11_Algebra.GR_Graph iri ->
                        ParseOk
                          ((SPARQL11_Algebra.U_Create (silent, iri)), ts3)
                    | uu___2 -> ParseErr "CREATE expects GRAPH <iri>")))
     | Tok_ADD ->
         let ts1 = parse_advance ts in
         let uu___1 = parse_silent ts1 in
         (match uu___1 with
          | (silent, ts2) ->
              (match parse_graph_or_default pm ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (src, ts3) ->
                   (match parse_expect Tok_TO ts3 with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts4) ->
                        (match parse_graph_or_default pm ts4 with
                         | ParseErr m -> ParseErr m
                         | ParseOk (dst, ts5) ->
                             ParseOk
                               ((SPARQL11_Algebra.U_Add (silent, src, dst)),
                                 ts5)))))
     | Tok_MOVE ->
         let ts1 = parse_advance ts in
         let uu___1 = parse_silent ts1 in
         (match uu___1 with
          | (silent, ts2) ->
              (match parse_graph_or_default pm ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (src, ts3) ->
                   (match parse_expect Tok_TO ts3 with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts4) ->
                        (match parse_graph_or_default pm ts4 with
                         | ParseErr m -> ParseErr m
                         | ParseOk (dst, ts5) ->
                             ParseOk
                               ((SPARQL11_Algebra.U_Move (silent, src, dst)),
                                 ts5)))))
     | Tok_COPY ->
         let ts1 = parse_advance ts in
         let uu___1 = parse_silent ts1 in
         (match uu___1 with
          | (silent, ts2) ->
              (match parse_graph_or_default pm ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (src, ts3) ->
                   (match parse_expect Tok_TO ts3 with
                    | ParseErr m -> ParseErr m
                    | ParseOk ((), ts4) ->
                        (match parse_graph_or_default pm ts4 with
                         | ParseErr m -> ParseErr m
                         | ParseOk (dst, ts5) ->
                             ParseOk
                               ((SPARQL11_Algebra.U_Copy (silent, src, dst)),
                                 ts5)))))
     | Tok_INSERT ->
         let ts1 = parse_advance ts in
         (match parse_peek ts1 with
          | Tok_DATA ->
              let ts2 = parse_advance ts1 in
              (match parse_quad_data pm (fuel - Prims.int_one) ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (data, ts3) ->
                   if gp_has_var data
                   then ParseErr "INSERT DATA must not contain variables"
                   else
                     if gp_has_nested_graph_under_graph data
                     then
                       ParseErr
                         "INSERT DATA: nested GRAPH blocks not allowed"
                     else ParseOk ((SPARQL11_Algebra.U_InsertData data), ts3))
          | Tok_LBRACE ->
              (match parse_quad_data pm (fuel - Prims.int_one) ts1 with
               | ParseErr m -> ParseErr m
               | ParseOk (insert_tmpl, ts2) ->
                   (match parse_using_list pm (fuel - Prims.int_one) [] ts2
                    with
                    | ParseErr m -> ParseErr m
                    | ParseOk (using, ts3) ->
                        (match parse_expect Tok_WHERE ts3 with
                         | ParseErr m -> ParseErr m
                         | ParseOk ((), ts4) ->
                             (match parse_group_graph_pattern pm
                                      (fuel - Prims.int_one) ts4
                              with
                              | ParseErr m -> ParseErr m
                              | ParseOk (where, ts5) ->
                                  ParseOk
                                    ((SPARQL11_Algebra.U_Modify
                                        (FStar_Pervasives_Native.None,
                                          FStar_Pervasives_Native.None,
                                          (FStar_Pervasives_Native.Some
                                             insert_tmpl), using, where)),
                                      ts5)))))
          | uu___1 -> ParseErr "expected DATA or { after INSERT")
     | Tok_DELETE ->
         let ts1 = parse_advance ts in
         (match parse_peek ts1 with
          | Tok_DATA ->
              let ts2 = parse_advance ts1 in
              (match parse_quad_data pm (fuel - Prims.int_one) ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (data, ts3) ->
                   if gp_has_var data
                   then ParseErr "DELETE DATA must not contain variables"
                   else
                     if gp_has_bnode data
                     then ParseErr "DELETE DATA must not contain blank nodes"
                     else
                       if gp_has_nested_graph_under_graph data
                       then
                         ParseErr
                           "DELETE DATA: nested GRAPH blocks not allowed"
                       else
                         ParseOk ((SPARQL11_Algebra.U_DeleteData data), ts3))
          | Tok_WHERE ->
              let ts2 = parse_advance ts1 in
              (match parse_group_graph_pattern pm (fuel - Prims.int_one) ts2
               with
               | ParseErr m -> ParseErr m
               | ParseOk (pat, ts3) ->
                   if gp_has_bnode pat
                   then ParseErr "DELETE WHERE must not contain blank nodes"
                   else ParseOk ((SPARQL11_Algebra.U_DeleteWhere pat), ts3))
          | Tok_LBRACE ->
              (match parse_quad_data pm (fuel - Prims.int_one) ts1 with
               | ParseErr m -> ParseErr m
               | ParseOk (del_tmpl, ts2) ->
                   if gp_has_bnode del_tmpl
                   then
                     ParseErr "DELETE template must not contain blank nodes"
                   else
                     (let uu___2 =
                        match parse_peek ts2 with
                        | Tok_INSERT ->
                            let ts2a = parse_advance ts2 in
                            (match parse_quad_data pm (fuel - Prims.int_one)
                                     ts2a
                             with
                             | ParseOk (tmpl, ts2b) ->
                                 ((FStar_Pervasives_Native.Some tmpl), ts2b)
                             | uu___3 -> (FStar_Pervasives_Native.None, ts2))
                        | uu___3 -> (FStar_Pervasives_Native.None, ts2) in
                      match uu___2 with
                      | (ins_tmpl, ts3) ->
                          (match parse_using_list pm (fuel - Prims.int_one)
                                   [] ts3
                           with
                           | ParseErr m -> ParseErr m
                           | ParseOk (using, ts4) ->
                               (match parse_expect Tok_WHERE ts4 with
                                | ParseErr m -> ParseErr m
                                | ParseOk ((), ts5) ->
                                    (match parse_group_graph_pattern pm
                                             (fuel - Prims.int_one) ts5
                                     with
                                     | ParseErr m -> ParseErr m
                                     | ParseOk (where, ts6) ->
                                         ParseOk
                                           ((SPARQL11_Algebra.U_Modify
                                               (FStar_Pervasives_Native.None,
                                                 (FStar_Pervasives_Native.Some
                                                    del_tmpl), ins_tmpl, [],
                                                 where)), ts6))))))
          | uu___1 -> ParseErr "expected DATA, WHERE, or { after DELETE")
     | Tok_WITH ->
         let ts1 = parse_advance ts in
         (match parse_iri_ref pm ts1 with
          | ParseErr m -> ParseErr m
          | ParseOk (with_iri, ts2) ->
              parse_modify_after_with pm (fuel - Prims.int_one)
                (FStar_Pervasives_Native.Some with_iri) ts2)
     | uu___1 -> ParseErr "expected update operation")
and parse_using_list (pm : prefix_map) (fuel : Prims.nat)
  (acc : SPARQL11_Algebra.dataset_clause Prims.list) (ts : token_stream) :
  SPARQL11_Algebra.dataset_clause Prims.list parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((FStar_List_Tot_Base.rev acc), ts)
  else
    (match parse_peek ts with
     | Tok_USING ->
         let ts1 = parse_advance ts in
         (match parse_peek ts1 with
          | Tok_NAMED ->
              let ts2 = parse_advance ts1 in
              (match parse_iri_ref pm ts2 with
               | ParseErr m -> ParseErr m
               | ParseOk (iri, ts3) ->
                   parse_using_list pm (fuel - Prims.int_one)
                     ((SPARQL11_Algebra.DC_Named iri) :: acc) ts3)
          | uu___1 ->
              (match parse_iri_ref pm ts1 with
               | ParseErr m -> ParseErr m
               | ParseOk (iri, ts2) ->
                   parse_using_list pm (fuel - Prims.int_one)
                     ((SPARQL11_Algebra.DC_Default iri) :: acc) ts2))
     | uu___1 -> ParseOk ((FStar_List_Tot_Base.rev acc), ts))
and parse_modify_after_with (pm : prefix_map) (fuel : Prims.nat)
  (with_iri : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (ts : token_stream) : SPARQL11_Algebra.update_op parse_result=
  if fuel = Prims.int_zero
  then ParseErr "update recursion limit"
  else
    (match parse_peek ts with
     | Tok_DELETE ->
         let ts1 = parse_advance ts in
         (match parse_peek ts1 with
          | Tok_WHERE ->
              let ts2 = parse_advance ts1 in
              (match parse_group_graph_pattern pm (fuel - Prims.int_one) ts2
               with
               | ParseErr m -> ParseErr m
               | ParseOk (pat, ts3) ->
                   if gp_has_bnode pat
                   then ParseErr "DELETE WHERE must not contain blank nodes"
                   else
                     ParseOk
                       ((SPARQL11_Algebra.U_Modify
                           (with_iri, (FStar_Pervasives_Native.Some pat),
                             FStar_Pervasives_Native.None, [], pat)), ts3))
          | Tok_LBRACE ->
              (match parse_quad_data pm (fuel - Prims.int_one) ts1 with
               | ParseErr m -> ParseErr m
               | ParseOk (del_tmpl, ts2) ->
                   if gp_has_bnode del_tmpl
                   then
                     ParseErr "DELETE template must not contain blank nodes"
                   else
                     (let uu___2 =
                        match parse_peek ts2 with
                        | Tok_INSERT ->
                            let ts2a = parse_advance ts2 in
                            (match parse_quad_data pm (fuel - Prims.int_one)
                                     ts2a
                             with
                             | ParseOk (tmpl, ts2b) ->
                                 ((FStar_Pervasives_Native.Some tmpl), ts2b)
                             | uu___3 -> (FStar_Pervasives_Native.None, ts2))
                        | uu___3 -> (FStar_Pervasives_Native.None, ts2) in
                      match uu___2 with
                      | (ins_tmpl, ts3) ->
                          (match parse_using_list pm (fuel - Prims.int_one)
                                   [] ts3
                           with
                           | ParseErr m -> ParseErr m
                           | ParseOk (using, ts4) ->
                               (match parse_expect Tok_WHERE ts4 with
                                | ParseErr m -> ParseErr m
                                | ParseOk ((), ts5) ->
                                    (match parse_group_graph_pattern pm
                                             (fuel - Prims.int_one) ts5
                                     with
                                     | ParseErr m -> ParseErr m
                                     | ParseOk (where, ts6) ->
                                         ParseOk
                                           ((SPARQL11_Algebra.U_Modify
                                               (with_iri,
                                                 (FStar_Pervasives_Native.Some
                                                    del_tmpl), ins_tmpl,
                                                 using, where)), ts6))))))
          | uu___1 -> ParseErr "expected { or WHERE after DELETE")
     | Tok_INSERT ->
         let ts1 = parse_advance ts in
         (match parse_peek ts1 with
          | Tok_LBRACE ->
              (match parse_quad_data pm (fuel - Prims.int_one) ts1 with
               | ParseErr m -> ParseErr m
               | ParseOk (ins_tmpl, ts2) ->
                   (match parse_using_list pm (fuel - Prims.int_one) [] ts2
                    with
                    | ParseErr m -> ParseErr m
                    | ParseOk (using, ts3) ->
                        (match parse_expect Tok_WHERE ts3 with
                         | ParseErr m -> ParseErr m
                         | ParseOk ((), ts4) ->
                             (match parse_group_graph_pattern pm
                                      (fuel - Prims.int_one) ts4
                              with
                              | ParseErr m -> ParseErr m
                              | ParseOk (where, ts5) ->
                                  ParseOk
                                    ((SPARQL11_Algebra.U_Modify
                                        (with_iri,
                                          FStar_Pervasives_Native.None,
                                          (FStar_Pervasives_Native.Some
                                             ins_tmpl), using, where)), ts5)))))
          | uu___1 -> ParseErr "expected { after INSERT")
     | uu___1 -> ParseErr "expected DELETE or INSERT after WITH <iri>")
let rec parse_update_seq (pm : prefix_map)
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (acc : SPARQL11_Algebra.update_op Prims.list) (need_sep : Prims.bool)
  (fuel : Prims.nat) (ts : token_stream) :
  (prefix_map * RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option *
    SPARQL11_Algebra.update_op Prims.list) parse_result=
  if fuel = Prims.int_zero
  then ParseOk ((pm, base, (FStar_List_Tot_Base.rev acc)), ts)
  else
    (match parse_peek ts with
     | Tok_EOF -> ParseOk ((pm, base, (FStar_List_Tot_Base.rev acc)), ts)
     | Tok_PREFIX ->
         (match parse_update_prologue pm base ts with
          | ParseErr m -> ParseErr m
          | ParseOk ((pm', base'), ts') ->
              let ts'' = resolve_relative_iri_tokens base' ts' in
              parse_update_seq pm' base' acc false (fuel - Prims.int_one)
                ts'')
     | Tok_BASE ->
         (match parse_update_prologue pm base ts with
          | ParseErr m -> ParseErr m
          | ParseOk ((pm', base'), ts') ->
              let ts'' = resolve_relative_iri_tokens base' ts' in
              parse_update_seq pm' base' acc false (fuel - Prims.int_one)
                ts'')
     | Tok_SEMI ->
         if need_sep
         then
           parse_update_seq pm base acc false (fuel - Prims.int_one)
             (parse_advance ts)
         else ParseErr "unexpected ';' (no preceding update operation)"
     | uu___1 ->
         if need_sep
         then ParseErr "missing ';' between update operations"
         else
           (match parse_single_update_op pm (Prims.of_int (2000)) ts with
            | ParseErr m -> ParseErr m
            | ParseOk (op, ts') ->
                parse_update_seq pm base (op :: acc) true
                  (fuel - Prims.int_one) ts'))
let rec prefix_map_to_wf (pm : prefix_map) :
  (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list=
  match pm with
  | [] -> []
  | (p, i)::rest ->
      if RDF_Graph_Executable.is_iri i
      then (p, i) :: (prefix_map_to_wf rest)
      else prefix_map_to_wf rest
let parse_sparql_update (input : Prims.string) :
  SPARQL11_Algebra.sparql_update parse_result=
  let tokens = tokenize input in
  match parse_update_seq [] FStar_Pervasives_Native.None [] false
          (Prims.of_int (10000)) tokens
  with
  | ParseErr m -> ParseErr m
  | ParseOk ((pm, base, ops), rest) ->
      if Prims.op_Negation (tokens_only_eof rest)
      then ParseErr "unexpected tokens after update request"
      else
        ParseOk
          ({
             SPARQL11_Algebra.u_base = base;
             SPARQL11_Algebra.u_prefixes = (prefix_map_to_wf pm);
             SPARQL11_Algebra.u_ops = ops
           }, rest)
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
