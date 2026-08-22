/-
L4Factoidal.SPARQL.Expr — the SPARQL 1.1 expression language: the
expression AST (§17/§18.2), effective boolean value (§17.2.2), the
value space evaluation returns, and the total evaluator for the §17.4
operator and function library.

Port of `formal/fstar/SPARQL11.Algebra.fst` Part 3 (`expr`, `comp_op`,
`arith_op`, `aggregate_fn`), the `eval_result` value type with
`ebv_checked` / `er_to_term` / `er_to_string` / `er_string_info`, the
scaled-decimal numeric model (`parse_to_scaled`,
`parse_double_to_scaled`, `format_scaled_value`, `format_as_double`,
`numeric_compare`, `value_compare`, `add_scaled`,
`format_numeric_result`), the `fn_*` accessor family, and the
`eval_expr_with_base` / `eval_coalesce_with_base` / `eval_in_with_base`
/ `eval_concat_with_base` evaluator clique.

WHAT THIS FILE IMPLEMENTS (SPARQL 1.1 Query, W3C Rec. 21 March 2013):
  * §17.2.2 effective boolean value — `ebv`, the operand-mapping table
    transcribed row by row;
  * §17.3 the error-tolerant / error-preserving `&&`, `||`, `!` tables;
  * §17.4.1 functional forms: BOUND, IF, COALESCE, IN, NOT IN, `=`,
    `!=`, `<`, `>`, `<=`, `>=`, sameTerm;
  * §17.4.2 term-accessor / test forms: isIRI, isBlank, isLiteral,
    isNumeric, STR, LANG, DATATYPE, IRI, STRDT, STRLANG, plus the RDF
    1.2 direction family hasLANG, hasLANGDIR, LANGDIR, STRLANGDIR
    (RDF 1.2 Concepts §3.3);
  * §17.4.3 string functions: STRLEN, SUBSTR, UCASE, LCASE, STRSTARTS,
    STRENDS, CONTAINS, STRBEFORE, STRAFTER, CONCAT, ENCODE_FOR_URI,
    langMatches;
  * §17.4.4 numeric functions ABS, ROUND, CEIL, FLOOR and the §17.4.1
    arithmetic operators `+ - * /` over the promoted numeric types;
  * §17.4.5 the xsd:dateTime component accessors YEAR … SECONDS;
  * SPARQL 1.2 triple-term builtins TRIPLE/SUBJECT/PREDICATE/OBJECT/
    isTRIPLE (Query WD §17.4).

WHAT THIS FILE DELIBERATELY DOES NOT EVALUATE (each returns the
constructor-level `EvalResult.error`, which IS an operator's spec
behaviour when it cannot produce a value — never `sorry`, never a
`partial def`):
  * `Expr.regex` / `Expr.replace` — REGEX and REPLACE need an XPath
    regular-expression engine (§17.4.3.14/§17.4.3.15). In the F* tree
    those are host call-outs (`regex_match`, `regex_replace`); the Lean
    purity doctrine wants a pure regex matcher, which is a port of its
    own.
  * `Expr.existsPat` / `Expr.notExistsPat` — §18.6 EXISTS needs pattern
    evaluation against a graph, which sits above expressions. Wired as
    the optional `EvalEnv.existsHook`; with no hook the result is the
    error the F* evaluator also returns at this layer
    (`E_Exists _ -> ER_Error`, delegated to the pattern evaluator).
  * `Expr.aggregate` — aggregates are evaluated in the §18.5.1
    aggregation context over a solution GROUP, not per solution
    mapping. The F* arm is `E_Aggregate _ _ _ -> ER_Error` for exactly
    this reason; the port keeps that.
  * `Expr.md5` / `sha1` / `sha256` / `sha384` / `sha512` — §17.4.3.16
    hash builtins. The F* tree assumes them (`assume val hash_*`); the
    Lean purity doctrine forbids that, so they wait for a pure
    implementation rather than being faked.
  * `Expr.now` — §17.4.5.1 reads a clock. Modelled purely: the
    timestamp is an INPUT, `EvalEnv.now`; with none supplied the result
    is an error rather than an ambient effect.
  * `Expr.timezone` / `Expr.tz` — §17.4.5.8/9 timezone extraction; part
    of the date/time family the `dt_timezone`/`dt_tz` helpers cover in
    F*, deferred with the xsd:dateTime work.
  * §17.6 extension functions and every unrecognised `functionCall`
    IRI — offered to `EvalEnv.ext`; an unregistered IRI is a type
    error, which is precisely what §17.6 requires. BNODE(), UUID(),
    STRUUID(), RAND() live in that family in the F* tree and are
    effectful there; they stay unimplemented rather than pseudo-random.

Readability contract (as elsewhere in this port): every definition
cites the spec section it implements, and names track the spec's
vocabulary rather than implementation jargon.
-/
import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Datatype IRIs this file needs beyond `RDF.Core`'s set -/

/-- `xsd:float` — in `is_numeric_datatype`'s set alongside integer,
decimal and double (SPARQL 1.1 §17.1 operand types). -/
def xsdFloat : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#float", rfl⟩

/-- `xsd:dateTime` — the operand type of the §17.4.5 accessors. -/
def xsdDateTime : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#dateTime", rfl⟩

/-- SPARQL 1.1 §17.1: the numeric operand types. -/
def isNumericDatatype (dt : WfIri) : Bool :=
  dt == xsdInteger || dt == xsdDecimal || dt == xsdDouble || dt == xsdFloat

/-! ## Well-formed literal builders

`RDF.Core` carries the well-formedness rule `literalWf` in the type of
`WfLiteral`, so every literal an operator CONSTRUCTS has to come with
its proof. These three builders are the only ways this file makes one;
each discharges `literalWf` by kernel computation, so no operator arm
below has to reason about it. (The F* source builds bare records and
lets Z3 discharge the refinement; this is the same obligation, paid
once.) -/

/-- A literal with an explicit datatype. A request for `rdf:langString`
or `rdf:dirLangString` without a language tag is not well-formed, and
falls back to a plain `xsd:string` literal — the same rule the F*
`fn_strdt` applies (§17.4.2.3 STRDT). -/
def mkTypedLiteral (lex : String) (dt : WfIri) : WfLiteral :=
  if h : dt ≠ rdfLangString ∧ dt ≠ rdfDirLangString then
    ⟨{ lexicalForm := lex, datatype := dt, langTag := none, direction := none },
      by simp [literalWf, h.1, h.2]⟩
  else Literal.string lex

/-- A language-tagged literal — §17.4.2.4 STRLANG. -/
def mkLangLiteral (lex tag : String) : WfLiteral := Literal.langString lex tag

/-- A directional language-tagged literal (RDF 1.2 Concepts §3.3) —
SPARQL 1.2 STRLANGDIR. -/
def mkDirLangLiteral (lex tag : String) (d : TextDirection) : WfLiteral :=
  ⟨{ lexicalForm := lex, datatype := rdfDirLangString,
     langTag := some tag, direction := some d }, rfl⟩

/-! ## Operators — SPARQL 1.1 §17.4.1.7 (comparison) / §17.4.1 (arithmetic) -/

/-- The relational operators `=`, `!=`, `<`, `>`, `<=`, `>=`. -/
inductive CompOp where
  | eq | ne | lt | gt | le | ge
  deriving DecidableEq, Repr

/-- The arithmetic operators `+`, `-`, `*`, `/` (§17.4.1). -/
inductive ArithOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr

/-- Set functions (§18.5.1). Carried by the AST so a HAVING/SELECT
expression parses; evaluation belongs to the aggregation context. -/
inductive AggregateFn where
  | count | sum | min | max | avg
  | groupConcat (separator : Option String)
  | sample
  deriving DecidableEq, Repr

/-! ## The expression AST — SPARQL 1.1 §18.2

One constructor per §17 operator or function form, matching the F*
`expr` type constructor for constructor. `existsPat`/`notExistsPat`
carry a `GraphPattern` because §18.6 defines EXISTS over the algebra;
this is the only place expressions refer back to patterns. -/

inductive Expr where
  -- Primary expressions (§18.2)
  | var         (v : VarName)
  | iri         (i : WfIri)
  | lit         (l : WfLiteral)
  | boolLit     (b : Bool)
  | numericLit  (n : Int)            -- xsd:integer literal
  | decimalLit  (s : String)         -- xsd:decimal, lexical form
  | doubleLit   (s : String)         -- xsd:double, lexical form
  -- Arithmetic (§17.4.1)
  | arith       (op : ArithOp) (l r : Expr)
  | unaryMinus  (e : Expr)
  | unaryPlus   (e : Expr)
  -- Comparison (§17.4.1.7)
  | compare     (op : CompOp) (l r : Expr)
  -- Logical connectives (§17.3)
  | and         (l r : Expr)
  | or          (l r : Expr)
  | not         (e : Expr)
  -- Node type tests (§17.4.2)
  | isIri       (e : Expr)
  | isBlank     (e : Expr)
  | isLiteral   (e : Expr)
  | isNumeric   (e : Expr)
  -- Accessors (§17.4.2)
  | str         (e : Expr)
  | lang        (e : Expr)
  | datatype    (e : Expr)
  | iriFn       (e : Expr)           -- IRI() / URI()
  -- RDF 1.2 base-direction accessors (RDF 1.2 Concepts §3.3)
  | hasLang     (e : Expr)
  | hasLangDir  (e : Expr)
  | langDir     (e : Expr)
  -- Term constructors (§17.4.2)
  | strDt       (lex dt : Expr)
  | strLang     (lex tag : Expr)
  | strLangDir  (lex tag dir : Expr)
  -- BOUND (§17.4.1.1)
  | bound       (v : VarName)
  -- Functional forms (§17.4.1)
  | cond        (c t e : Expr)       -- IF(c, t, e)
  | coalesce    (es : List Expr)
  | inList      (e : Expr) (es : List Expr)
  | notInList   (e : Expr) (es : List Expr)
  -- String functions (§17.4.3)
  | strLen      (e : Expr)
  | substr      (e start : Expr) (len : Option Expr)
  | uCase       (e : Expr)
  | lCase       (e : Expr)
  | strStarts   (e pre : Expr)
  | strEnds     (e suf : Expr)
  | contains    (e sub : Expr)
  | strBefore   (e sep : Expr)
  | strAfter    (e sep : Expr)
  | concat      (es : List Expr)
  | encodeForUri (e : Expr)
  | replace     (e pat rep : Expr) (flags : Option Expr)   -- scoped out
  | regex       (e pat : Expr) (flags : Option Expr)       -- scoped out
  -- Numeric functions (§17.4.4)
  | abs         (e : Expr)
  | round       (e : Expr)
  | ceil        (e : Expr)
  | floor       (e : Expr)
  -- Hash functions (§17.4.3.16) — scoped out
  | md5         (e : Expr)
  | sha1        (e : Expr)
  | sha256      (e : Expr)
  | sha384      (e : Expr)
  | sha512      (e : Expr)
  -- Date/time functions (§17.4.5)
  | now
  | year        (e : Expr)
  | month       (e : Expr)
  | day         (e : Expr)
  | hours       (e : Expr)
  | minutes     (e : Expr)
  | seconds     (e : Expr)
  | timezone    (e : Expr)                                  -- scoped out
  | tz          (e : Expr)                                  -- scoped out
  -- RDF term identity (§17.4.1.2)
  | sameTerm    (l r : Expr)
  -- EXISTS / NOT EXISTS (§18.6) — needs pattern evaluation
  | existsPat    (p : GraphPattern)
  | notExistsPat (p : GraphPattern)
  -- Aggregates (§18.5.1) — evaluated over a group, not a solution
  | aggregate   (fn : AggregateFn) (distinct : Bool) (e : Expr)
  -- IRI-named function call (§17.6 extension point)
  | functionCall (i : WfIri) (args : List Expr)
  -- SPARQL 1.2 triple-term builtins (Query WD §17.4)
  | tripleTerm  (s p o : Expr)
  | ttSubject   (e : Expr)
  | ttPredicate (e : Expr)
  | ttObject    (e : Expr)
  | isTriple    (e : Expr)

/-! ## The value space of expression evaluation

Port of the F* `eval_result`. The three numeric constructors exist so
that a value keeps the numeric TYPE it was promoted to (§17.1's
xsd:integer / xsd:decimal / xsd:double lattice) without repeatedly
re-parsing a literal — the promoted-type discipline every operator arm
below has to honour (an operator that only looks at
`term (Term.literal _)` and forgets `num`/`dec`/`dbl`/`bool` is the
classic bug this shape is designed to make visible). -/

inductive EvalResult where
  | term  (t : Term)
  | bool  (b : Bool)
  | num   (n : Int)
  | dec   (s : String)
  | dbl   (s : String)
  | error
  deriving DecidableEq, Repr

/-- SPARQL 1.1 §17.2.2, "Effective Boolean Value" — the operand
mapping table, transcribed row for row:

| argument | EBV |
|---|---|
| xsd:boolean | its value (lexical `true`/`1`) |
| xsd:string / simple literal | false iff the lexical form is empty |
| numeric | false iff the value is `0` (or `NaN` for double) |
| anything else, or a type error | **type error** (`none`) |

A language-tagged literal is "any other argument": the table's String
row is the un-tagged case only, so `ebv` of a `rdf:langString` is a
type error and not `true`. Returning `Option Bool` rather than `Bool`
is what lets §17.3's connectives below stay error-PRESERVING. -/
def ebv : EvalResult → Option Bool
  | .bool b => some b
  | .num n  => some (n ≠ 0)
  | .dec s  => some (s ≠ "0" && s ≠ "0.0" && s ≠ "")
  | .dbl s  => some (s ≠ "0" && s ≠ "0.0" && s ≠ "NaN" && s ≠ "")
  | .term (.literal l) =>
      if l.val.datatype == xsdBoolean then
        some (l.val.lexicalForm == "true" || l.val.lexicalForm == "1")
      else if l.val.datatype == xsdString then
        some (l.val.lexicalForm.length > 0)
      else if isNumericDatatype l.val.datatype then
        some (l.val.lexicalForm ≠ "0" && l.val.lexicalForm ≠ "0.0" &&
              l.val.lexicalForm ≠ "")
      else none
  | .term _ => none
  | .error  => none

/-- §18.5 FILTER treats a type error and `false` alike (the row is
dropped either way), so call sites that only need "does this row
survive" collapse the error here. Call sites that must tell a type
error from a definite `false` — the §17.3 connectives — use `ebv`. -/
def ebvOrFalse (v : EvalResult) : Bool := (ebv v).getD false

/-! ### §17.3 — the error-tolerant, error-preserving truth tables

A determinate `false` operand makes `&&` false even when its
co-operand is a type error (error-TOLERANT); two operands that do not
dominate propagate the error rather than collapsing it
(error-PRESERVING). -/

/-- §17.3 logical-and table. -/
def boolAnd : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- §17.3 logical-or table. -/
def boolOr : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- §17.3 logical-not table: an error stays an error. -/
def boolNot : Option Bool → Option Bool
  | some b => some (!b)
  | none   => none

/-! ### Views over an `EvalResult` -/

/-- The RDF term a value denotes — §18.5 BIND / SELECT projection needs
this to turn an expression result back into a binding. A type error
denotes no term, which is why BIND leaves the variable unbound. Port of
`er_to_term`. -/
def EvalResult.toTerm? : EvalResult → Option Term
  | .term t     => some t
  | .bool true  => some (.literal (mkTypedLiteral "true" xsdBoolean))
  | .bool false => some (.literal (mkTypedLiteral "false" xsdBoolean))
  | .num n      => some (.literal (mkTypedLiteral (toString n) xsdInteger))
  | .dec s      => some (.literal (mkTypedLiteral s xsdDecimal))
  | .dbl s      => some (.literal (mkTypedLiteral s xsdDouble))
  | .error      => none

/-- The string a value presents to a string function (port of
`er_to_string`): a literal's lexical form, an IRI's string, or the
canonical lexical form of a promoted number/boolean. Blank nodes,
triple terms and errors have none. -/
def EvalResult.toString? : EvalResult → Option String
  | .term (.literal l) => some l.val.lexicalForm
  | .term (.iri i)     => some i.val
  | .num n             => some (toString n)
  | .dec s             => some s
  | .dbl s             => some s
  | .bool b            => some (if b then "true" else "false")
  | _                  => none

/-- Lexical form + language tag + datatype, for the string functions
that PRESERVE their argument's metadata (§17.4.3: SUBSTR, UCASE,
LCASE, STRBEFORE, STRAFTER, CONCAT). Port of `er_string_info`. -/
def EvalResult.stringInfo? : EvalResult → Option (String × Option String × WfIri)
  | .term (.literal l) => some (l.val.lexicalForm, l.val.langTag, l.val.datatype)
  | .num n             => some (toString n, none, xsdInteger)
  | .dec s             => some (s, none, xsdDecimal)
  | .dbl s             => some (s, none, xsdDouble)
  | .bool b            => some ((if b then "true" else "false"), none, xsdBoolean)
  | _                  => none

/-- The base direction a value carries, if any (RDF 1.2 Concepts §3.3).
Kept separate from `stringInfo?` because only CONCAT is specified to
preserve direction. Port of `er_direction`. -/
def EvalResult.direction? : EvalResult → Option TextDirection
  | .term (.literal l) => l.val.direction
  | _                  => none

/-- A simple literal result (`xsd:string`, no tag) — the return shape of
STR, ENCODE_FOR_URI, LANG, LANGDIR. -/
def erString (s : String) : EvalResult := .term (.literal (Literal.string s))

/-- Rebuild a string result carrying its argument's metadata forward
(port of `er_string_preserve`): a language tag survives only on
`rdf:langString`, a datatype survives only when it is neither of the
language-tagged datatypes; everything else degrades to a simple
literal. -/
def erStringPreserve (s : String) (lang : Option String) (dt : WfIri) : EvalResult :=
  match lang with
  | none =>
      if dt != rdfLangString && dt != rdfDirLangString then
        .term (.literal (mkTypedLiteral s dt))
      else erString s
  | some l =>
      if dt == rdfLangString then .term (.literal (mkLangLiteral s l))
      else erString s

/-! ## Integer helpers

The F* source's arithmetic runs on unbounded `int`. Lean's `Int` is the
same; the one place the two languages could silently disagree is the
rounding direction of `/`, so this port never writes `/` on `Int` and
uses the explicit truncate-toward-zero definition instead — the
behaviour of F*'s `op_Division` and of its OCaml extraction. -/

/-- Truncating (toward zero) integer division. -/
def intDivT (a b : Int) : Int :=
  if b = 0 then 0
  else
    let q : Int := ((a.natAbs / b.natAbs : Nat) : Int)
    if (decide (a < 0)) == (decide (b < 0)) then q else -q

/-- `10 ^ n`, as the F* `pow10`. -/
def pow10 : Nat → Int
  | 0 => 1
  | n + 1 => 10 * pow10 n

/-- Three-way integer comparison: `-1`, `0`, `1` (port of `int_compare`). -/
def intCompare (a b : Int) : Int :=
  if a < b then -1 else if a = b then 0 else 1

/-- §17.4.1.7: turn a three-way comparison into the operator's Boolean
(port of `apply_comp_op`). -/
def applyCompOp (cmp : Int) : CompOp → Bool
  | .eq => cmp == 0
  | .ne => cmp != 0
  | .lt => cmp < 0
  | .gt => cmp > 0
  | .le => cmp ≤ 0
  | .ge => cmp ≥ 0

/-! ## String helpers (character-list based, matching the F* source)

Everything works on `String.toList` (codepoints), because the F* tree's
own helpers do and because byte-level operations mis-handle non-ASCII —
an error this project has paid for on the OCaml side. -/

def listIsPrefix : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as1, b :: bs1 => a == b && listIsPrefix as1 bs1

def listContainsSublist (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | h :: t => listIsPrefix needle (h :: t) || listContainsSublist needle t

def strStartsWith (s pre : String) : Bool :=
  listIsPrefix pre.toList s.toList

def strEndsWith (s suffix : String) : Bool :=
  listIsPrefix suffix.toList.reverse s.toList.reverse

def strContains (s sub : String) : Bool :=
  listContainsSublist sub.toList s.toList

/-- Index of the first occurrence of `needle`, as a codepoint offset. -/
def findSubstringPos (needle : List Char) : List Char → Nat → Option Nat
  | [], pos => if needle.isEmpty then some pos else none
  | h :: t, pos =>
      if listIsPrefix needle (h :: t) then some pos
      else findSubstringPos needle t (pos + 1)

/-- §17.4.3.13 STRBEFORE's string part: everything before the first
occurrence, or `""` when there is none. -/
def strBeforeRaw (s arg : String) : String :=
  if arg.length = 0 then ""
  else match findSubstringPos arg.toList s.toList 0 with
    | none => ""
    | some pos => String.ofList (s.toList.take pos)

/-- §17.4.3.14 STRAFTER's string part: everything after the first
occurrence, or `""` when there is none. -/
def strAfterRaw (s arg : String) : String :=
  if arg.length = 0 then s
  else match findSubstringPos arg.toList s.toList 0 with
    | none => ""
    | some pos => String.ofList (s.toList.drop (pos + arg.length))

/-- §17.4.3.3 SUBSTR: 1-BASED start index, optional length; positions
outside the string clamp rather than erroring. Port of
`fn_substr_spec` ∘ `string_substring`. -/
def substrSpec (s : String) (start : Nat) (len : Option Nat) : String :=
  let idx := if start > 0 then start - 1 else 0
  let cs := s.toList
  let slen := cs.length
  let start' := if idx ≥ slen then slen else idx
  let actualLen :=
    match len with
    | some l => if start' + l > slen then slen - start' else l
    | none   => slen - start'
  if actualLen = 0 || start' ≥ slen then ""
  else String.ofList ((cs.drop start').take actualLen)

/-! ### §17.4.3.15 ENCODE_FOR_URI -/

def nibbleToHex (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n - 10 + 65)

/-- RFC 3986 unreserved characters — the set ENCODE_FOR_URI leaves
alone. -/
def isUriUnreserved (c : Char) : Bool :=
  let code := c.toNat
  (code ≥ 65 && code ≤ 90) || (code ≥ 97 && code ≤ 122) ||
  (code ≥ 48 && code ≤ 57) ||
  code == 45 || code == 95 || code == 46 || code == 126

def percentEncodeByte (b : Nat) : List Char :=
  ['%', nibbleToHex (b / 16), nibbleToHex (b % 16)]

/-- Percent-encode one codepoint as its UTF-8 bytes. -/
def percentEncodeChar (c : Char) : List Char :=
  let code := c.toNat
  if code < 0x80 then percentEncodeByte code
  else if code < 0x800 then
    percentEncodeByte (0xC0 + code / 64) ++ percentEncodeByte (0x80 + code % 64)
  else if code < 0x10000 then
    percentEncodeByte (0xE0 + code / 4096) ++
    percentEncodeByte (0x80 + (code / 64) % 64) ++
    percentEncodeByte (0x80 + code % 64)
  else
    percentEncodeByte (0xF0 + code / 262144) ++
    percentEncodeByte (0x80 + (code / 4096) % 64) ++
    percentEncodeByte (0x80 + (code / 64) % 64) ++
    percentEncodeByte (0x80 + code % 64)

def encodeUriChars : List Char → List Char
  | [] => []
  | c :: rest =>
      if isUriUnreserved c then c :: encodeUriChars rest
      else percentEncodeChar c ++ encodeUriChars rest

def strEncodeUri (s : String) : String := String.ofList (encodeUriChars s.toList)

/-! ### §17.4.3.10 langMatches — RFC 4647 basic filtering -/

/-- `langMatches(tag, range)`: `"*"` matches any non-empty tag;
otherwise the tag matches the range exactly or as an extended
sub-tag, comparing case-insensitively (BCP 47 tags are ASCII, so
Lean's `String.toLower` is exact here). Port of
`fn_langMatches_spec`. -/
def fnLangMatches (tag range : String) : Bool :=
  if range == "*" then tag.length > 0
  else
    let ltag := tag.toLower
    let lrange := range.toLower
    ltag == lrange || strStartsWith ltag (lrange ++ "-")

/-! ## The scaled-decimal numeric model — SPARQL 1.1 §17.1 / XSD 1.1

A value is `mantissa / 10 ^ scale`. Every xsd:decimal lexical form and
every FINITE xsd:double lexical form is EXACT in this model, so `=`,
`<` and `+ - *` over them are exact too — the same representation the
F* tree uses (`parse_to_scaled` / `parse_double_to_scaled`), and the
reason `1 = 1.0` and `1 = 1.0E0` decide correctly without floating
point. Consequences worth stating: `INF`/`-INF`/`NaN` have no scaled
value (they parse to `none`, hence a type error), and `/` is
approximated at a fixed 10-digit scale exactly as the F* source does. -/

/-- A number as `mantissa / 10 ^ scale`. -/
structure Scaled where
  mantissa : Int
  scale : Nat
  deriving DecidableEq, Repr

/-- The three numeric types of §17.1's promotion lattice. -/
inductive NumKind where
  | int | dec | dbl
  deriving DecidableEq, Repr

/-- §17.1 numeric type promotion: double dominates decimal dominates
integer (port of `promote_kind`). -/
def promoteKind : NumKind → NumKind → NumKind
  | .dbl, _ | _, .dbl => .dbl
  | .dec, _ | _, .dec => .dec
  | _, _ => .int

def charToDigit (c : Char) : Option Nat :=
  let n := c.toNat
  if n ≥ 48 && n ≤ 57 then some (n - 48) else none

def parseIntChars : List Char → Int → Option Int
  | [], acc => some acc
  | c :: rest, acc =>
      match charToDigit c with
      | some d => parseIntChars rest (10 * acc + (d : Int))
      | none => none

/-- Parse an XSD integer lexical form (port of `parse_int_string`). -/
def parseIntString (s : String) : Option Int :=
  match s.toList with
  | [] => none
  | c :: rest =>
      if c == '-' then (parseIntChars rest 0).map (fun n => -n)
      else parseIntChars (c :: rest) 0

/-- Split a decimal lexical form into integer part, fraction digits and
"was there a point" (port of `split_decimal`). -/
def splitDecimal (s : String) : Option Int × List Char × Bool :=
  let chars := s.toList
  let before := chars.takeWhile (fun c => c != '.')
  match chars.dropWhile (fun c => c != '.') with
  | [] => (parseIntString (String.ofList before), [], false)
  | _ :: frac => (parseIntString (String.ofList before), frac, true)

/-- `"3.5" ↦ 35/10¹`, `"100" ↦ 100/10⁰`, `"-2.2" ↦ -22/10¹`. Port of
`parse_to_scaled`; note the explicit negative-zero handling ("-0.5"
has integer part `0` but is negative). -/
def parseToScaled (s : String) : Option Scaled :=
  let (ip, frac, _) := splitDecimal s
  match ip with
  | none => none
  | some intPart =>
      let scale := frac.length
      if scale = 0 then some ⟨intPart, 0⟩
      else
        match parseIntString (String.ofList frac) with
        | none => some ⟨intPart * pow10 scale, scale⟩
        | some f =>
            let isNeg := intPart < 0 || (intPart = 0 && strStartsWith s "-")
            let absScaled := (intPart.natAbs : Int) * pow10 scale + (f.natAbs : Int)
            some ⟨if isNeg then -absScaled else absScaled, scale⟩

/-- `"1.0E2" ↦ 100/10⁰`, `"2.0E-1" ↦ 20/10²`. Port of
`parse_double_to_scaled`. A lexical form with no exponent falls
through to `parseToScaled`, which is why double-aware parsing must be
TRIED FIRST on a value that might carry E-notation. -/
def parseDoubleToScaled (s : String) : Option Scaled :=
  let chars := s.toList
  let notE := fun (c : Char) => c != 'E' && c != 'e'
  let beforeE := chars.takeWhile notE
  match chars.dropWhile notE with
  | [] => parseToScaled s
  | _ :: expChars =>
      match parseToScaled (String.ofList beforeE), parseIntString (String.ofList expChars) with
      | some m, some exp =>
          let effectiveScale : Int := (m.scale : Int) - exp
          if effectiveScale ≤ 0 then
            some ⟨m.mantissa * pow10 (-effectiveScale).toNat, 0⟩
          else some ⟨m.mantissa, effectiveScale.toNat⟩
      | _, _ => none

def makeZeros : Nat → String
  | 0 => ""
  | n + 1 => "0" ++ makeZeros n

def padLeftZeros (s : String) (target : Nat) : String :=
  if s.length ≥ target then s else makeZeros (target - s.length) ++ s

/-- `(67, 1) ↦ "6.7"`, `(2220, 3) ↦ "2.220"` (port of
`format_scaled_value`). -/
def formatScaledValue (value : Int) (scale : Nat) : String :=
  if scale = 0 then toString value
  else
    let absVal : Int := (value.natAbs : Int)
    let p := pow10 scale
    let intPart := intDivT absVal p
    let fracPart := absVal - intPart * p
    let fracStr := padLeftZeros (toString fracPart) scale
    (if value < 0 then "-" else "") ++ toString intPart ++ "." ++ fracStr

def stripTrailingZerosChars (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | _ =>
      let stripped := cs.reverse.dropWhile (fun c => c == '0')
      if stripped.isEmpty then ['0'] else stripped.reverse

/-- Canonicalise an xsd:decimal lexical form, keeping at least one
fraction digit (port of `strip_trailing_decimal_zeros`). -/
def stripTrailingDecimalZeros (s : String) : String :=
  let chars := s.toList
  let beforeDot := chars.takeWhile (fun c => c != '.')
  match chars.dropWhile (fun c => c != '.') with
  | [] => s
  | _ :: frac =>
      String.ofList beforeDot ++ "." ++ String.ofList (stripTrailingZerosChars frac)

/-- Decimal digit count, structurally recursive on an explicit fuel
argument (the fuel starts at `n`, which always exceeds the digit
count). The F* source uses well-founded recursion on `n / 10`; fuel
keeps this port structural, so `#guard` can evaluate it. -/
def countDigitsFuel : Nat → Nat → Nat
  | 0, _ => 1
  | _ + 1, n => if n < 10 then 1 else 1 + countDigitsFuel n (n / 10)

def countDigits (n : Nat) : Nat := countDigitsFuel n n

/-- xsd:double canonical lexical form: `(32100, 0) ↦ "3.21E4"`,
`(20, 2) ↦ "2.0E-1"` (port of `format_as_double`). -/
def formatAsDouble (value : Int) (scale : Nat) : String :=
  if value = 0 then "0E0"
  else
    let absVal := value.natAbs
    let ndigits := countDigits absVal
    let exp : Int := ((ndigits - 1 : Nat) : Int) - (scale : Int)
    let mantissaStr := formatScaledValue (absVal : Int) (ndigits - 1)
    let stripped := stripTrailingDecimalZeros mantissaStr
    let withDot := if strContains stripped "." then stripped else stripped ++ ".0"
    (if value < 0 then "-" else "") ++ withDot ++ "E" ++ toString exp

/-- The scaled value and numeric type a result denotes; `none` for
anything non-numeric (port of `er_to_numeric`). -/
def EvalResult.toNumeric? : EvalResult → Option (Scaled × NumKind)
  | .num n => some (⟨n, 0⟩, .int)
  | .dec s => (parseToScaled s).map (fun v => (v, .dec))
  | .dbl s => (parseDoubleToScaled s).map (fun v => (v, .dbl))
  | _ => none

/-- Three-way comparison of two scaled values, by normalising to the
larger scale (port of `numeric_compare`'s core). -/
def Scaled.cmp (a b : Scaled) : Int :=
  if a.scale ≥ b.scale then
    intCompare a.mantissa (b.mantissa * pow10 (a.scale - b.scale))
  else
    intCompare (a.mantissa * pow10 (b.scale - a.scale)) b.mantissa

/-- Numeric comparison of two results; `none` if either is not numeric
(port of `numeric_compare`). -/
def numericCompare (a b : EvalResult) : Option Int :=
  match a.toNumeric?, b.toNumeric? with
  | some (x, _), some (y, _) => some (x.cmp y)
  | _, _ => none

/-- Sum at the larger scale (port of `add_scaled`). -/
def Scaled.add (a b : Scaled) : Scaled :=
  if a.scale ≥ b.scale then
    ⟨a.mantissa + b.mantissa * pow10 (a.scale - b.scale), a.scale⟩
  else
    ⟨a.mantissa * pow10 (b.scale - a.scale) + b.mantissa, b.scale⟩

def Scaled.sub (a b : Scaled) : Scaled :=
  if a.scale ≥ b.scale then
    ⟨a.mantissa - b.mantissa * pow10 (a.scale - b.scale), a.scale⟩
  else
    ⟨a.mantissa * pow10 (b.scale - a.scale) - b.mantissa, b.scale⟩

/-- Exact product: scales add. -/
def Scaled.mul (a b : Scaled) : Scaled :=
  ⟨a.mantissa * b.mantissa, a.scale + b.scale⟩

/-- §17.4.1 `/`: division by zero is a type error, and the quotient is
computed at a fixed extra precision of 10 fraction digits — the F*
source's `extra = 10` (exact division is not always representable in
the scaled model). -/
def Scaled.div? (a b : Scaled) : Option Scaled :=
  if b.mantissa = 0 then none
  else
    let extra : Nat := 10
    let extended := a.mantissa * pow10 (b.scale + extra)
    let divisor := b.mantissa * pow10 a.scale
    if divisor = 0 then none
    else some ⟨intDivT extended divisor, extra⟩

/-- Present a scaled result in its promoted type (port of
`format_numeric_result`): an integer result truncates, a decimal
result is canonicalised, a double result goes to E-notation. -/
def formatNumericResult (v : Scaled) : NumKind → EvalResult
  | .int => if v.scale = 0 then .num v.mantissa else .num (intDivT v.mantissa (pow10 v.scale))
  | .dec => .dec (stripTrailingDecimalZeros (formatScaledValue v.mantissa v.scale))
  | .dbl => .dbl (formatAsDouble v.mantissa v.scale)

/-- §17.4.1 integer arithmetic. Note `integer / integer` is an
xsd:DECIMAL, not an integer (port of `eval_arith_int`). -/
def evalArithInt (op : ArithOp) (a b : Int) : EvalResult :=
  match op with
  | .add => .num (a + b)
  | .sub => .num (a - b)
  | .mul => .num (a * b)
  | .div =>
      if b = 0 then .error
      else formatNumericResult
             (⟨intDivT (a * pow10 16) b, 16⟩ : Scaled) .dec

/-! ## §17.4.1.7 value comparison and RDF-term equality -/

/-- Promote a literal to the numeric/boolean result it denotes, so that
comparison sees VALUES rather than lexical forms (port of
`literal_promote`). -/
def literalPromote (l : WfLiteral) : EvalResult :=
  if l.val.datatype == xsdInteger then
    match parseIntString l.val.lexicalForm with
    | some n => .num n
    | none => .term (.literal l)
  else if l.val.datatype == xsdDecimal then .dec l.val.lexicalForm
  else if l.val.datatype == xsdDouble || l.val.datatype == xsdFloat then
    .dbl l.val.lexicalForm
  else if l.val.datatype == xsdBoolean then
    .bool (l.val.lexicalForm == "true" || l.val.lexicalForm == "1")
  else .term (.literal l)

/-- Literal equality that compares numeric literals by VALUE and
everything else by the engine's term equality (port of
`literal_value_eq_numeric`). -/
def literalValueEqNumeric (l1 l2 : WfLiteral) : Bool :=
  if isNumericDatatype l1.val.datatype || isNumericDatatype l2.val.datatype then
    match numericCompare (literalPromote l1) (literalPromote l2) with
    | some c => c == 0
    | none => false
  else l1.val.eqb l2.val

/-- RDF 1.2 triple-term VALUE equality, used by `=` (op:triple):
subject and predicate compare structurally, the object recurses and
compares numeric literals by value. Deliberately NOT `sameTerm`:
`<<( :a :b 123 )>> = <<( :a :b 123.0 )>>` holds under `=` but not
under `sameTerm`. Port of `triple_term_value_eq`. -/
def tripleTermValueEq : Term → Term → Bool
  | .iri i1, .iri i2 => i1 == i2
  | .bnode b1, .bnode b2 => b1 == b2
  | .literal l1, .literal l2 => literalValueEqNumeric l1 l2
  | .tripleTerm s1 p1 o1, .tripleTerm s2 p2 o2 =>
      s1.eqb s2 && p1 == p2 && tripleTermValueEq o1 o2
  | _, _ => false

/-- Lexicographic codepoint comparison of two strings, as three-way
(the F* source's `String.compare`). -/
def listCharCompare : List Char → List Char → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as1, b :: bs1 =>
      let c := intCompare (a.toNat : Int) (b.toNat : Int)
      if c == 0 then listCharCompare as1 bs1 else c

def strCompare (a b : String) : Int := listCharCompare a.toList b.toList

/-- §17.4.1.7 operator mapping for `= != < > <= >=`, with §17.1's
cross-type numeric promotion. `none` is a type error. Reading the arms
in order: any two numerics compare by value; two booleans compare
false < true; two IRIs and two same-datatype literals compare by
lexical order — and two literals of DIFFERENT datatypes are a type
error, which is what makes `=` open-world on unknown datatypes; two
triple terms support only `=`/`!=` (they have no order). Port of
`value_compare`. Blank nodes fall to the final catch-all: a type
error, exactly as the F* source. -/
def valueCompare (v1 v2 : EvalResult) (op : CompOp) : Option Bool :=
  match v1, v2 with
  | .num _, .num _ | .num _, .dec _ | .num _, .dbl _
  | .dec _, .num _ | .dec _, .dec _ | .dec _, .dbl _
  | .dbl _, .num _ | .dbl _, .dec _ | .dbl _, .dbl _ =>
      (numericCompare v1 v2).map (fun c => applyCompOp c op)
  | .bool a, .bool b =>
      some (applyCompOp (intCompare (if a then 1 else 0) (if b then 1 else 0)) op)
  | .term (.iri i1), .term (.iri i2) =>
      some (applyCompOp (strCompare i1.val i2.val) op)
  | .term (.literal l1), .term (.literal l2) =>
      if l1.val.datatype == l2.val.datatype then
        if l1.val.langTag == l2.val.langTag then
          some (applyCompOp (strCompare l1.val.lexicalForm l2.val.lexicalForm) op)
        else
          match op with
          | .eq => some false
          | .ne => some true
          | _ => none
      else none
  | .term (.tripleTerm s1 p1 o1), .term (.tripleTerm s2 p2 o2) =>
      match op with
      | .eq => some (tripleTermValueEq (.tripleTerm s1 p1 o1) (.tripleTerm s2 p2 o2))
      | .ne => some (!tripleTermValueEq (.tripleTerm s1 p1 o1) (.tripleTerm s2 p2 o2))
      | _ => none
  | _, _ => none

/-! ## §17.4.2 node tests and accessors -/

def fnIsIri : EvalResult → EvalResult
  | .term (.iri _) => .bool true
  | .error => .error
  | _ => .bool false

def fnIsBlank : EvalResult → EvalResult
  | .term (.bnode _) => .bool true
  | .error => .error
  | _ => .bool false

def fnIsLiteral : EvalResult → EvalResult
  | .term (.literal _) => .bool true
  | .num _ | .dec _ | .dbl _ | .bool _ => .bool true
  | .error => .error
  | _ => .bool false

def fnIsNumeric : EvalResult → EvalResult
  | .num _ | .dec _ | .dbl _ => .bool true
  | .term (.literal l) => .bool (isNumericDatatype l.val.datatype)
  | .error => .error
  | _ => .bool false

/-- §17.4.2.5 STR. Not defined on a triple term (which is neither
literal nor IRI). -/
def fnStr : EvalResult → EvalResult
  | .term (.iri i) => erString i.val
  | .term (.literal l) => erString l.val.lexicalForm
  | .term (.bnode b) => erString b
  | .num n => erString (toString n)
  | .dec s => erString s
  | .dbl s => erString s
  | .bool b => .term (.literal (mkTypedLiteral (if b then "true" else "false") xsdBoolean))
  | .term (.tripleTerm _ _ _) => .error
  | .error => .error

/-- §17.4.2.6 LANG: the empty string for an untagged literal, a type
error for a non-literal. -/
def fnLang : EvalResult → EvalResult
  | .term (.literal l) => erString (l.val.langTag.getD "")
  | .num _ | .dec _ | .dbl _ | .bool _ => erString ""
  | _ => .error

/-- §17.4.2.7 DATATYPE. -/
def fnDatatype : EvalResult → EvalResult
  | .term (.literal l) => .term (.iri l.val.datatype)
  | .num _ => .term (.iri xsdInteger)
  | .dec _ => .term (.iri xsdDecimal)
  | .dbl _ => .term (.iri xsdDouble)
  | .bool _ => .term (.iri xsdBoolean)
  | _ => .error

/-- RDF 1.2 `hasLANG(term)` — a presence test over ANY value, so an IRI
argument answers `false` rather than erroring. -/
def fnHasLang : EvalResult → EvalResult
  | .error => .error
  | .term (.literal l) => .bool l.val.langTag.isSome
  | _ => .bool false

/-- RDF 1.2 `hasLANGDIR(term)`. -/
def fnHasLangDir : EvalResult → EvalResult
  | .error => .error
  | .term (.literal l) => .bool l.val.direction.isSome
  | _ => .bool false

def textDirectionToString : TextDirection → String
  | .ltr => "ltr"
  | .rtl => "rtl"

/-- Strict, lowercase-only (RDF 1.2): `STRLANGDIR(_, _, "LTR")` is an
error, matching the W3C lang-basedir fixture. -/
def parseTextDirection (s : String) : Option TextDirection :=
  if s == "ltr" then some .ltr else if s == "rtl" then some .rtl else none

/-- RDF 1.2 `LANGDIR(term)` — mirrors LANG exactly. -/
def fnLangDir : EvalResult → EvalResult
  | .term (.literal l) =>
      erString (match l.val.direction with
                | some d => textDirectionToString d
                | none => "")
  | .num _ | .dec _ | .dbl _ | .bool _ => erString ""
  | _ => .error

/-! ### §17.4.5 xsd:dateTime component accessors

The accessors read the canonical lexical form positionally, exactly as
the F* `dt_*` helpers do. TIMEZONE and TZ are not ported (see the
module banner). -/

/-- The xsd:dateTime lexical form behind a value, if it has one. -/
def erToDateTimeLex : EvalResult → Option String
  | .term (.literal l) =>
      if l.val.datatype == xsdDateTime then some l.val.lexicalForm else none
  | _ => none

/-- Positional substring of a lexical form, by codepoint offset. -/
def lexSlice (s : String) (from_ len : Nat) : String :=
  String.ofList ((s.toList.drop from_).take len)

def dtYear (s : String) : Option Int :=
  if s.length < 4 then none else parseIntString (lexSlice s 0 4)
def dtMonth (s : String) : Option Int :=
  if s.length < 7 then none else parseIntString (lexSlice s 5 2)
def dtDay (s : String) : Option Int :=
  if s.length < 10 then none else parseIntString (lexSlice s 8 2)
def dtHours (s : String) : Option Int :=
  if s.length < 13 then none else parseIntString (lexSlice s 11 2)
def dtMinutes (s : String) : Option Int :=
  if s.length < 16 then none else parseIntString (lexSlice s 14 2)

/-- SECONDS returns an xsd:decimal (fractional seconds are in scope). -/
def dtSeconds (s : String) : Option String :=
  if s.length < 19 then none
  else
    let after := s.toList.drop 17
    let secChars := after.takeWhile (fun c => c != 'Z' && c != '+' && c != '-')
    if secChars.isEmpty then none else some (String.ofList secChars)

/-! ### §17.4.4 numeric functions -/

def allZeros (cs : List Char) : Bool := cs.all (fun c => c == '0')

/-- FLOOR on a decimal lexical form (port of `int_floor`). -/
def lexFloor (s : String) : Int :=
  let (ip, frac, hasDot) := splitDecimal s
  match ip with
  | none => 0
  | some n => if !hasDot || allZeros frac then n else if n ≥ 0 then n else n - 1

/-- CEIL on a decimal lexical form (port of `int_ceil`). -/
def lexCeil (s : String) : Int :=
  let (ip, frac, hasDot) := splitDecimal s
  match ip with
  | none => 0
  | some n => if !hasDot || allZeros frac then n else if n ≥ 0 then n + 1 else n

/-- ROUND, half away from zero (port of `int_round`). -/
def lexRound (s : String) : Int :=
  let (ip, frac, hasDot) := splitDecimal s
  match ip with
  | none => 0
  | some n =>
      if !hasDot || frac.isEmpty || allZeros frac then n
      else match frac.head? with
        | some c => if c.toNat ≥ 53 then (if n ≥ 0 then n + 1 else n - 1) else n
        | none => n

/-! ## The evaluation environment

The F* evaluator reaches for the host through `assume val`s (a clock,
an extension-function registry, a regex engine). Lean has no
`assume val`, and this project's purity doctrine says the answer is
PARAMETERISATION: what the host would supply becomes an explicit
input, so the semantics stays a total function of its arguments and
real I/O lives in `IO` at the executable edge only. -/

structure EvalEnv where
  /-- §17.6 extension functions: an IRI-named function the host
  registers. Absent (the default) means every unregistered IRI is a
  type error — which is the §17.6 requirement, not a shortcut. -/
  ext : String → List EvalResult → Option EvalResult := fun _ _ => none
  /-- §18.6 EXISTS: pattern evaluation, supplied by the layer above
  expressions. Absent means EXISTS is a type error at this layer. -/
  existsHook : Option (GraphPattern → Binding → Bool) := none
  /-- §17.4.5.1 NOW(): the query's execution timestamp as an
  xsd:dateTime lexical form. Read once, at the edge, and passed in —
  never an ambient clock call. -/
  now : Option String := none
  /-- SPARQL 1.1 Federated Query §2 SERVICE: the endpoint IRI → graph
  map. The F* tree reaches the same information through the
  `service_endpoint_lookup` `assume val`; here it is an ordinary input,
  so SERVICE evaluation stays a total function of its arguments. An
  endpoint absent from this list is an unreachable endpoint, which is
  what SILENT is defined against. -/
  services : List (Iri × Graph) := []

/-- Resolve a SERVICE endpoint IRI to the graph it serves. -/
def EvalEnv.resolveService (env : EvalEnv) (i : Iri) : Option Graph :=
  match env.services.find? (fun p => p.1 == i) with
  | some p => some p.2
  | none   => none

/-- The environment with no host services: extension functions error,
EXISTS errors, NOW errors. -/
def emptyEnv : EvalEnv := {}

/-- The IRI the F* evaluator dispatches `langMatches` on. -/
def langMatchesIri : WfIri :=
  ⟨"http://www.w3.org/2005/xpath-functions#langMatches", rfl⟩

/-! ### CONCAT — §17.4.3.12

CONCAT keeps a language tag (and, RDF 1.2, a base direction) only when
EVERY argument agrees on it; any disagreement drops to `xsd:string`.
The single-argument case is handled explicitly because a fold that
starts from `""` would lose the tag — the recursive-base-case bug this
project has hit before. -/
def concatResults : List EvalResult → EvalResult
  | [] => erString ""
  | [v] =>
      match v.stringInfo? with
      | none => .error
      | some (s, lang, dt) =>
          match lang, v.direction? with
          | some l1, some d => .term (.literal (mkDirLangLiteral s l1 d))
          | _, _ => erStringPreserve s lang dt
  | v :: rest =>
      match v.stringInfo? with
      | none => .error
      | some (s, lang, dt) =>
          match concatResults rest with
          | .term (.literal l) =>
              let combined := s ++ l.val.lexicalForm
              match lang, l.val.langTag with
              | some l1, some l2 =>
                  if l1.toLower == l2.toLower then
                    match v.direction?, l.val.direction with
                    | some d1, some d2 =>
                        if d1 == d2 then .term (.literal (mkDirLangLiteral combined l1 d1))
                        else erString combined
                    | none, none => .term (.literal (mkLangLiteral combined l1))
                    | _, _ => erString combined
                  else erString combined
              | none, none =>
                  if dt == l.val.datatype then
                    .term (.literal (mkTypedLiteral combined dt))
                  else erString combined
              | _, _ => erString combined
          | _ => .error

/-- §17.4.3.3 SUBSTR applied to arguments that are already evaluated.
Split out of the evaluator so that each evaluator arm stays a plain
structural match — which is what lets Lean generate the equation
lemmas the proofs in `ExprTheorems` rewrite with. -/
def substrResult (v1 v2 : EvalResult) (vlen : Option EvalResult) : EvalResult :=
  match v1.stringInfo?, v2 with
  | some (s, tg, dt), .num start =>
      if start < 0 then .error
      else
        let lenVal :=
          match vlen with
          | some (.num n) => if n ≥ 0 then some n.toNat else none
          | _ => none
        erStringPreserve (substrSpec s start.toNat lenVal) tg dt
  | _, _ => .error

/-- §17.4.1.3 COALESCE: the first argument that is not a type error. -/
def coalesceResults : List EvalResult → EvalResult
  | [] => .error
  | .error :: rest => coalesceResults rest
  | v :: _ => v

/-- §17.4.1.9 IN: `=` against each element in turn. Following the F*
source, a comparison that ERRORS is treated as "no match" rather than
poisoning the whole test, so `IN` answers `false` instead of erroring
when nothing matches. -/
def inResults (v : EvalResult) : List EvalResult → EvalResult
  | [] => .bool false
  | w :: rest =>
      match valueCompare v w .eq with
      | some true => .bool true
      | _ => inResults v rest

/-- §17.4.3.13/§17.4.3.14 argument compatibility for STRBEFORE and
STRAFTER: the two arguments must be plain-string compatible, or agree
on their language tag. -/
def strBeforeAfterCompatible
    (lang1 : Option String) (dt1 : WfIri)
    (lang2 : Option String) (dt2 : WfIri) : Bool :=
  (lang1.isNone && lang2.isNone) ||
  (lang1.isNone && dt1 == xsdString && lang2.isNone && dt2 == xsdString) ||
  (lang1.isSome && lang2.isNone && (dt2 == xsdString || dt2 == rdfLangString)) ||
  (lang1.isNone && dt1 == xsdString && lang2.isSome) ||
  (lang1.isSome && lang2.isSome && lang1 == lang2)

/-! ## The evaluator — SPARQL 1.1 §17

`Expr.evalIn env mu e` is TOTAL: every operator either produces a value
or produces `EvalResult.error`, the spec's type error. There is no
`partial def`, no fuel, and no escape hatch; the recursion is
structural on the expression tree, with `evalArgs` handling the
argument LISTS of COALESCE, IN, NOT IN, CONCAT and function calls. -/

mutual

/-- Evaluate one expression under a solution mapping. Port of
`eval_expr_with_base` (with the BASE-IRI parameter dropped — see the
deviation note on `Expr.iriFn`). -/
def Expr.evalIn (env : EvalEnv) (mu : Binding) : Expr → EvalResult
  -- §18.2 primary expressions. A bound variable holding a numeric or
  -- boolean literal is PROMOTED here, so `?x = 1` compares values.
  | .var v =>
      match mu.lookup v with
      | some (.literal l) => literalPromote l
      | some t => .term t
      | none => .error
  | .iri i => .term (.iri i)
  | .lit l => .term (.literal l)
  | .boolLit b => .bool b
  | .numericLit n => .num n
  | .decimalLit s => .dec s
  | .doubleLit s => .dbl s

  -- §17.4.1 arithmetic, with §17.1 numeric promotion.
  | .arith op e1 e2 =>
      let v1 := Expr.evalIn env mu e1
      let v2 := Expr.evalIn env mu e2
      match v1, v2 with
      | .num a, .num b => evalArithInt op a b
      | _, _ =>
          match v1.toNumeric?, v2.toNumeric? with
          | some (a, ka), some (b, kb) =>
              let k := promoteKind ka kb
              -- `/` never yields an integer: integer ÷ integer is decimal.
              let k := match op, k with | .div, .int => .dec | _, _ => k
              match op with
              | .add => formatNumericResult (a.add b) k
              | .sub => formatNumericResult (a.sub b) k
              | .mul => formatNumericResult (a.mul b) k
              | .div =>
                  match a.div? b with
                  | some q => formatNumericResult q k
                  | none => .error
          | _, _ => .error
  | .unaryMinus e1 =>
      match Expr.evalIn env mu e1 with
      | .num n => .num (-n)
      | .dec s =>
          if strStartsWith s "-" && s.length > 1 then .dec (String.ofList (s.toList.drop 1))
          else if strStartsWith s "-" then .dec "0"
          else .dec ("-" ++ s)
      | .dbl s =>
          if strStartsWith s "-" && s.length > 1 then .dbl (String.ofList (s.toList.drop 1))
          else if strStartsWith s "-" then .dbl "0"
          else .dbl ("-" ++ s)
      | _ => .error
  | .unaryPlus e1 => Expr.evalIn env mu e1

  -- §17.4.1.7 comparison.
  | .compare op e1 e2 =>
      match valueCompare (Expr.evalIn env mu e1) (Expr.evalIn env mu e2) op with
      | some b => .bool b
      | none => .error

  -- §17.3 connectives: error-tolerant and error-preserving.
  | .and e1 e2 =>
      match boolAnd (ebv (Expr.evalIn env mu e1)) (ebv (Expr.evalIn env mu e2)) with
      | some b => .bool b
      | none => .error
  | .or e1 e2 =>
      match boolOr (ebv (Expr.evalIn env mu e1)) (ebv (Expr.evalIn env mu e2)) with
      | some b => .bool b
      | none => .error
  | .not e1 =>
      match boolNot (ebv (Expr.evalIn env mu e1)) with
      | some b => .bool b
      | none => .error

  -- §17.4.2 node tests.
  | .isIri e1 => fnIsIri (Expr.evalIn env mu e1)
  | .isBlank e1 => fnIsBlank (Expr.evalIn env mu e1)
  | .isLiteral e1 => fnIsLiteral (Expr.evalIn env mu e1)
  | .isNumeric e1 => fnIsNumeric (Expr.evalIn env mu e1)

  -- §17.4.2 accessors.
  | .str e1 => fnStr (Expr.evalIn env mu e1)
  | .lang e1 => fnLang (Expr.evalIn env mu e1)
  | .datatype e1 => fnDatatype (Expr.evalIn env mu e1)
  | .hasLang e1 => fnHasLang (Expr.evalIn env mu e1)
  | .hasLangDir e1 => fnHasLangDir (Expr.evalIn env mu e1)
  | .langDir e1 => fnLangDir (Expr.evalIn env mu e1)
  -- §17.4.2.8 IRI(). DEVIATION from the F* source, stated plainly: the
  -- F* arm resolves a RELATIVE reference against the query's BASE
  -- (`resolve_iri`); RFC 3986 reference resolution is not ported here,
  -- so a lexical form that is not already an absolute IRI is an error.
  | .iriFn e1 =>
      match Expr.evalIn env mu e1 with
      | .term (.iri i) => .term (.iri i)
      | .term (.literal l) =>
          if h : L4Factoidal.RDF.isIri l.val.lexicalForm then .term (.iri ⟨l.val.lexicalForm, h⟩)
          else .error
      | _ => .error

  -- §17.4.2 term constructors.
  | .strDt e1 e2 =>
      match (Expr.evalIn env mu e1).toString?, Expr.evalIn env mu e2 with
      | some s, .term (.iri dt) => .term (.literal (mkTypedLiteral s dt))
      | _, _ => .error
  | .strLang e1 e2 =>
      match Expr.evalIn env mu e1, (Expr.evalIn env mu e2).toString? with
      | .term (.literal l), some tag =>
          if l.val.datatype == xsdString && l.val.langTag.isNone then
            .term (.literal (mkLangLiteral l.val.lexicalForm tag))
          else .error
      | _, _ => .error
  | .strLangDir e1 e2 e3 =>
      match Expr.evalIn env mu e1, (Expr.evalIn env mu e2).toString?,
            (Expr.evalIn env mu e3).toString? with
      | .term (.literal l), some tag, some dirStr =>
          if l.val.datatype == xsdString && l.val.langTag.isNone && tag.length > 0 then
            match parseTextDirection dirStr with
            | some d => .term (.literal (mkDirLangLiteral l.val.lexicalForm tag d))
            | none => .error
          else .error
      | _, _, _ => .error

  -- §17.4.1.1 BOUND. The only form that inspects the mapping's DOMAIN
  -- rather than a value, and so the only one that never errors.
  | .bound v => .bool (mu.lookup v).isSome

  -- §17.4.1 functional forms.
  | .cond c t e =>
      if ebvOrFalse (Expr.evalIn env mu c) then Expr.evalIn env mu t
      else Expr.evalIn env mu e
  | .coalesce es => coalesceResults (Expr.evalArgs env mu es)
  | .inList e1 es => inResults (Expr.evalIn env mu e1) (Expr.evalArgs env mu es)
  | .notInList e1 es =>
      match inResults (Expr.evalIn env mu e1) (Expr.evalArgs env mu es) with
      | .bool b => .bool (!b)
      | other => other

  -- §17.4.3 string functions.
  | .strLen e1 =>
      match (Expr.evalIn env mu e1).toString? with
      | some s => .num (s.length : Int)
      | none => .error
  | .substr e1 e2 lenOpt =>
      substrResult (Expr.evalIn env mu e1) (Expr.evalIn env mu e2)
        (Expr.evalOpt env mu lenOpt)
  | .uCase e1 =>
      match (Expr.evalIn env mu e1).stringInfo? with
      | some (s, tg, dt) => erStringPreserve s.toUpper tg dt
      | none => .error
  | .lCase e1 =>
      match (Expr.evalIn env mu e1).stringInfo? with
      | some (s, tg, dt) => erStringPreserve s.toLower tg dt
      | none => .error
  | .strStarts e1 e2 =>
      match (Expr.evalIn env mu e1).toString?, (Expr.evalIn env mu e2).toString? with
      | some s, some p => .bool (strStartsWith s p)
      | _, _ => .error
  | .strEnds e1 e2 =>
      match (Expr.evalIn env mu e1).toString?, (Expr.evalIn env mu e2).toString? with
      | some s, some p => .bool (strEndsWith s p)
      | _, _ => .error
  | .contains e1 e2 =>
      match (Expr.evalIn env mu e1).toString?, (Expr.evalIn env mu e2).toString? with
      | some s, some p => .bool (strContains s p)
      | _, _ => .error
  | .strBefore e1 e2 =>
      match (Expr.evalIn env mu e1).stringInfo?, (Expr.evalIn env mu e2).stringInfo? with
      | some (s, lang1, dt1), some (arg, lang2, dt2) =>
          if !strBeforeAfterCompatible lang1 dt1 lang2 dt2 then .error
          else if arg.length = 0 then erStringPreserve "" lang1 dt1
          else
            let result := strBeforeRaw s arg
            if result.length = 0 && !strContains s arg then erString ""
            else erStringPreserve result lang1 dt1
      | _, _ => .error
  | .strAfter e1 e2 =>
      match (Expr.evalIn env mu e1).stringInfo?, (Expr.evalIn env mu e2).stringInfo? with
      | some (s, lang1, dt1), some (arg, lang2, dt2) =>
          if !strBeforeAfterCompatible lang1 dt1 lang2 dt2 then .error
          else if arg.length = 0 then erStringPreserve s lang1 dt1
          else
            let result := strAfterRaw s arg
            if result.length = 0 && !strContains s arg then erString ""
            else erStringPreserve result lang1 dt1
      | _, _ => .error
  | .concat es => concatResults (Expr.evalArgs env mu es)
  | .encodeForUri e1 =>
      -- ENCODE_FOR_URI always returns xsd:string; no tag is preserved.
      match (Expr.evalIn env mu e1).toString? with
      | some s => erString (strEncodeUri s)
      | none => .error
  -- SCOPED OUT: REGEX/REPLACE need an XPath regex engine (see banner).
  | .replace _ _ _ _ => .error
  | .regex _ _ _ => .error

  -- §17.4.4 numeric functions.
  | .abs e1 =>
      match Expr.evalIn env mu e1 with
      | .num n => .num (n.natAbs : Int)
      | .dec s => .dec (if strStartsWith s "-" then String.ofList (s.toList.drop 1) else s)
      | .dbl s => .dbl (if strStartsWith s "-" then String.ofList (s.toList.drop 1) else s)
      | _ => .error
  | .round e1 =>
      match Expr.evalIn env mu e1 with
      | .num n => .num n
      | .dec s => .dec (toString (lexRound s))
      | .dbl s => .dbl (toString (lexRound s))
      | _ => .error
  | .ceil e1 =>
      match Expr.evalIn env mu e1 with
      | .num n => .num n
      | .dec s => .dec (toString (lexCeil s))
      | .dbl s => .dbl (toString (lexCeil s))
      | _ => .error
  | .floor e1 =>
      match Expr.evalIn env mu e1 with
      | .num n => .num n
      | .dec s => .dec (toString (lexFloor s))
      | .dbl s => .dbl (toString (lexFloor s))
      | _ => .error

  -- SCOPED OUT: §17.4.3.16 hash builtins (see banner).
  | .md5 _ | .sha1 _ | .sha256 _ | .sha384 _ | .sha512 _ => .error

  -- §17.4.5 date/time.
  | .now =>
      match env.now with
      | some ts => .term (.literal (mkTypedLiteral ts xsdDateTime))
      | none => .error
  | .year e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtYear s with | some n => .num n | none => .error
      | none => .error
  | .month e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtMonth s with | some n => .num n | none => .error
      | none => .error
  | .day e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtDay s with | some n => .num n | none => .error
      | none => .error
  | .hours e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtHours s with | some n => .num n | none => .error
      | none => .error
  | .minutes e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtMinutes s with | some n => .num n | none => .error
      | none => .error
  | .seconds e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtSeconds s with | some ds => .dec ds | none => .error
      | none => .error
  -- SCOPED OUT: TIMEZONE/TZ (see banner).
  | .timezone _ | .tz _ => .error

  -- §17.4.1.2 sameTerm — term IDENTITY, stricter than `=`.
  | .sameTerm e1 e2 =>
      match Expr.evalIn env mu e1, Expr.evalIn env mu e2 with
      | .term t1, .term t2 => .bool (t1.eqb t2)
      | .num a, .num b => .bool (a == b)
      | .dec a, .dec b => .bool (a == b)
      | .dbl a, .dbl b => .bool (a == b)
      | .bool a, .bool b => .bool (a == b)
      | _, _ => .bool false

  -- §18.6 EXISTS: delegated to the pattern layer through the hook.
  | .existsPat p =>
      match env.existsHook with
      | some h => .bool (h p mu)
      | none => .error
  | .notExistsPat p =>
      match env.existsHook with
      | some h => .bool (!h p mu)
      | none => .error

  -- SCOPED OUT: §18.5.1 aggregates evaluate over a GROUP.
  | .aggregate _ _ _ => .error

  -- §17.4.3.10 langMatches is the one IRI-named function with native
  -- semantics; everything else is offered to the §17.6 host registry,
  -- and an unregistered IRI is the spec-required type error.
  | .functionCall i args =>
      let vals := Expr.evalArgs env mu args
      if i == langMatchesIri then
        match vals with
        | [v1, v2] =>
            match v1.toString?, v2.toString? with
            | some tag, some range => .bool (fnLangMatches tag range)
            | _, _ => .error
        | _ => .error
      else
        match env.ext i.val vals with
        | some r => r
        | none => .error

  -- SPARQL 1.2 triple-term builtins.
  | .tripleTerm es ep eo =>
      match (Expr.evalIn env mu es).toTerm?, (Expr.evalIn env mu ep).toTerm?,
            (Expr.evalIn env mu eo).toTerm? with
      | some sterm, some (.iri p), some oterm =>
          match sterm.toSubject? with
          | some ssub => .term (.tripleTerm ssub p oterm)
          | none => .error
      | _, _, _ => .error
  | .ttSubject e1 =>
      match Expr.evalIn env mu e1 with
      | .term (.tripleTerm s _ _) => .term s.toTerm
      | _ => .error
  | .ttPredicate e1 =>
      match Expr.evalIn env mu e1 with
      | .term (.tripleTerm _ p _) => .term (.iri p)
      | _ => .error
  | .ttObject e1 =>
      match Expr.evalIn env mu e1 with
      | .term (.tripleTerm _ _ o) => .term o
      | _ => .error
  | .isTriple e1 =>
      match Expr.evalIn env mu e1 with
      | .error => .error
      | .term (.tripleTerm _ _ _) => .bool true
      | _ => .bool false

/-- Evaluate an argument LIST (COALESCE, IN, CONCAT, function calls).
Evaluating every argument before selecting is observationally the same
as the F* source's short-circuiting recursion: the evaluator is pure
and total, so an unused argument's value cannot be observed. -/
def Expr.evalArgs (env : EvalEnv) (mu : Binding) : List Expr → List EvalResult
  | [] => []
  | e :: rest => Expr.evalIn env mu e :: Expr.evalArgs env mu rest

/-- Evaluate an OPTIONAL sub-expression (SUBSTR's length argument). -/
def Expr.evalOpt (env : EvalEnv) (mu : Binding) : Option Expr → Option EvalResult
  | none => none
  | some e => some (Expr.evalIn env mu e)

end

/-- Evaluate with no host services — the §17 semantics on its own. -/
def Expr.eval (mu : Binding) (e : Expr) : EvalResult := Expr.evalIn emptyEnv mu e

/-! ## Bridge to the algebra — §18.5 FILTER

`GraphPattern.filter` and `GraphPattern.leftJoin` take a
`Binding → Bool`; §18.5 says a row survives FILTER when its expression
"has an effective boolean value of true", so a type error is
indistinguishable from `false` at that boundary. `Expr.toCond` is
exactly that collapse — and it is where §17's careful error PRESERVING
finally stops mattering. -/

def Expr.toCond (e : Expr) : Binding → Bool := fun mu => (ebv (e.eval mu)).getD false

/-- FILTER(expr) as an algebra operation (§18.5). -/
def GraphPattern.filterExpr (e : Expr) (p : GraphPattern) : GraphPattern :=
  .filter e.toCond p

/-- OPTIONAL with a filter: LeftJoin(P1, P2, expr) (§18.5). -/
def GraphPattern.leftJoinExpr (l r : GraphPattern) (e : Expr) : GraphPattern :=
  .leftJoin l r e.toCond

end L4Factoidal.SPARQL
