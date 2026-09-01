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

ALSO IMPLEMENTED, each as a total function of explicit inputs:
  * §17.4.4.7–11 hash builtins MD5 / SHA1 / SHA256 / SHA384 / SHA512 —
    pure Lean digests (`Crypto/MD5.lean`, `Crypto/SHA1.lean`,
    `Crypto/SHA2.lean`; see `skills/crypto-policy/SKILL.md`, tier 1:
    hashes over public data), lowercase hex, where the F* tree assumes
    them (`assume val hash_*`);
  * §17.4.5.7/8 TIMEZONE and TZ (`dtTimezone`, `dtTz`, ports of the F*
    `dt_timezone`/`dt_tz`);
  * §17.5 XSD constructor functions `xsd:integer` / `decimal` / `float`
    / `double` / `string` / `boolean` and, for any other XSD datatype
    IRI, a typed literal (`evalXsdCast`, port of `eval_xsd_cast`);
  * §17.4.2.9/12/13 BNODE() / BNODE(str) / UUID() / STRUUID() — FRESH
    values derived deterministically from the (row, call-site) freshness
    context the caller injects (`Binding.withFreshnessCtx`, the F*
    `fx_ctx_put` design), so a query's result is reproducible;
    §17.4.4.3 RAND() is the F* tree's fixed `0.5` (a double in [0, 1)),
    stated plainly: not random;
  * §17.4.2.8 IRI()/URI() resolves a relative reference against the
    query's BASE, carried in `EvalEnv.base` (RFC 3986, `Syntax/
    IriResolve.lean`).

WHAT THIS FILE DELIBERATELY DOES NOT EVALUATE (each returns the
constructor-level `EvalResult.error`, which IS an operator's spec
behaviour when it cannot produce a value — never `sorry`, never a
`partial def`):
  * (closed 2026-08-22) `Expr.regex` / `Expr.replace` — REGEX and
    REPLACE (§17.4.3.14/§17.4.3.15) now run on the pure XPath engine
    `L4Factoidal.Regex` (the port of the F* derivative engine; see
    `regexCore` / `replaceCore`).
  * `Expr.existsPat` / `Expr.notExistsPat` — §18.6 EXISTS needs pattern
    evaluation against the active graph and the dataset, which sits
    above expressions. The pattern layer (`Query.lean`,
    `substituteExistentials`) replaces every EXISTS sub-expression by
    its boolean BEFORE an expression reaches this evaluator, exactly as
    the F* `substitute_existentials` does; an EXISTS that reaches this
    layer un-substituted is the error the F* evaluator also returns
    here (`E_Exists _ -> ER_Error`). Design record: `SPARQL/Exists.lean`.
  * `Expr.aggregate` — aggregates are evaluated in the §18.5.1
    aggregation context over a solution GROUP, not per solution
    mapping. The F* arm is `E_Aggregate _ _ _ -> ER_Error` for exactly
    this reason; the port keeps that.
  * `Expr.now` — §17.4.5.1 reads a clock. Modelled purely: the
    timestamp is an INPUT, `EvalEnv.now`; with none supplied the result
    is an error rather than an ambient effect.
  * §17.6 extension functions and every unrecognised `functionCall`
    IRI — offered to `EvalEnv.ext`; an unregistered IRI is a type
    error, which is precisely what §17.6 requires.

DEVIATIONS FROM THE F* SOURCE, each one the W3C expected file's side
(the F* runner's row comparison, `bin/w3c-runner/w3c_runner.ml`
`binding_row_matches_with`, ignores an actual binding the expected row
lacks, which hides these in the F* scores; this port's harness does
not):
  * STRDT's first argument must be a simple / `xsd:string` literal
    (§17.4.2.3; W3C `strdt01`/`strdt03`); the F* accepts any value.
  * IF propagates a type error in its condition (§17.4.1.2; W3C
    `if02`); the F* folds the error to `false`.
  * CONCAT, STRBEFORE and STRAFTER require STRING literal arguments
    (§17.4.3.1 argument compatibility; W3C `concat02`,
    `strbefore01a`, `strafter01a`); the F* accepts promoted numbers.
  * STRBEFORE/STRAFTER: a simple-literal first argument with a
    language-tagged second argument is NOT compatible (§17.4.3.1 lists
    exactly three compatible pairs; W3C `strbefore02`/`strafter02`);
    the F* compatibility predicate has a fourth, permissive clause.
  * `xsd:decimal` of a STRING requires an xsd:decimal lexical form (no
    exponent; W3C `cast-decimal` rows `s03`, `s07`, `s10`); the F*
    accepts E-notation strings there.

Readability contract (as elsewhere in this port): every definition
cites the spec section it implements, and names track the spec's
vocabulary rather than implementation jargon.
-/
import L4Factoidal.SPARQL.Algebra
import L4Factoidal.Syntax.IriResolve
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Crypto.MD5
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Regex.XPath

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Datatype IRIs this file needs beyond `RDF.Core`'s set -/

/-- `xsd:float` — in `is_numeric_datatype`'s set alongside integer,
decimal and double (SPARQL 1.1 §17.1 operand types). -/
def xsdFloat : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#float", rfl⟩

/-- `xsd:dateTime` — the operand type of the §17.4.5 accessors. -/
def xsdDateTime : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#dateTime", rfl⟩

/-- `xsd:dayTimeDuration` — the result type of §17.4.5.7 TIMEZONE. -/
def xsdDayTimeDuration : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#dayTimeDuration", rfl⟩

/-- The XML Schema namespace, for §17.5 constructor-function dispatch. -/
def xsdNamespace : String := "http://www.w3.org/2001/XMLSchema#"

/-- The XPath functions namespace the F* evaluator dispatches RAND(),
UUID(), STRUUID() and BNODE() on (the parser maps those keywords to
`functionCall` with these IRIs). -/
def fnNamespace : String := "http://www.w3.org/2005/xpath-functions#"

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
carry a `QueryPattern` — the CONCRETE pattern AST, exactly as the F*
`E_Exists : group_graph_pattern -> expr` does — so an EXISTS body is
lowered into the algebra only at evaluation time, under the real
environment and the active graph of its enclosing pattern (§18.6:
"exists(pattern, μ) evaluates substitute(pattern, μ)"). That is why
the expression AST and the query AST (`QueryPattern`, `Query` and the
query-level pieces that carry expressions) form ONE mutual inductive
below: the F* has the same knot in one `type … and …` group. The
query-level types are documented where the F* documents them
(`Query.lean` still holds their accessors and the evaluator); they
live here only because Lean requires a mutual block to be one
declaration. Design record: `SPARQL/Exists.lean`. -/

/-- §13.2 `FROM` / `FROM NAMED`. Carries no expression, so it sits
outside the mutual block. -/
inductive DatasetClause where
  | default (i : WfIri)
  | named   (i : WfIri)

mutual

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
  | replace     (e pat rep : Expr) (flags : Option Expr)   -- §17.4.3.15
  | regex       (e pat : Expr) (flags : Option Expr)       -- §17.4.3.14
  -- Numeric functions (§17.4.4)
  | abs         (e : Expr)
  | round       (e : Expr)
  | ceil        (e : Expr)
  | floor       (e : Expr)
  -- Hash functions (§17.4.4.7–11)
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
  | timezone    (e : Expr)
  | tz          (e : Expr)
  -- RDF term identity (§17.4.1.2)
  | sameTerm    (l r : Expr)
  -- EXISTS / NOT EXISTS (§18.6) — the body is the concrete pattern AST
  | existsPat    (p : QueryPattern)
  | notExistsPat (p : QueryPattern)
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

/-- A SELECT projection item: a bare variable, or `(expr AS ?v)`
(§18.2.4). -/
inductive SelectItem where
  | var  (v : VarName)
  | expr (e : Expr) (v : VarName)

/-- `SELECT ?a ?b` versus `SELECT *`. -/
inductive SelectClause where
  | vars (items : List SelectItem)
  | all

/-- §18.2 query forms. DESCRIBE is carried in the AST for completeness
but evaluates to nothing, exactly as the F* source's `QF_Describe`
does — the description shape is a policy decision the spec leaves to
implementations, and this port makes no choice for it. -/
inductive QueryForm where
  | select    (sel : SelectClause)
  | construct (template : List TriplePattern)
  | ask
  | describe  (terms : List PatternTerm)

/-- §15.1 `ORDER BY ASC(e)` / `DESC(e)`. -/
inductive OrderCondition where
  | asc  (e : Expr)
  | desc (e : Expr)

/-- §15 solution modifiers, gathered (port of `solution_modifier`). -/
structure SolutionModifier where
  orderBy  : Option (List OrderCondition) := none
  distinct : Bool := false
  reduced  : Bool := false
  offset   : Option Nat := none
  limit    : Option Nat := none

/-- §18.2.4.1 GROUP BY: a variable, or an expression with an optional
`AS ?alias`. -/
inductive GroupCondition where
  | var  (v : VarName)
  | expr (e : Expr) (alias : Option VarName)

/-- The concrete graph-pattern AST — one constructor per F*
`group_graph_pattern` case (§18.2.2). Lowered into
`SPARQL.GraphPattern` by `QueryPattern.lower` (`Query.lean`). -/
inductive QueryPattern where
  | bgp          (patterns : Bgp)
  | join         (l r : QueryPattern)
  /-- `OPTIONAL { P } FILTER(e)` — LeftJoin(P1, P2, e), §18.5. -/
  | leftJoin     (l r : QueryPattern) (cond : Expr)
  | filter       (cond : Expr) (p : QueryPattern)
  | union        (l r : QueryPattern)
  | minus        (l r : QueryPattern)
  /-- `GRAPH <iri> { P }` / `GRAPH ?g { P }` — §18.6. -/
  | graph        (name : PatternTerm) (p : QueryPattern)
  /-- `P1 LATERAL { P2 }` — correlated evaluation. -/
  | lateral      (l r : QueryPattern)
  /-- `BIND(e AS ?v)` — §18.6. -/
  | bind         (e : Expr) (v : VarName) (p : QueryPattern)
  /-- `VALUES (?x ?y) { (1 2) (3 UNDEF) }` — §10.2. -/
  | values       (vars : List VarName) (rows : List (List (Option Term)))
  /-- `SERVICE [SILENT] <iri> { P }` — Federated Query §2. -/
  | service      (endpoint : WfIri) (silent : Bool) (p : QueryPattern)
  /-- `SERVICE [SILENT] ?v { P }` — variable endpoint. -/
  | serviceVar   (v : VarName) (silent : Bool) (p : QueryPattern)
  /-- A sub-SELECT used as a group graph pattern (§18.2.4). -/
  | subSelect    (q : Query)
  /-- `?s path ?o` — §18.4. -/
  | propertyPath (s : PatternSubject) (path : PropertyPath) (o : PatternTerm)
  /-- The empty group pattern `{}`. -/
  | empty

/-- A complete SPARQL 1.1 query (port of the F* `query` record). It is
an `inductive` rather than a `structure` only because it predates
mutual structures; `mkQuery` and the field accessors in `Query.lean`
restore the record ergonomics.

`base` is the BASE IRI in force for the query (the prologue's `BASE`,
else the document/request IRI the parser was given) — the F* `q_base`
— which §17.4.2.8 IRI() resolves relative references against.
`postValues` is the trailing `VALUES` block a query may carry after
its WHERE clause (§10.2): its rows are JOINed onto the WHERE result. -/
inductive Query where
  | mk (form       : QueryForm)
       (dataset    : List DatasetClause)
       (pattern    : QueryPattern)
       (groupBy    : Option (List GroupCondition))
       (having     : List Expr)
       (modifier   : SolutionModifier)
       (postValues : Option (List Binding))
       (base       : Option String)

end

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
        -- Valid lexical forms only (XSD 1.1 §3.3.2). SPARQL 1.1
        -- §17.2.2 sent an ill-formed boolean to `false`; SPARQL 1.2
        -- removed that rule, so it is a type error (`not-not`: the
        -- row for `"z"^^xsd:boolean` leaves its BIND unbound). No
        -- sparql11 suite test exercises the removed rule — measured,
        -- all 34 suites stay green — so one behaviour serves both.
        match l.val.lexicalForm with
        | "true" | "1" => some true
        | "false" | "0" => some false
        | _ => none
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

/-- Lexical form + language tag + datatype of a STRING LITERAL only —
a simple literal, an `xsd:string`, an `rdf:langString` or an
`rdf:dirLangString`. §17.4.3.1 "Strings in SPARQL functions" defines
the string functions over exactly these; a promoted number or boolean
is NOT a string literal (W3C `concat02`, `strbefore01a`: `CONCAT(?x,
7)` and `STRBEFORE(7, "b")` are type errors). CONCAT, STRBEFORE and
STRAFTER use this; SUBSTR/UCASE/LCASE keep the wider `stringInfo?`
as in the F* source. -/
def EvalResult.stringLiteralInfo? : EvalResult → Option (String × Option String × WfIri)
  | .term (.literal l) =>
      if l.val.datatype == xsdString || l.val.datatype == rdfLangString ||
         l.val.datatype == rdfDirLangString then
        some (l.val.lexicalForm, l.val.langTag, l.val.datatype)
      else none
  | _ => none

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
    -- Valid lexical forms only, like the integer arm above: an
    -- ill-formed boolean has no value to promote TO, and promoting it
    -- to `false` hid the type error `ebv` must raise (sparql12
    -- `expression/not-not`, the `"z"^^xsd:boolean` row).
    match l.val.lexicalForm with
    | "true" | "1" => .bool true
    | "false" | "0" => .bool false
    | _ => .term (.literal l)
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
        /- RDF language tags are case-insensitive in the term/value equality
           used by SPARQL `=`.  Keep `sameTerm`'s distinct strict-term rule
           separate; this operator mapping follows `Literal.eqb`. -/
        if langTagOptionEq l1.val.langTag l2.val.langTag then
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
the F* `dt_*` helpers do. -/

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

/-- Strip leading zeros from a numeric lexical form, keeping one digit
before a decimal point: `"01" ↦ "1"`, `"00" ↦ "0"`, `"01.5" ↦ "1.5"`,
`"0.5" ↦ "0.5"` (port of `strip_leading_zeros_num`). -/
def stripLeadingZerosNum (s : String) : String :=
  let rec skip : List Char → List Char
    | '0' :: rest =>
        match rest with
        | []       => ['0']
        | c2 :: _  => if c2 == '.' then '0' :: rest else skip rest
    | cs => cs
  match skip s.toList with
  | [] => "0"
  | cs => String.ofList cs

/-- SECONDS returns an xsd:decimal (fractional seconds are in scope);
the lexical form is canonicalised (`"01"` ↦ `"1"`), the W3C
`seconds01` expectation. -/
def dtSeconds (s : String) : Option String :=
  if s.length < 19 then none
  else
    let after := s.toList.drop 17
    let secChars := after.takeWhile (fun c => c != 'Z' && c != '+' && c != '-')
    if secChars.isEmpty then none
    else some (stripLeadingZerosNum (String.ofList secChars))

/-- Codepoint offset of the timezone sign (`+`/`-`) at or after
position 19 of an xsd:dateTime lexical form. -/
def dtTzPos (s : String) : Option Nat :=
  let rec go : List Char → Nat → Option Nat
    | [], _ => none
    | c :: rest, pos =>
        if pos ≥ 19 && (c == '+' || c == '-') then some pos else go rest (pos + 1)
  go s.toList 0

/-- §17.4.5.7 TIMEZONE: the timezone as an xsd:dayTimeDuration lexical
form — `Z ↦ "PT0S"`, `-08:00 ↦ "-PT8H"`, `+05:30 ↦ "PT5H30M"`; `""`
when the value carries no timezone (the caller turns that into the
spec's type error). Port of `dt_timezone`. -/
def dtTimezone (s : String) : Option String :=
  let len := s.length
  if len < 19 then none
  else if s.toList.getLast? == some 'Z' then some "PT0S"
  else match dtTzPos s with
    | none => some ""
    | some pos =>
        if len ≥ pos + 6 then
          let signStr := if lexSlice s pos 1 == "-" then "-" else ""
          match parseIntString (lexSlice s (pos + 1) 2), parseIntString (lexSlice s (pos + 4) 2) with
          | some h, some m =>
              if m = 0 then some (signStr ++ "PT" ++ toString h ++ "H")
              else some (signStr ++ "PT" ++ toString h ++ "H" ++ toString m ++ "M")
          | _, _ => none
        else none

/-- §17.4.5.8 TZ: the timezone part of the lexical form as written —
`"Z"`, `"-08:00"`, or `""` when there is none. Port of `dt_tz`. -/
def dtTz (s : String) : Option String :=
  let len := s.length
  if len < 19 then none
  else if s.toList.getLast? == some 'Z' then some "Z"
  else match dtTzPos s with
    | none => some ""
    | some pos => if pos < len then some (lexSlice s pos (len - pos)) else none

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
  /-- §18.6 EXISTS: the dataset `D` that `exists(pattern, μ)` evaluates
  the substituted pattern against (the F* `eval_exists … ds`
  argument). `evalSelect` / `evalAsk` / `evalConstruct` install the
  query's dataset here (after FROM / FROM NAMED); with none, EXISTS
  is left un-substituted and is the expression-layer error. -/
  dataset : Option Dataset := none
  /-- §17.4.2.8 IRI(): the query's BASE IRI (the prologue's `BASE`, or
  the request/document IRI the parser was given), against which a
  relative reference resolves. The F* evaluator threads this as the
  `base` parameter of `eval_expr_with_base`; here it is an environment
  field. Absent means a non-absolute lexical form is a type error. -/
  base : Option String := none

/-- Resolve a SERVICE endpoint IRI to the graph it serves. -/
def EvalEnv.resolveService (env : EvalEnv) (i : Iri) : Option Graph :=
  match env.services.find? (fun p => p.1 == i) with
  | some p => some p.2
  | none   => none

/-- The environment with no host services and no dataset: extension
functions error, EXISTS errors, NOW errors. -/
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
      match v.stringLiteralInfo? with
      | none => .error
      | some (s, lang, dt) =>
          match lang, v.direction? with
          | some l1, some d => .term (.literal (mkDirLangLiteral s l1 d))
          | _, _ => erStringPreserve s lang dt
  | v :: rest =>
      match v.stringLiteralInfo? with
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

/-- §17.4.3.14 REGEX over the pure XPath engine (`L4Factoidal.Regex`,
the port of the F* derivative engine behind `regex_match`). Arguments:
text (a string literal — simple, xsd:string or language-tagged),
pattern and flags (simple literals). An invalid pattern or flag
(FORX0001/FORX0002) is an expression error. -/
def regexCore (t p f : EvalResult) : EvalResult :=
  match t.stringLiteralInfo?, p.toString?, f.toString? with
  | some (s, _, _), some pat, some fl =>
      match Regex.compile pat fl with
      | .ok r    => .bool (Regex.isMatch r s)
      | .error _ => .error
  | _, _, _ => .error

/-- §17.4.3.15 REPLACE: like REGEX, plus the replacement template
(FORX0003 for a nullable pattern, FORX0004 for a bad template); the
text's language tag / datatype is kept (`erStringPreserve`). -/
def replaceCore (t p r f : EvalResult) : EvalResult :=
  match t.stringLiteralInfo?, p.toString?, r.toString?, f.toString? with
  | some (s, lg, dt), some pat, some rep, some fl =>
      match Regex.compile pat fl with
      | .ok re =>
          match Regex.replace re s rep with
          | .ok out  => erStringPreserve out lg dt
          | .error _ => .error
      | .error _ => .error
  | _, _, _, _ => .error

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

/-- §17.4.3.1 argument compatibility for STRBEFORE and STRAFTER (both
arguments already known to be string literals, see
`stringLiteralInfo?`). The table lists exactly three compatible
pairs: two simple/`xsd:string` literals; two language-tagged literals
with the SAME tag; a language-tagged first argument with a
simple/`xsd:string` second. A simple first argument with a tagged
second is NOT compatible (W3C `strbefore02`: `STRBEFORE("abc",
"b"@cy)` is a type error). -/
def strBeforeAfterCompatible
    (lang1 : Option String) (_dt1 : WfIri)
    (lang2 : Option String) (_dt2 : WfIri) : Bool :=
  match lang1, lang2 with
  | none,    none    => true
  | some _,  none    => true
  | some l1, some l2 => l1 == l2
  | none,    some _  => false

/-! ## §17.5 XSD constructor functions (casting)

Port of `eval_xsd_cast`, with the XSD lexical-space rule made
explicit: a cast FROM A STRING succeeds only when the lexical form is
in the target datatype's lexical space (XSD 1.1 Part 2 §3.3.13
integer, §3.3.3 decimal, §3.3.5 double, §3.3.2 boolean); a cast from
a NUMBER or BOOLEAN converts the VALUE. The W3C `cast` suite pins
both halves (`xsd:integer("1.5")` is an error, `xsd:integer(1.5)` is
`1`). -/

/-- Drop one leading `+` (numeric lexical forms admit it, results do
not carry it). -/
def stripLeadingPlus (s : String) : String :=
  match s.toList with
  | '+' :: rest => String.ofList rest
  | _ => s

def isDigit (c : Char) : Bool := c.toNat ≥ 48 && c.toNat ≤ 57

/-- XSD integer lexical space: `[+-]?[0-9]+`. -/
def isIntegerLexical (s : String) : Bool :=
  let cs := match s.toList with
    | '+' :: rest | '-' :: rest => rest
    | cs => cs
  !cs.isEmpty && cs.all isDigit

/-- XSD decimal lexical space: `[+-]?([0-9]+(\.[0-9]*)?|\.[0-9]+)`. -/
def isDecimalLexical (s : String) : Bool :=
  let cs := match s.toList with
    | '+' :: rest | '-' :: rest => rest
    | cs => cs
  let intPart := cs.takeWhile isDigit
  match cs.dropWhile isDigit with
  | [] => !intPart.isEmpty
  | '.' :: frac => (!intPart.isEmpty || !frac.isEmpty) && frac.all isDigit
  | _ => false

/-- XSD double/float lexical space: a decimal with an optional
`[Ee][+-]?[0-9]+` exponent, or `INF` / `-INF` / `NaN`. -/
def isDoubleLexical (s : String) : Bool :=
  if s == "INF" || s == "-INF" || s == "+INF" || s == "NaN" then true
  else
    let cs := s.toList
    let notE := fun (c : Char) => c != 'E' && c != 'e'
    let mant := String.ofList (cs.takeWhile notE)
    match cs.dropWhile notE with
    | [] => isDecimalLexical mant
    | _ :: ex => isDecimalLexical mant && isIntegerLexical (String.ofList ex)

/-- Canonical xsd:decimal lexical form of a decimal lexical: no
leading `+`, a digit before the point, trailing zeros dropped but one
fraction digit kept (`"+33.3300" ↦ "33.33"`, `"0" ↦ "0.0"`). -/
def canonDecimalLexical (s : String) : String :=
  let s1 := stripLeadingPlus s
  let (neg, cs) := match s1.toList with
    | '-' :: rest => (true, rest)
    | cs => (false, cs)
  let intPart := cs.takeWhile (fun c => c != '.')
  let frac := (cs.dropWhile (fun c => c != '.')).drop 1
  let intStr := if intPart.isEmpty then "0"
                else String.ofList (stripLeadingZerosNum (String.ofList intPart)).toList
  let fracStr := String.ofList (stripTrailingZerosChars frac)
  let fracStr := if fracStr.isEmpty then "0" else fracStr
  (if neg then "-" else "") ++ intStr ++ "." ++ fracStr

/-- Decimal lexical form of a scaled value, with at least one fraction
digit (`⟨1, 0⟩ ↦ "1.0"`, `⟨125, 2⟩ ↦ "1.25"`). -/
def scaledToDecimalLexical (v : Scaled) : String :=
  if v.scale = 0 then toString v.mantissa ++ ".0"
  else stripTrailingDecimalZeros (formatScaledValue v.mantissa v.scale)

/-- The lexical form a cast reads: promoted numbers print canonically,
literals and IRIs give their own string; blank nodes and triple terms
have none. -/
def castLexical : EvalResult → Option String
  | .num n => some (toString n)
  | .dec s => some s
  | .dbl s => some s
  | .bool b => some (if b then "true" else "false")
  | .term (.literal l) => some l.val.lexicalForm
  | .term (.iri i) => some i.val
  | _ => none

/-- `xsd:integer(v)`: a boolean maps to 1/0, a number truncates toward
zero (`-7.875 ↦ -7`), a string must be an integer lexical form. -/
def castInteger (v : EvalResult) (lex : String) : EvalResult :=
  match v with
  | .bool b => .num (if b then 1 else 0)
  | .num n => .num n
  | .dec _ | .dbl _ =>
      match parseDoubleToScaled lex with
      | some sv => .num (intDivT sv.mantissa (pow10 sv.scale))
      | none => .error
  | _ =>
      if isIntegerLexical lex then
        match parseIntString lex with
        | some n => .num n
        | none => .error
      else .error

/-- `xsd:decimal(v)`: a boolean maps to `1.0`/`0.0`, an integer gains
`.0`, a double converts by value, a string must be a decimal lexical
form (no exponent) and is canonicalised. -/
def castDecimal (v : EvalResult) (lex : String) : EvalResult :=
  match v with
  | .bool b => .dec (if b then "1.0" else "0.0")
  | .num n => .dec (toString n ++ ".0")
  | .dec _ => if isDecimalLexical lex then .dec (canonDecimalLexical lex) else .error
  | .dbl _ =>
      if isDecimalLexical lex then .dec (canonDecimalLexical lex)
      else match parseDoubleToScaled lex with
        | some sv => .dec (scaledToDecimalLexical sv)
        | none => .error
  | _ => if isDecimalLexical lex then .dec (canonDecimalLexical lex) else .error

/-- `xsd:double(v)`: the F* lexical conventions — a boolean is
`1.0E0`/`0.0E0`, an integer `<n>.0E0`, a decimal or double keeps its
lexical form, a string must be a double lexical form. -/
def castDouble (v : EvalResult) (lex : String) : EvalResult :=
  match v with
  | .bool b => .dbl (if b then "1.0E0" else "0.0E0")
  | .num n => .dbl (toString n ++ ".0E0")
  | .dbl _ | .dec _ => if isDoubleLexical lex then .dbl lex else .error
  | _ => if isDoubleLexical lex then .dbl lex else .error

/-- `xsd:float(v)`: a typed `xsd:float` literal (no promoted float
kind exists). Lexical conventions follow the F* source (ARQ's, which
the W3C `cast-float` expectation records): boolean `1.0E0`/`0E0`,
integer `0` or `<n>.0`, an integer-VALUED double `0.0`/`<n>.0`,
anything else its own lexical form. -/
def castFloat (v : EvalResult) (lex : String) : EvalResult :=
  let mkFloat := fun (s : String) => EvalResult.term (.literal (mkTypedLiteral s xsdFloat))
  match v with
  | .bool b => mkFloat (if b then "1.0E0" else "0E0")
  | .num n => mkFloat (if n = 0 then "0" else toString n ++ ".0")
  | .dbl _ =>
      match parseDoubleToScaled lex with
      | some sv =>
          let p := pow10 sv.scale
          if sv.mantissa % p = 0 then
            let n := intDivT sv.mantissa p
            mkFloat (if n = 0 then "0.0" else toString n ++ ".0")
          else mkFloat lex
      | none => .error
  | .dec _ => if isDecimalLexical lex then mkFloat lex else .error
  | _ => if isDoubleLexical lex then mkFloat lex else .error

/-- `xsd:boolean(v)`: a number is `true` iff non-zero; a string must
be one of `true`, `false`, `1`, `0`. -/
def castBoolean (v : EvalResult) (lex : String) : EvalResult :=
  match v with
  | .bool b => .bool b
  | .num n => .bool (n ≠ 0)
  | .dec _ | .dbl _ =>
      match parseDoubleToScaled lex with
      | some sv => .bool (sv.mantissa ≠ 0)
      | none => .error
  | _ =>
      if lex == "true" || lex == "1" then .bool true
      else if lex == "false" || lex == "0" then .bool false
      else .error

/-- `xsd:string(v)`: a simple literal; an integer-valued decimal or
double prints as its integer (`1.0 ↦ "1"`, `1E0 ↦ "1"`), as in the F*
source. -/
def castString (v : EvalResult) (lex : String) : EvalResult :=
  match v with
  | .dec _ =>
      match parseToScaled lex with
      | some sv =>
          let p := pow10 sv.scale
          if sv.mantissa % p = 0 then erString (toString (intDivT sv.mantissa p)) else erString lex
      | none => erString lex
  | .dbl _ =>
      match parseDoubleToScaled lex with
      | some sv =>
          let p := pow10 sv.scale
          if sv.mantissa % p = 0 then erString (toString (intDivT sv.mantissa p)) else erString lex
      | none => erString lex
  | _ => erString lex

/-- §17.5: dispatch `xsd:<targetType>(v)`. Any other XSD datatype IRI
(`xsd:dateTime`, …) constructs a typed literal from the lexical form;
the language-tagged datatypes are never constructible this way. -/
def evalXsdCast (v : EvalResult) (targetType : String) (fullIri : WfIri) : EvalResult :=
  match castLexical v with
  | none => .error
  | some lex0 =>
      let lex := if targetType == "string" || targetType == "boolean" then lex0
                 else stripLeadingPlus lex0
      if targetType == "integer" then castInteger v lex
      else if targetType == "decimal" then castDecimal v lex
      else if targetType == "double" then castDouble v lex
      else if targetType == "float" then castFloat v lex
      else if targetType == "boolean" then castBoolean v lex
      else if targetType == "string" then castString v lex
      else if fullIri != rdfLangString && fullIri != rdfDirLangString then
        .term (.literal (mkTypedLiteral lex fullIri))
      else .error

/-! ## §17.4.2.9 / §17.4.2.12 / §17.4.2.13 — fresh values, purely

BNODE(), UUID() and STRUUID() must return a value distinct per
solution and per call site. The caller (BIND, the SELECT projection)
injects the row index and a call-site tag under the reserved keys of
`Binding.withFreshnessCtx`; the value is SHA-256 of a seed built from
them, so it is deterministic, reproducible, and distinct wherever the
spec requires distinctness (port of `fx_uuid_of_seed` /
`fx_bnode_of_seed`). -/

/-- The first 32 hex digits of SHA-256(seed) laid out 8-4-4-4-12
(lowercase; the W3C UUID fixtures match case-insensitively). -/
def fxUuidOfSeed (seed : String) : String :=
  let cs := (Crypto.hashHex .sha256 seed).toList.take 32
  let s := fun (l : List Char) => String.ofList l
  s (cs.take 8) ++ "-" ++ s ((cs.drop 8).take 4) ++ "-" ++ s ((cs.drop 12).take 4) ++ "-" ++
  s ((cs.drop 16).take 4) ++ "-" ++ s (cs.drop 20)

/-- A fresh blank-node label; the `fxbn` prefix keeps these apart
from data blank nodes. (The F* label carries a literal `_:` prefix;
Lean blank-node labels never do, so it is omitted here.) -/
def fxBnodeOfSeed (seed : String) : String :=
  "fxbn" ++ Crypto.hashHex .sha256 seed

/-- Hash builtin body shared by MD5/SHA1/SHA256/SHA384/SHA512
(§17.4.4.7–11): the string value of the argument, hashed, as a simple
literal of lowercase hex; a non-string argument is a type error. -/
def hashResult (digest : String → String) (v : EvalResult) : EvalResult :=
  match v.toString? with
  | some s => erString (digest s)
  | none => .error

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
  -- §17.4.2.8 IRI(): a literal's lexical form is resolved against the
  -- query's BASE when there is one (RFC 3986 §5.2, `resolveIri`), as
  -- the F* arm does with `resolve_iri`; the result must be an
  -- absolute IRI.
  | .iriFn e1 =>
      match Expr.evalIn env mu e1 with
      | .term (.iri i) => .term (.iri i)
      | .term (.literal l) =>
          let s := L4Factoidal.Syntax.resolveAgainst? env.base l.val.lexicalForm
          if h : L4Factoidal.RDF.isIri s then .term (.iri ⟨s, h⟩)
          else .error
      | _ => .error

  -- §17.4.2 term constructors. STRDT takes a SIMPLE LITERAL (RDF 1.1:
  -- an `xsd:string` literal without a language tag); a tagged or
  -- otherwise-typed literal, or a promoted value, is a type error
  -- (W3C `strdt01`, `strdt03`).
  | .strDt e1 e2 =>
      match Expr.evalIn env mu e1, Expr.evalIn env mu e2 with
      | .term (.literal l), .term (.iri dt) =>
          if l.val.datatype == xsdString && l.val.langTag.isNone then
            .term (.literal (mkTypedLiteral l.val.lexicalForm dt))
          else .error
      | _, _ => .error
  | .strLang e1 e2 =>
      match Expr.evalIn env mu e1, (Expr.evalIn env mu e2).toString? with
      | .term (.literal l), some tag =>
          -- An empty language tag is not a language tag; SPARQL 1.2
          -- `lang-basedir/strlang` requires the error, and `strLangDir`
          -- below already carries the same check.
          if l.val.datatype == xsdString && l.val.langTag.isNone
              && tag.length > 0 then
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

  -- §17.4.1.2 IF: "if the EBV of expression1 raises an error, then an
  -- error is raised" — the condition's type error PROPAGATES (W3C
  -- `if02`: `IF(1/0, false, true)` is unbound), it is not folded to
  -- the else branch.
  | .cond c t e =>
      match ebv (Expr.evalIn env mu c) with
      | some true  => Expr.evalIn env mu t
      | some false => Expr.evalIn env mu e
      | none       => .error
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
      match (Expr.evalIn env mu e1).stringLiteralInfo?,
            (Expr.evalIn env mu e2).stringLiteralInfo? with
      | some (s, lang1, dt1), some (arg, lang2, dt2) =>
          if !strBeforeAfterCompatible lang1 dt1 lang2 dt2 then .error
          else if arg.length = 0 then erStringPreserve "" lang1 dt1
          else
            let result := strBeforeRaw s arg
            if result.length = 0 && !strContains s arg then erString ""
            else erStringPreserve result lang1 dt1
      | _, _ => .error
  | .strAfter e1 e2 =>
      match (Expr.evalIn env mu e1).stringLiteralInfo?,
            (Expr.evalIn env mu e2).stringLiteralInfo? with
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
  -- §17.4.3.14 REGEX / §17.4.3.15 REPLACE, over the pure XPath regex
  -- engine in `L4Factoidal.Regex` (F* `regex_match` / `regex_replace`,
  -- which the F* tree reaches through its host call-out; here a port
  -- of the same derivative engine). The text argument is a string
  -- literal (simple, xsd:string or language-tagged — `stringLiteralInfo?`);
  -- pattern, replacement and flags are simple literals. REPLACE keeps
  -- the text's language tag / datatype (`erStringPreserve`). An invalid
  -- pattern, flag or replacement template (FORX0001–FORX0004) is an
  -- expression error, as in F&O.
  | .regex e1 pat none =>
      regexCore (Expr.evalIn env mu e1) (Expr.evalIn env mu pat) (erString "")
  | .regex e1 pat (some f) =>
      regexCore (Expr.evalIn env mu e1) (Expr.evalIn env mu pat) (Expr.evalIn env mu f)
  | .replace e1 pat rep none =>
      replaceCore (Expr.evalIn env mu e1) (Expr.evalIn env mu pat) (Expr.evalIn env mu rep) (erString "")
  | .replace e1 pat rep (some f) =>
      replaceCore (Expr.evalIn env mu e1) (Expr.evalIn env mu pat) (Expr.evalIn env mu rep) (Expr.evalIn env mu f)

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

  -- §17.4.4.7–11 hash builtins: pure Lean digests of the UTF-8 bytes,
  -- lowercase hex. SHA-2 goes through the hash-agile `Crypto.hashHex`.
  | .md5 e1    => hashResult Crypto.md5Hex (Expr.evalIn env mu e1)
  | .sha1 e1   => hashResult Crypto.sha1Hex (Expr.evalIn env mu e1)
  | .sha256 e1 => hashResult (Crypto.hashHex .sha256) (Expr.evalIn env mu e1)
  | .sha384 e1 => hashResult (Crypto.hashHex .sha384) (Expr.evalIn env mu e1)
  | .sha512 e1 => hashResult (Crypto.hashHex .sha512) (Expr.evalIn env mu e1)

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
  -- §17.4.5.7 TIMEZONE: an xsd:dayTimeDuration; a dateTime with no
  -- timezone is a type error (W3C `timezone01`, row `d4` unbound).
  | .timezone e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s =>
          match dtTimezone s with
          | some "" => .error
          | some tzStr => .term (.literal (mkTypedLiteral tzStr xsdDayTimeDuration))
          | none => .error
      | none => .error
  -- §17.4.5.8 TZ: a simple literal, `""` when there is no timezone.
  | .tz e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtTz s with | some tzStr => erString tzStr | none => .error
      | none => .error

  -- §17.4.1.2 sameTerm — term IDENTITY, stricter than `=`.
  | .sameTerm e1 e2 =>
      match Expr.evalIn env mu e1, Expr.evalIn env mu e2 with
      | .term t1, .term t2 => .bool (t1.eqb t2)
      | .num a, .num b => .bool (a == b)
      | .dec a, .dec b => .bool (a == b)
      | .dbl a, .dbl b => .bool (a == b)
      | .bool a, .bool b => .bool (a == b)
      | _, _ => .bool false

  -- §18.6 EXISTS: evaluated by the pattern layer, which replaces every
  -- EXISTS sub-expression by its boolean before calling this function
  -- (`substituteExistentials`, Query.lean — the F* arm is
  -- `E_Exists _ -> ER_Error` for the same reason).
  | .existsPat _ => .error
  | .notExistsPat _ => .error

  -- SCOPED OUT: §18.5.1 aggregates evaluate over a GROUP.
  | .aggregate _ _ _ => .error

  -- IRI-named functions, dispatched in the F* arm's order: langMatches
  -- (§17.4.3.10); RAND / UUID / STRUUID / BNODE (the parser maps the
  -- keywords to `fn:` IRIs); the §17.5 `xsd:` constructor functions;
  -- then the §17.6 host registry, where an unregistered IRI is the
  -- spec-required type error.
  | .functionCall i args =>
      let vals := Expr.evalArgs env mu args
      let iriS := i.val
      if i == langMatchesIri then
        match vals with
        | [v1, v2] =>
            match v1.toString?, v2.toString? with
            | some tag, some range => .bool (fnLangMatches tag range)
            | _, _ => .error
        | _ => .error
      -- §17.4.4.3 RAND(): the F* tree's fixed value — a double in
      -- [0, 1), deterministic by design (stated in the banner).
      else if iriS == fnNamespace ++ "rand" then .dbl "0.5"
      -- §17.4.2.12 UUID(): a fresh `urn:uuid:` IRI per (row, call site).
      else if iriS == fnNamespace ++ "uuid" then
        let row := mu.freshnessCtx fxKeyRow
        let occ := mu.freshnessCtx fxKeyOcc
        let u := "urn:uuid:" ++ fxUuidOfSeed ("u|" ++ row ++ "|" ++ occ)
        if h : L4Factoidal.RDF.isIri u then .term (.iri ⟨u, h⟩) else .error
      -- §17.4.2.13 STRUUID(): the same value as a simple literal.
      else if iriS == fnNamespace ++ "struuid" then
        let row := mu.freshnessCtx fxKeyRow
        let occ := mu.freshnessCtx fxKeyOcc
        erString (fxUuidOfSeed ("u|" ++ row ++ "|" ++ occ))
      -- §17.4.2.9 BNODE(): distinct across solutions AND across call
      -- sites within one solution; BNODE(str): the same label for the
      -- same string within one solution, distinct across solutions.
      else if iriS == fnNamespace ++ "bnode" then
        let row := mu.freshnessCtx fxKeyRow
        match vals with
        | [] =>
            let occ := mu.freshnessCtx fxKeyOcc
            .term (.bnode (fxBnodeOfSeed ("n|" ++ row ++ "|" ++ occ)))
        | [v1] =>
            match v1.toString? with
            | some s => .term (.bnode (fxBnodeOfSeed ("s|" ++ row ++ "|" ++ s)))
            | none => .error
        | _ => .error
      -- §17.5 `xsd:<type>(v)`.
      else if xsdNamespace.isPrefixOf iriS && iriS.length > xsdNamespace.length then
        match vals with
        | [v1] => evalXsdCast v1 (String.ofList (iriS.toList.drop xsdNamespace.length)) i
        | _ => .error
      else
        match env.ext iriS vals with
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
`Graph → Binding → Bool` (the active graph is what an EXISTS inside
the condition is evaluated against; `Query.lean` builds those
conditions). §18.5 says a row survives FILTER when its expression
"has an effective boolean value of true", so a type error is
indistinguishable from `false` at that boundary. `Expr.toCond` is
exactly that collapse — and it is where §17's careful error PRESERVING
finally stops mattering. This bridge evaluates under `emptyEnv`, so an
EXISTS in `e` is the expression-layer error; the full pipeline is
`QueryPattern.lower`. -/

def Expr.toCond (e : Expr) : Binding → Bool := fun mu => (ebv (e.eval mu)).getD false

/-- FILTER(expr) as an algebra operation (§18.5). -/
def GraphPattern.filterExpr (e : Expr) (p : GraphPattern) : GraphPattern :=
  .filter (fun _ => e.toCond) p

/-- OPTIONAL with a filter: LeftJoin(P1, P2, expr) (§18.5). -/
def GraphPattern.leftJoinExpr (l r : GraphPattern) (e : Expr) : GraphPattern :=
  .leftJoin l r (fun _ => e.toCond)

end L4Factoidal.SPARQL
