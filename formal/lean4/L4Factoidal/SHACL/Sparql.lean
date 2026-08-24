/-
L4Factoidal.SHACL.Sparql — SHACL-SPARQL (SHACL Part 2), the evaluator.

W3C SHACL Recommendation (20 July 2017), https://www.w3.org/TR/shacl/:

  * §5.1  `sh:sparql` constraints with `sh:select`;
  * §5.2  `sh:prefixes` / `sh:declare` (decoded in `Shapes.lean`, which
          prepends the `PREFIX` header to the query text);
  * §5.3  pre-binding of `$this`, and §5.3.1's `$shapesGraph` /
          `$currentShape` / `$value` / `$PATH`;
  * §5.3.2 the pre-binding restrictions that make a query ill-formed —
          "must be rejected with a failure", which the test suite
          records as `sht:Failure`;
  * §6    SPARQL-based constraint components: `sh:parameter`,
          `sh:validator` / `sh:nodeValidator` / `sh:propertyValidator`,
          §6.2.1 `sh:ask` validators (per value node), §6.2.2
          `sh:select` validators (per focus node), §6.3 the `{?param}`
          message template.

Port of `formal/fstar/SHACL.Validation.fst` sections 11k–11l
(`subst_var_*`, `subst_vars_gp`, `prebinding_unsupported`,
`sparql_violations_for_*`, `eval_custom_component_ask` / `_select`,
`custom_violations_for_*`) and section 13's `validate` failure channel.

Not ported: the SPARQL-based TARGET (`sh:target [ sh:select … ]`,
SHACL-AF). `Shapes.lean` records it in `ShapesGraph.unsupported` so the
harness names it. The F\* `assume val eval_sparql_target_select` exists
only because `SHACL.Validation.fst` precedes the SPARQL evaluator in
the F\* module order; here SHACL imports SPARQL, so nothing corresponds
to it.

## How pre-binding is implemented, and why

SHACL §5.3 says a pre-bound variable "is substituted with the
[pre-bound] value" before the query is evaluated. Two implementations
are possible: substitute the value into the query, or join a
one-row initial binding onto the WHERE-clause result. **This port
substitutes into the parsed query** — the concrete `QueryPattern` /
`Expr` AST that `SPARQL/Parser.lean` produces, before
`QueryPattern.lower` turns filter conditions into closures — exactly
as the F\* `subst_vars_gp` does, and exactly as `SPARQL/Exists.lean`
substitutes a solution mapping into an EXISTS body.

A post-hoc join is not enough. `pre-binding-001`'s whole WHERE clause
is `FILTER ($this = ex:InvalidResource)`: with a join, `$this` is
unbound while the FILTER runs and the query yields nothing. The
variable has to be visible INSIDE the pattern — in FILTER, in BIND, in
BGP positions, inside GRAPH and EXISTS alike. `Expr.bound v` for a
pre-bound `v` therefore becomes `Expr.boolLit true`
(`shapesGraph-001`'s `FILTER bound($shapesGraph)`).

A one-row `postValues` binding is joined on TOP of the substitution,
for the projection only: `SELECT $this WHERE { … }` must still carry
`$this` in its result rows after every occurrence inside the pattern
has been replaced by a term.

Substitution and pre-binding agree exactly BECAUSE of the §5.3.2
restrictions, which is why an ill-formed query is a failure rather
than a best effort:

  * `MINUS` — §18.5's domain-disjointness test reads the RHS variable
    domain; substituting a variable away changes that domain, so
    substitution and pre-binding differ. Rejected.
  * `SERVICE` — the remote endpoint evaluates the pattern itself and
    never sees our substitution. Rejected. (`LATERAL`, a SPARQL 1.2
    addition this AST carries, is rejected for the same reason its
    RHS is built per-row from the left solution, not substituted.)
  * `VALUES` on a pre-bound variable — a second, conflicting source of
    bindings for the same name. Rejected wherever it appears, in the
    pattern or as the query's trailing block.
  * a sub-`SELECT` that does not project a pre-bound variable — the
    variable is out of scope outside the sub-select, so substituting
    inside it invents a correlation the query does not have.
    `SELECT *` counts as not projecting (`pre-binding-006` fails,
    `pre-binding-007` passes).
  * assignment to a pre-bound variable, `BIND(… AS $this)` or
    `SELECT (… AS $this)` — re-binding what is already bound.

Everything above is a total function of its inputs: the failure
channel is an `Option String` in the report, never an exception.
-/
import L4Factoidal.SHACL.Validation
import L4Factoidal.SPARQL.Parser

open L4Factoidal.RDF
open L4Factoidal.SPARQL

namespace L4Factoidal.SHACL

/-! ## §5.3 pre-binding by AST substitution

One substitution engine, parameterised over the variable name being
replaced (F\* `subst_var_*`, generalised from `$this` when the §6
constraint components needed the same walk for `$value` and each
`sh:parameter` variable). -/

/-- A subject position takes an IRI or a blank node; a literal or a
triple term has no subject form, so the variable is left in place
(the pattern then simply matches nothing — sound by omission). -/
def substVarSubject (name : VarName) (t : Term) (ps : PatternSubject) : PatternSubject :=
  match ps with
  | .var v =>
    if v == name then
      match t with
      | .iri i => .iri i
      | .bnode b => .bnode b
      | _ => ps
    else ps
  | _ => ps

/-- An object / predicate position takes any term except a triple term
(the pattern AST has no triple-term literal form for it). -/
def substVarTerm (name : VarName) (t : Term) : PatternTerm → PatternTerm
  | .var v =>
    if v == name then
      match t with
      | .iri i => .iri i
      | .bnode b => .bnode b
      | .literal l => .literal l
      | .tripleTerm _ _ _ => .var v
    else .var v
  | .tripleTerm s p o =>
    .tripleTerm (substVarTerm name t s) (substVarTerm name t p) (substVarTerm name t o)
  | pt => pt

def substVarTP (name : VarName) (t : Term) (tp : TriplePattern) : TriplePattern :=
  { s := substVarSubject name t tp.s,
    p := substVarTerm name t tp.p,
    o := substVarTerm name t tp.o }

/-- The expression form of a term (F\* `term_to_expr_opt`): a blank
node and a triple term have none, so an `Expr.var` for them is left
alone.

A pre-bound variable must behave in an expression EXACTLY as the same
binding would in the solution mapping, so a numeric or boolean literal
becomes the promoted `Expr` constructor, not `Expr.lit`. `Expr.var`
promotes a literal binding through `literalPromote` (SPARQL §17.1),
while `Expr.lit` does not — substituting `Expr.lit "5"^^xsd:integer`
into `FILTER($value <= $maxVal)` would compare the two LEXICALLY and
answer `"5" > "10"`. `termToExpr_evalIn_eq_literalPromote`
(`SparqlTheorems.lean`) pins the agreement. The F\* `term_to_expr_opt`
returns the un-promoted `E_Literal` and has the same lexical-compare
exposure (`SPARQL11.Algebra.fst:4013`); the vendored SHACL-SPARQL
fixtures do not exercise it. -/
def termToExpr? : Term → Option Expr
  | .iri i => some (.iri i)
  | .literal l =>
    if l.val.datatype == RDF.xsdInteger then
      match parseIntString l.val.lexicalForm with
      | some n => some (.numericLit n)
      | none => some (.lit l)
    else if l.val.datatype == RDF.xsdDecimal then some (.decimalLit l.val.lexicalForm)
    else if l.val.datatype == RDF.xsdDouble || l.val.datatype == SPARQL.xsdFloat then
      some (.doubleLit l.val.lexicalForm)
    else if l.val.datatype == RDF.xsdBoolean then
      -- Valid lexical forms only, matching `literalPromote`: an
      -- ill-formed boolean stays a term literal so its type errors
      -- surface, exactly as an unsubstituted binding's would.
      match l.val.lexicalForm with
      | "true" | "1" => some (.boolLit true)
      | "false" | "0" => some (.boolLit false)
      | _ => some (.lit l)
    else some (.lit l)
  | _ => none

mutual
  /-- Substitute `name := t` through an expression. Constructors with
  no expression or pattern child fall through the final wildcard.
  `BOUND(?name)` becomes `true`: the variable IS bound, by
  pre-binding (§5.3). -/
  def substVarExpr (name : VarName) (t : Term) : Expr → Expr
    | .var v => if v == name then (match termToExpr? t with
                                   | some e => e
                                   | none => .var v)
                else .var v
    | .bound v => if v == name then .boolLit true else .bound v
    | .arith op l r => .arith op (substVarExpr name t l) (substVarExpr name t r)
    | .unaryMinus e => .unaryMinus (substVarExpr name t e)
    | .unaryPlus e => .unaryPlus (substVarExpr name t e)
    | .compare op l r => .compare op (substVarExpr name t l) (substVarExpr name t r)
    | .and l r => .and (substVarExpr name t l) (substVarExpr name t r)
    | .or l r => .or (substVarExpr name t l) (substVarExpr name t r)
    | .not e => .not (substVarExpr name t e)
    | .isIri e => .isIri (substVarExpr name t e)
    | .isBlank e => .isBlank (substVarExpr name t e)
    | .isLiteral e => .isLiteral (substVarExpr name t e)
    | .isNumeric e => .isNumeric (substVarExpr name t e)
    | .str e => .str (substVarExpr name t e)
    | .lang e => .lang (substVarExpr name t e)
    | .datatype e => .datatype (substVarExpr name t e)
    | .iriFn e => .iriFn (substVarExpr name t e)
    | .hasLang e => .hasLang (substVarExpr name t e)
    | .hasLangDir e => .hasLangDir (substVarExpr name t e)
    | .langDir e => .langDir (substVarExpr name t e)
    | .strDt l d => .strDt (substVarExpr name t l) (substVarExpr name t d)
    | .strLang l g => .strLang (substVarExpr name t l) (substVarExpr name t g)
    | .strLangDir l g d =>
      .strLangDir (substVarExpr name t l) (substVarExpr name t g) (substVarExpr name t d)
    | .cond c a b =>
      .cond (substVarExpr name t c) (substVarExpr name t a) (substVarExpr name t b)
    | .coalesce es => .coalesce (substVarExprs name t es)
    | .inList e es => .inList (substVarExpr name t e) (substVarExprs name t es)
    | .notInList e es => .notInList (substVarExpr name t e) (substVarExprs name t es)
    | .strLen e => .strLen (substVarExpr name t e)
    | .substr e s l =>
      .substr (substVarExpr name t e) (substVarExpr name t s) (substVarExprOpt name t l)
    | .uCase e => .uCase (substVarExpr name t e)
    | .lCase e => .lCase (substVarExpr name t e)
    | .strStarts e p => .strStarts (substVarExpr name t e) (substVarExpr name t p)
    | .strEnds e p => .strEnds (substVarExpr name t e) (substVarExpr name t p)
    | .contains e p => .contains (substVarExpr name t e) (substVarExpr name t p)
    | .strBefore e p => .strBefore (substVarExpr name t e) (substVarExpr name t p)
    | .strAfter e p => .strAfter (substVarExpr name t e) (substVarExpr name t p)
    | .concat es => .concat (substVarExprs name t es)
    | .encodeForUri e => .encodeForUri (substVarExpr name t e)
    | .replace e p r fl =>
      .replace (substVarExpr name t e) (substVarExpr name t p) (substVarExpr name t r)
        (substVarExprOpt name t fl)
    | .regex e p fl =>
      .regex (substVarExpr name t e) (substVarExpr name t p) (substVarExprOpt name t fl)
    | .abs e => .abs (substVarExpr name t e)
    | .round e => .round (substVarExpr name t e)
    | .ceil e => .ceil (substVarExpr name t e)
    | .floor e => .floor (substVarExpr name t e)
    | .md5 e => .md5 (substVarExpr name t e)
    | .sha1 e => .sha1 (substVarExpr name t e)
    | .sha256 e => .sha256 (substVarExpr name t e)
    | .sha384 e => .sha384 (substVarExpr name t e)
    | .sha512 e => .sha512 (substVarExpr name t e)
    | .year e => .year (substVarExpr name t e)
    | .month e => .month (substVarExpr name t e)
    | .day e => .day (substVarExpr name t e)
    | .hours e => .hours (substVarExpr name t e)
    | .minutes e => .minutes (substVarExpr name t e)
    | .seconds e => .seconds (substVarExpr name t e)
    | .timezone e => .timezone (substVarExpr name t e)
    | .tz e => .tz (substVarExpr name t e)
    | .sameTerm l r => .sameTerm (substVarExpr name t l) (substVarExpr name t r)
    | .existsPat p => .existsPat (substVarPattern name t p)
    | .notExistsPat p => .notExistsPat (substVarPattern name t p)
    | .aggregate fn d e => .aggregate fn d (substVarExpr name t e)
    | .functionCall i args => .functionCall i (substVarExprs name t args)
    | .tripleTerm s p o =>
      .tripleTerm (substVarExpr name t s) (substVarExpr name t p) (substVarExpr name t o)
    | .ttSubject e => .ttSubject (substVarExpr name t e)
    | .ttPredicate e => .ttPredicate (substVarExpr name t e)
    | .ttObject e => .ttObject (substVarExpr name t e)
    | .isTriple e => .isTriple (substVarExpr name t e)
    | e => e

  def substVarExprs (name : VarName) (t : Term) : List Expr → List Expr
    | [] => []
    | e :: rest => substVarExpr name t e :: substVarExprs name t rest

  def substVarExprOpt (name : VarName) (t : Term) : Option Expr → Option Expr
    | none => none
    | some e => some (substVarExpr name t e)

  /-- Substitute `name := t` through a graph pattern (F\*
  `subst_var_gp`). `VALUES`, `SERVICE` and `LATERAL` are left
  untouched — `prebindingUnsupported` rejects a query containing them
  before this walk is ever reached, so leaving them alone can never
  produce a silently different answer. -/
  def substVarPattern (name : VarName) (t : Term) : QueryPattern → QueryPattern
    | .bgp b => .bgp (substVarBgp name t b)
    | .join l r => .join (substVarPattern name t l) (substVarPattern name t r)
    | .leftJoin l r c =>
      .leftJoin (substVarPattern name t l) (substVarPattern name t r) (substVarExpr name t c)
    | .filter c p => .filter (substVarExpr name t c) (substVarPattern name t p)
    | .union l r => .union (substVarPattern name t l) (substVarPattern name t r)
    | .minus l r => .minus (substVarPattern name t l) (substVarPattern name t r)
    | .graph n p => .graph (substVarTerm name t n) (substVarPattern name t p)
    | .bind e v p => .bind (substVarExpr name t e) v (substVarPattern name t p)
    -- The `Query.mk` pattern is matched open rather than going through
    -- `Query.pattern`, so the recursive argument stays a visible
    -- subterm for the termination checker (the F\* uses the
    -- `Mkquery?.q_pattern` projector for the same reason).
    | .subSelect (.mk f d p gb h m pv b) =>
      .subSelect (.mk f d (substVarPattern name t p) gb h m pv b)
    | .propertyPath s pp o =>
      .propertyPath (substVarSubject name t s) pp (substVarTerm name t o)
    | p => p

  def substVarBgp (name : VarName) (t : Term) : Bgp → Bgp
    | [] => []
    | tp :: rest => substVarTP name t tp :: substVarBgp name t rest
end

/-- Fold a whole binding list through the substitution above. Order is
irrelevant: each step rewrites occurrences of its OWN variable name
only, and a substituted position is a term, never a variable. -/
def substVarsPattern : List (VarName × Term) → QueryPattern → QueryPattern
  | [], p => p
  | (name, t) :: rest, p => substVarsPattern rest (substVarPattern name t p)

/-! ## §5.3.2 the pre-binding restrictions -/

/-- The variables SHACL pre-binds and therefore forbids re-binding
(§5.3.1: `$this`, `$value`, `$PATH`; `$PATH` reaches the query as a
textual path substitution, and `path` is its variable spelling in the
solution rows). -/
def preboundVarNames : List VarName := ["this", "value", "path"]

def selectItemProjectsThis : SelectItem → Bool
  | .var v => v == "this"
  | _ => false

def selectItemAssignsPrebound : SelectItem → Bool
  | .expr _ v => preboundVarNames.contains v
  | _ => false

/-- `none` when the pattern may be pre-bound; `some why` when SHACL
§5.3.2 requires the query to be rejected with a failure. -/
def prebindingUnsupported : QueryPattern → Option String
  | .minus _ _ => some "MINUS is not supported with pre-bound variables"
  | .lateral _ _ => some "LATERAL is not supported with pre-bound variables"
  | .service _ _ _ => some "SERVICE is not supported with pre-bound variables"
  | .serviceVar _ _ _ => some "SERVICE is not supported with pre-bound variables"
  | .values _ _ => some "VALUES is not supported with pre-bound variables"
  | .bind _ v p =>
    if preboundVarNames.contains v then some "assignment to a pre-bound variable"
    else prebindingUnsupported p
  | .subSelect (.mk f _ p _ _ _ _ _) =>
    match f with
    | .select (.vars items) =>
      if items.any selectItemAssignsPrebound then
        some "assignment to a pre-bound variable in a nested SELECT"
      else if items.any selectItemProjectsThis then prebindingUnsupported p
      else some "nested SELECT does not project $this"
    | _ => some "nested SELECT does not project $this"
  | .join l r => match prebindingUnsupported l with
                 | some m => some m
                 | none => prebindingUnsupported r
  | .leftJoin l r _ => match prebindingUnsupported l with
                       | some m => some m
                       | none => prebindingUnsupported r
  | .union l r => match prebindingUnsupported l with
                  | some m => some m
                  | none => prebindingUnsupported r
  | .filter _ p => prebindingUnsupported p
  | .graph _ p => prebindingUnsupported p
  | _ => none

/-- The whole query: its trailing `VALUES` block (§10.2) is a second
source of bindings for a pre-bound variable, so it is rejected before
the pattern is even walked (F\* `query_values_of`). -/
def queryPrebindingUnsupported (q : Query) : Option String :=
  if q.postValues.isSome then some "VALUES is not supported with pre-bound variables"
  else prebindingUnsupported q.pattern

/-- Replace a query's pattern and install a one-row pre-binding as the
trailing `VALUES` block, so a `SELECT $this` projection keeps the
binding after every in-pattern occurrence has been substituted away.
Blank-node and triple-term values have no `VALUES` form in the row and
are dropped from it (the in-pattern substitution already handled
them). -/
def queryWithPrebinding (q : Query) (binds : List (VarName × Term)) : Query :=
  let row : Binding := binds
  .mk q.form q.dataset (substVarsPattern binds q.pattern)
     q.groupBy q.having q.modifier (some [row]) q.base

/-! ## §5.3.1 `$PATH`

The one spec-sanctioned TEXTUAL substitution: "the only legal use of
the variable PATH … is in the predicate position of a triple pattern",
so `$PATH` is replaced by the property shape's own path rendered in
SPARQL 1.1 property-path syntax. A node shape has no path, and a query
that mentions `$PATH` without one is left unsubstituted — an inert
token, never a fabricated path. Port of `path_to_sparql_expr` /
`substitute_path`. -/

mutual
  /-- The path as a SPARQL property-path expression. -/
  def pathToSparql : Path → String
    | .pred i => "<" ++ i.val ++ ">"
    | .inverse p => "^" ++ pathToSparqlAtom p
    | .seq ps => pathListToSparql "/" ps
    | .alt ps => pathListToSparql "|" ps
    | .zeroOrMore p => pathToSparqlAtom p ++ "*"
    | .oneOrMore p => pathToSparqlAtom p ++ "+"
    | .zeroOrOne p => pathToSparqlAtom p ++ "?"

  /-- The parenthesised twin, so the substituted text is unambiguous
  whatever surrounds `$PATH`. Written out rather than delegating to
  `pathToSparql` on the same argument, which would not decrease. -/
  def pathToSparqlAtom : Path → String
    | .pred i => "<" ++ i.val ++ ">"
    | .inverse p => "(^" ++ pathToSparqlAtom p ++ ")"
    | .seq ps => "(" ++ pathListToSparql "/" ps ++ ")"
    | .alt ps => "(" ++ pathListToSparql "|" ps ++ ")"
    | .zeroOrMore p => "(" ++ pathToSparqlAtom p ++ "*)"
    | .oneOrMore p => "(" ++ pathToSparqlAtom p ++ "+)"
    | .zeroOrOne p => "(" ++ pathToSparqlAtom p ++ "?)"

  def pathListToSparql (sep : String) : List Path → String
    | [] => ""
    | [p] => pathToSparqlAtom p
    | p :: rest => pathToSparqlAtom p ++ sep ++ pathListToSparql sep rest
end

def substitutePath (q : String) : Option Path → String
  | none => q
  | some p => q.replace "$PATH" (pathToSparql p)

/-! ## Running one query

The dataset key `$shapesGraph` resolves through: a synthetic named
graph holding a copy of the RAW shapes graph. It never appears in a
validation report — it is an internal dataset key — so any IRI that
cannot collide with a vendored fixture's own IRIs will do. -/

def shaclInternalShapesGraphIri : WfIri :=
  ⟨"http://factoidal.example/shacl-internal#shapesGraph", rfl⟩

/-- The outcome of one SHACL-SPARQL query run: the results it produced,
or the §5.3.2 failure that stopped it. -/
structure SparqlOutcome where
  results : List Violation
  failure : Option String := none

def SparqlOutcome.empty : SparqlOutcome := { results := [] }

def SparqlOutcome.append (a b : SparqlOutcome) : SparqlOutcome :=
  { results := a.results ++ b.results,
    failure := match a.failure with | some f => some f | none => b.failure }

def SparqlOutcome.concat : List SparqlOutcome → SparqlOutcome
  | [] => .empty
  | o :: rest => o.append (SparqlOutcome.concat rest)

/-- The pre-bound query of a SHACL-SPARQL constraint (§5.3), or the
reason SHACL requires it to be rejected: a parse error, or a §5.3.2
construct that pre-binding does not support. Named separately from the
evaluation below so a specification can quantify over it. -/
def preboundQuery (queryText : String) (path : Option Path)
    (binds : List (VarName × Term)) : Except String Query :=
  match parseSparql (substitutePath queryText path) with
  | .error e => .error s!"query parse error: {e.msg}"
  | .ok q =>
    match queryPrebindingUnsupported q with
    | some why => .error s!"unsupported query: {why}"
    | none => .ok (queryWithPrebinding q binds)

/-- Run `k` on the pre-bound query. Every rejection path is a
`failure`, never an exception. -/
def withPreboundQuery (queryText : String) (path : Option Path)
    (binds : List (VarName × Term)) (what : String)
    (k : Query → SparqlOutcome) : SparqlOutcome :=
  match preboundQuery queryText path binds with
  | .error e => { results := [], failure := some (what ++ " " ++ e) }
  | .ok q => k q

/-! ## §5.1 `sh:sparql` constraints

Every SELECT solution IS a validation result. The suite's own fixtures
fix the column defaults (`node/sparql-003` has no `?value` column and
expects `sh:value` = `$this`; `property/sparql-001` has no `?path`
column and expects the property shape's own path):

  * `?value` absent → `sh:value` is the focus node;
  * `?path` absent → `sh:resultPath` is the shape's own path;
  * `?message` absent → the `sh:sparql` constraint node's own
    `sh:message`, then the owning shape's, then none. -/

/-- §5.3.1: what a `sh:sparql` constraint pre-binds — the focus node,
the shapes graph (as the internal named-graph IRI) and the owning
shape. -/
def sparqlPrebindings (focus : Term) (s : Shape) : List (VarName × Term) :=
  [("this", focus),
   ("shapesGraph", .iri shaclInternalShapesGraphIri),
   ("currentShape", shapeRefToTerm s.id)]

/-- The dataset a `sh:sparql` query runs against: the data graph as
default, the raw shapes graph under the internal `$shapesGraph` IRI. -/
def sparqlDataset (data shapesRaw : Graph) : Dataset :=
  { default := data,
    named := [{ name := .iri shaclInternalShapesGraphIri, graph := shapesRaw }] }

/-- One `sh:sparql` constraint against one focus node. -/
def sparqlViolationsForFocus (data shapesRaw : Graph) (focus : Term) (s : Shape)
    (cref : ShapeRef) (queryText : String) (cmsg : Option WfLiteral)
    (csev : Severity) : SparqlOutcome :=
  let cc := Constraint.sparql cref queryText cmsg (some csev)
  withPreboundQuery queryText s.path (sparqlPrebindings focus s) "sh:sparql" fun q =>
    { results := ((evalSelect emptyEnv (sparqlDataset data shapesRaw) q).2).map fun mu =>
        { focus := focus,
          path := match mu.lookup "path" with
                  | some (.iri p) => some (.pred p)
                  | _ => s.path,
          value := some ((mu.lookup "value").getD focus),
          sourceShape := s.id,
          constraint := cc,
          severity := csev,
          message := match mu.lookup "message" with
                     | some (.literal l) => some l
                     | _ => match cmsg with
                            | some _ => cmsg
                            | none => s.message } }

/-- Every `sh:sparql` constraint of a shape, over every focus node.
`sh:sparql` is dispatched for shapes WITH targets only; a nested
property shape's `sh:sparql` is not reached (the same slice the F\*
takes — the vendored suite has no fixture for it). -/
def sparqlViolationsForShape (data shapesRaw : Graph) (allSubjects : List Subject)
    (s : Shape) : SparqlOutcome :=
  let ccs := s.constraints.filterMap fun c =>
    match c with
    | .sparql cref q m sev => some (cref, q, m, sev.getD s.severity)
    | _ => none
  if ccs.isEmpty then .empty
  else
    SparqlOutcome.concat <|
      (shapeFocusNodes data allSubjects s).flatMap fun fn =>
        ccs.map fun (cref, q, m, sev) =>
          sparqlViolationsForFocus data shapesRaw fn s cref q m sev

/-! ## §6.3 message templates

A validator's `sh:message` may carry `{?name}` / `{$name}`
placeholders, filled from the component parameters or from the
solution row, and rendered to a plain `xsd:string`. -/

def termToPlainString : Term → String
  | .iri i => i.val
  | .bnode b => "_:" ++ b
  | .literal l => l.val.lexicalForm
  | .tripleTerm _ _ _ => ""

/-- The placeholder name up to the closing brace, and the rest. -/
def splitAtCloseBrace : List Char → Option (List Char × List Char)
  | '}' :: rest => some ([], rest)
  | c :: rest => match splitAtCloseBrace rest with
                 | some (nm, r) => some (c :: nm, r)
                 | none => none
  | [] => none

/-- Fuel bounds the walk; each step consumes at least one character. -/
def fillTemplateChars (lookup : String → Option String) : Nat → List Char → List Char
  | 0, cs => cs
  | _ + 1, [] => []
  | fuel + 1, '{' :: '?' :: rest
  | fuel + 1, '{' :: '$' :: rest =>
    match splitAtCloseBrace rest with
    | some (nm, after) =>
      (match lookup (String.ofList nm) with
       | some v => v.toList
       | none => []) ++ fillTemplateChars lookup fuel after
    | none => '{' :: fillTemplateChars lookup fuel ('?' :: rest)
  | fuel + 1, c :: rest => c :: fillTemplateChars lookup fuel rest

def fillMessageTemplate (tmpl : String) (params : List (VarName × Term))
    (mu : Binding) : WfLiteral :=
  let lookup (name : String) : Option String :=
    match params.find? (fun p => p.1 == name) with
    | some (_, t) => some (termToPlainString t)
    | none => match mu.lookup name with
              | some t => some (termToPlainString t)
              | none => none
  let cs := tmpl.toList
  Literal.string (String.ofList (fillTemplateChars lookup (cs.length + 1) cs))

/-! ## §6 SPARQL-based constraint components

§6.2.1 a `sh:ask` validator runs once per VALUE NODE and reports a
result when the ASK is false; §6.2.2 a `sh:select` validator runs once
per FOCUS NODE and every solution is a result. Both pre-bind `$this`,
`$value` (ASK only — a SELECT validator's own pattern determines
`?value`) and each `sh:parameter` variable. -/

/-- §6.2.1 / §6.2.2: what a constraint component pre-binds. An ASK
validator runs per value node and pre-binds `$value` too; a SELECT
validator's own pattern determines `?value`. -/
def customPrebindings (focus : Term) (value : Option Term)
    (params : List (VarName × Term)) : List (VarName × Term) :=
  match value with
  | some v => ("this", focus) :: ("value", v) :: params
  | none => ("this", focus) :: params

def customAskViolation (data : Graph) (focus v : Term) (s : Shape)
    (cc : Constraint) (queryText : String) (params : List (VarName × Term)) :
    SparqlOutcome :=
  withPreboundQuery queryText s.path (customPrebindings focus (some v) params)
      "constraint component" fun q =>
    if evalAsk emptyEnv { default := data, named := [] } q then .empty
    else { results := [{ focus := focus, path := s.path, value := some v,
                         sourceShape := s.id, constraint := cc,
                         severity := s.severity, message := s.message }] }

def customSelectViolations (data : Graph) (focus : Term) (s : Shape)
    (cc : Constraint) (queryText : String) (params : List (VarName × Term))
    (msgTemplate : Option String) : SparqlOutcome :=
  withPreboundQuery queryText s.path (customPrebindings focus none params)
      "constraint component" fun q =>
    { results := ((evalSelect emptyEnv { default := data, named := [] } q).2).map fun mu =>
        { focus := focus,
          path := match mu.lookup "path" with
                  | some (.iri p) => some (.pred p)
                  | _ => s.path,
          value := some ((mu.lookup "value").getD focus),
          sourceShape := s.id,
          constraint := cc,
          severity := s.severity,
          message := match msgTemplate with
                     | some tmpl => some (fillMessageTemplate tmpl params mu)
                     | none => match mu.lookup "message" with
                               | some (.literal l) => some l
                               | _ => s.message } }

def evalCustomComponent (data : Graph) (focus : Term) (s : Shape)
    (values : List Term) (cc : Constraint) : SparqlOutcome :=
  match cc with
  | .custom _ isAsk queryText params msgTemplate =>
    if isAsk then
      SparqlOutcome.concat <|
        values.map fun v => customAskViolation data focus v s cc queryText params
    else customSelectViolations data focus s cc queryText params msgTemplate
  | _ => .empty

/-- The constraint components of one shape at one occurrence, then the
same over the shape's `sh:property` shapes at their value nodes.
Unlike `sh:sparql`, a constraint component IS reached through
`sh:property` — `component/propertyValidator-select-001` and
`pre-binding/unsupported-sparql-006` both need it. -/
def customViolationsForOccurrence (data : Graph) (sg : List Shape) (node : Term)
    (s : Shape) : Nat → SparqlOutcome
  | 0 => .empty
  | fuel + 1 =>
    let values := valueNodes data node s
    let customs := s.constraints.filter fun c =>
      match c with | .custom _ _ _ _ _ => true | _ => false
    let own := SparqlOutcome.concat <|
      customs.map fun cc => evalCustomComponent data node s values cc
    let nested := SparqlOutcome.concat <|
      values.flatMap fun v =>
        s.propertyRefs.filterMap fun r =>
          match lookupShape r sg with
          | none => none
          | some ps => some (customViolationsForOccurrence data sg v ps fuel)
    own.append nested

def customViolationsForShape (data : Graph) (allSubjects : List Subject)
    (sg : List Shape) (s : Shape) (fuel : Nat) : SparqlOutcome :=
  SparqlOutcome.concat <|
    (shapeFocusNodes data allSubjects s).map fun fn =>
      customViolationsForOccurrence data sg fn s fuel

/-! ## §3.1 validation with SHACL-SPARQL

`validate` (`Validation.lean`) is SHACL Core: it sees the `.sparql` and
`.custom` constructors as inert. This entry point runs it, then the two
SHACL-SPARQL passes, and merges. A §5.3.2 failure is the report's
outcome: `conforms` / `results` are then a partial answer that the
harness does not compare (SHACL §3.6.1 gives no report for a failed
validation). -/

def validateWithSparql (data shapesRaw : Graph) (sgraph : ShapesGraph) :
    ValidationReport :=
  let core := validate data sgraph
  let shapes := sgraph.shapes
  let allSubjects := distinctSubjects data
  let fuel := validateFuel shapes
  let roots := shapes.filter fun s => !s.targets.isEmpty
  let sparqlOut := SparqlOutcome.concat <|
    roots.map fun s => sparqlViolationsForShape data shapesRaw allSubjects s
  let customOut := SparqlOutcome.concat <|
    roots.map fun s => customViolationsForShape data allSubjects shapes s fuel
  let out := sparqlOut.append customOut
  let results := core.results ++ out.results
  { conforms := results.isEmpty, results := results, failure := out.failure }

/-! ## The specification of the SHACL-SPARQL components

`Spec.Conforms` (`Validation.lean`) states SHACL Core conformance, and
`conformance_iff` proves the Core engine realises it. The SHACL-SPARQL
components CANNOT be folded into that relation: `conformance_iff` is an
`iff` against `collectShapeViolations`, which by design never evaluates
a `.sparql` or `.custom` constraint (it returns `List Violation` with
no room for the §5.3.2 failure channel — the same reason the F\*
dispatches these outside its Core mutual group). Adding a non-trivial
`FocusSatisfies` clause for them would make `conformance_iff` FALSE.

So the SHACL-SPARQL specification is a SIBLING of `Spec.Conforms`,
stated here over the same data, and `Spec.GraphConformsWithSparql`
below is the conjunction the top-level theorem targets.
`SparqlTheorems.lean` relates each predicate to its engine function. -/

namespace Spec

/-- §5.1: a focus node satisfies a `sh:sparql` constraint when the
pre-bound SELECT has no solution. A query SHACL rejects under §5.3.2
satisfies this vacuously — rejection is a FAILURE, a separate outcome
from non-conformance, carried by `SparqlOutcome.failure`. -/
def SparqlSatisfies (data shapesRaw : Graph) (focus : Term) (s : Shape)
    (queryText : String) : Prop :=
  ∀ q, preboundQuery queryText s.path (sparqlPrebindings focus s) = .ok q →
    (evalSelect emptyEnv (sparqlDataset data shapesRaw) q).2 = []

/-- §6.2.1: a value node satisfies an ASK validator when the pre-bound
ASK is true. -/
def AskValidatorSatisfies (data : Graph) (focus v : Term) (s : Shape)
    (queryText : String) (params : List (VarName × Term)) : Prop :=
  ∀ q, preboundQuery queryText s.path (customPrebindings focus (some v) params) = .ok q →
    evalAsk emptyEnv { default := data, named := [] } q = true

/-- §6.2.2: a focus node satisfies a SELECT validator when the
pre-bound SELECT has no solution. -/
def SelectValidatorSatisfies (data : Graph) (focus : Term) (s : Shape)
    (queryText : String) (params : List (VarName × Term)) : Prop :=
  ∀ q, preboundQuery queryText s.path (customPrebindings focus none params) = .ok q →
    (evalSelect emptyEnv { default := data, named := [] } q).2 = []

/-- §6: one constraint component at one occurrence, over that
occurrence's value nodes. -/
def CustomSatisfies (data : Graph) (focus : Term) (s : Shape) (values : List Term) :
    Constraint → Prop
  | .custom _ true queryText params _ =>
    ∀ v ∈ values, AskValidatorSatisfies data focus v s queryText params
  | .custom _ false queryText params _ =>
    SelectValidatorSatisfies data focus s queryText params
  | _ => True

/-- §6 through `sh:property`: a constraint component is reached at the
focus node's own occurrence and at every occurrence of every property
shape, down to the nesting budget. -/
def CustomOccurrenceConforms (data : Graph) (sg : List Shape) (node : Term) (s : Shape) :
    Nat → Prop
  | 0 => True
  | fuel + 1 =>
    let values := valueNodes data node s
    (∀ cc ∈ s.constraints, CustomSatisfies data node s values cc) ∧
    (∀ v ∈ values, ∀ r ∈ s.propertyRefs, ∀ ps, lookupShape r sg = some ps →
      CustomOccurrenceConforms data sg v ps fuel)

/-- §5.1 at shape level: every `sh:sparql` constraint of a targeted
shape, at every focus node. -/
def SparqlShapeConforms (data shapesRaw : Graph) (allSubjects : List Subject) (s : Shape) :
    Prop :=
  ∀ fn ∈ shapeFocusNodes data allSubjects s,
    ∀ cc ∈ s.constraints, ∀ cref q m sev, cc = .sparql cref q m sev →
      SparqlSatisfies data shapesRaw fn s q

/-- §3.1 with SHACL Part 2: SHACL Core conformance, plus every
`sh:sparql` constraint and every constraint component of every
targeted shape. -/
def GraphConformsWithSparql (data shapesRaw : Graph) (sg : ShapesGraph) : Prop :=
  GraphConforms data sg ∧
  (∀ s ∈ sg.shapes, s.targets ≠ [] →
     SparqlShapeConforms data shapesRaw (distinctSubjects data) s) ∧
  (∀ s ∈ sg.shapes, s.targets ≠ [] →
     ∀ fn ∈ shapeFocusNodes data (distinctSubjects data) s,
       CustomOccurrenceConforms data sg.shapes fn s (validateFuel sg.shapes))

end Spec

end L4Factoidal.SHACL
