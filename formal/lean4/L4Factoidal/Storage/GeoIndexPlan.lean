/-
L4Factoidal.Storage.GeoIndexPlan — which SPARQL queries the GBI1 geometry
bounding-box index may serve, and what a planner may do with its candidates.

Design record: `docs/designissues/2026-09-05-geometry-bounding-box-index.md`,
section 4. This module is the DECISION; `Wasm/Ops/StoreHandles.lean` only
carries bytes and rows. It is `LiteralIndexPlan` with a geometry in place of a
needle, and it makes the same promise.

## What the index does, and does not, decide

`GeoBBoxIndex.candidates?` returns a SUPERSET of the dictionary terms the
exact GeoSPARQL predicate accepts (`GeoBBoxIndex.mem_candidatesSpec`). It
decides no row. A planner that uses it restricts the rows it materialises and
then evaluates the ORIGINAL, UNMODIFIED query over them, so the answer is the
scan's answer whenever the restriction drops only rows that cannot appear in a
solution.

A bounding box is a CONSERVATIVE approximation. Non-overlapping boxes prove
the geometries share no point; overlapping boxes prove nothing. So a box can
exclude and can never confirm, and the re-evaluation is not optional.

## `geof:sfDisjoint` is refused

`sfDisjoint` accepts exactly the rows a box can exclude, so the box test
inverts there. `plan?` gives it `none` and the caller scans. Section 4.1 of
the design record has the argument.

## The five that are served

`sfIntersects`, `sfWithin`, `sfContains`, `sfTouches` and `sfEquals`, each
against a CONSTANT `geo:wktLiteral` whose geometry is inside the proved
fragment. `GeoBBoxIndex.candidates?` applies the fragment test itself and
answers `none` when the query geometry is outside it, so this module does not
restate the fragment.

## The argument order is read, not assumed

`geof:sfWithin(?geo, Q)` and `geof:sfWithin(Q, ?geo)` are different
predicates. The index entry is judged by `GeoBBoxIndex.evalTerm op t query`,
which computes `op.fn t Q` — the variable FIRST. A query that writes the
constant first is served by the CONVERSE operation, which for these five is
`sfWithin`/`sfContains` swapped and the other three unchanged, because
`sfIntersects`, `sfTouches` and `sfEquals` are symmetric in Simple Features.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.GeoBBoxIndex
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.Storage.GeoIndexPlan

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Geo
open L4Factoidal.Storage.GeoBBoxIndex

/-- What the planner may do with one admitted query. -/
structure Plan where
  /-- The predicate whose block the restriction applies to. -/
  predicate : WfIri
  /-- The operation the index is asked for, with the row geometry FIRST. -/
  op : GeoOp
  /-- The constant query geometry, parsed once at plan time. -/
  query : WktValue
  deriving Repr

/-- The six `geof:` local names, and `none` for anything else in that
    namespace or outside it.

    The local part is compared with `==` in an `if` chain, which is the shape
    `Geo.extFns` uses to dispatch the same six names. A `match` on string
    LITERALS does not work here: `String.drop` answers a `String.Slice` in
    this toolchain, and a slice never matches a string-literal pattern, so
    every name fell through to `none` and the index served nothing. -/
def opOfIri (iri : WfIri) : Option GeoOp :=
  if !(iri.val.startsWith geofNs) then none
  else
    let name := iri.val.drop geofNs.length
    if name == "sfEquals" then some .equals
    else if name == "sfWithin" then some .within
    else if name == "sfContains" then some .contains
    else if name == "sfIntersects" then some .intersects
    else if name == "sfTouches" then some .touches
    else if name == "sfDisjoint" then some .disjoint
    else none

/-- The operation with its two arguments exchanged. `sfIntersects`,
    `sfTouches` and `sfEquals` are symmetric; `sfWithin` and `sfContains` are
    each other's converse. `sfDisjoint` is symmetric and is refused anyway. -/
def converse : GeoOp → GeoOp
  | .within => .contains
  | .contains => .within
  | .equals => .equals
  | .intersects => .intersects
  | .touches => .touches
  | .disjoint => .disjoint

/-- A constant `geo:wktLiteral` argument, parsed. This is `GeoBBoxIndex.termWkt`
    on a literal the query wrote out, so the datatype gate is the evaluator's
    gate and is not restated. -/
def constantGeometry? : Expr → Option WktValue
  | .lit l => termWkt (.literal l)
  | _ => none

/-- The object variable read bare. `STR`, `LCASE` and the rest are absent on
    purpose: `Geo.wktArg` refuses anything but a `geo:wktLiteral` term, so a
    wrapped argument is a type error and the row is excluded either way, and
    admitting a shape whose meaning the index does not model is how a
    candidate filter starts dropping rows. -/
def objectVar? (v : VarName) : Expr → Bool
  | .var w => w == v
  | _ => false

/-- One `geof:` call that admits the index, if the expression carries one.
    `&&` is searched on both sides, as `LiteralIndexPlan` searches it: `A && B`
    is true only when both are, so either conjunct restricts the rows. `||` is
    NOT searched and neither is `!`. -/
def callIn? (v : VarName) : Expr → Option (GeoOp × WktValue)
  | .and left right =>
      match callIn? v left with
      | some found => some found
      | none => callIn? v right
  | .functionCall iri [a, b] => do
      let op ← opOfIri iri
      if op == GeoOp.disjoint then none
      else if objectVar? v a then
        let query ← constantGeometry? b
        some (op, query)
      else if objectVar? v b then
        let query ← constantGeometry? a
        some (converse op, query)
      else none
  | _ => none

/-- `?s <P> ?o` under one filter: the only pattern shape admitted, and the
    same one `LiteralIndexPlan` admits. -/
def filteredSinglePattern? : QueryPattern → Option (WfIri × VarName × Expr)
  | .filter cond (.bgp [triple]) =>
      match triple.p, triple.o with
      | .iri predicate, .var v => some (predicate, v, cond)
      | _, _ => none
  | _ => none

/-- One optional `GRAPH` layer is stripped, named or variable, for the reason
    `LiteralIndexPlan.strippedPattern?` strips it: an IBK4 block holds one
    predicate across every graph, and the body is a non-empty BGP. -/
def strippedPattern? : QueryPattern → Option (WfIri × VarName × Expr)
  | .graph _ inner => filteredSinglePattern? inner
  | pattern => filteredSinglePattern? pattern

/-- The geometry plan of one query, or `none` to scan.

    The two whole-query guards are `LiteralIndexPlan.plan?`'s and hold for the
    same reasons: a `FROM` / `FROM NAMED` clause rebuilds the default graph
    (section 13.2), and an `EXISTS` in the projection, a GROUP BY key, a
    HAVING condition or an ORDER BY condition is evaluated against the active
    graph (section 18.6), so it reads rows this restriction would drop. -/
def plan? (query : Query) : Option Plan :=
  if !query.dataset.isEmpty || !query.expressionsOutsidePatternExistsFree then none
  else do
    let (predicate, v, cond) ← strippedPattern? query.pattern
    let (op, geometry) ← callIn? v cond
    some { predicate, op, query := geometry }

/-! ## Executable pins

The rejections are what keep the answer the scan's answer, so each one is
pinned here beside the shape it refuses. -/

private def parse (text : String) : Option Query :=
  match parseSparql text with
  | .ok query => some query
  | .error _ => none

private def planned (text : String) : Option Plan :=
  (parse text).bind plan?

private def asWkt : String := "<http://www.opengis.net/ont/geosparql#asWKT>"
private def wktType : String := "^^<" ++ wktLiteralIri ++ ">"
private def geof (name : String) : String := "<" ++ geofNs ++ name ++ ">"
private def square : String := "POLYGON((0 0, 10 0, 10 10, 0 10, 0 0))"

private def shape (name arg1 arg2 : String) : String :=
  s!"SELECT ?s ?o WHERE \{ ?s {asWkt} ?o FILTER({geof name}({arg1}, {arg2})) }"

private def constant : String := "\"" ++ square ++ "\"" ++ wktType

#guard (planned (shape "sfWithin" "?o" constant)).map Plan.op == some GeoOp.within
#guard (planned (shape "sfIntersects" "?o" constant)).map Plan.op == some GeoOp.intersects
#guard (planned (shape "sfContains" "?o" constant)).map Plan.op == some GeoOp.contains
#guard (planned (shape "sfTouches" "?o" constant)).map Plan.op == some GeoOp.touches
#guard (planned (shape "sfEquals" "?o" constant)).map Plan.op == some GeoOp.equals
-- The constant written FIRST is the converse operation, not the same one.
#guard (planned (shape "sfWithin" constant "?o")).map Plan.op == some GeoOp.contains
#guard (planned (shape "sfContains" constant "?o")).map Plan.op == some GeoOp.within
#guard (planned (shape "sfIntersects" constant "?o")).map Plan.op == some GeoOp.intersects
-- A conjunct of `&&` is enough.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {asWkt} ?o FILTER(isLiteral(?o) && {geof "sfWithin"}(?o, {constant})) }").map
  Plan.op == some GeoOp.within
-- One GRAPH layer is stripped, named or variable.
#guard (planned s!"SELECT ?s ?o WHERE \{ GRAPH <https://example.test/g> \{ ?s {asWkt} ?o FILTER({geof "sfWithin"}(?o, {constant})) } }").map
  Plan.op == some GeoOp.within
#guard (planned s!"SELECT ?g ?s WHERE \{ GRAPH ?g \{ ?s {asWkt} ?o FILTER({geof "sfWithin"}(?o, {constant})) } }").map
  Plan.op == some GeoOp.within

-- Every refusal below falls back to the scan.
-- `sfDisjoint` accepts exactly the rows a box excludes.
#guard (planned (shape "sfDisjoint" "?o" constant)).isNone
-- A variable query geometry: no box at plan time.
#guard (planned (shape "sfWithin" "?o" "?q")).isNone
-- A plain string is not a `geo:wktLiteral`; `Geo.wktArg` refuses it.
#guard (planned (shape "sfWithin" "?o" "\"POINT(1 1)\"")).isNone
-- An unparseable lexical form.
#guard (planned (shape "sfWithin" "?o" ("\"NOT WKT\"" ++ wktType))).isNone
-- A `geof:` function that is not one of the six.
#guard (planned (shape "distance" "?o" constant)).isNone
-- Negation and disjunction: the complement of a superset is not a superset.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {asWkt} ?o FILTER(!{geof "sfWithin"}(?o, {constant})) }").isNone
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {asWkt} ?o FILTER({geof "sfWithin"}(?o, {constant}) || isIRI(?o)) }").isNone
-- A filter on a variable the pattern does not bind in object position.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {asWkt} ?o FILTER({geof "sfWithin"}(?s, {constant})) }").isNone
-- A wrapped object argument is a type error to `Geo.wktArg`; the index does
-- not model it and does not claim it.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {asWkt} ?o FILTER({geof "sfWithin"}(STR(?o), {constant})) }").isNone
-- A second triple pattern: the restriction would have to reason about a join.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {asWkt} ?o . ?s <https://example.test/q> ?z FILTER({geof "sfWithin"}(?o, {constant})) }").isNone
-- No filter at all, and a variable predicate the plan cannot name.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {asWkt} ?o }").isNone
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s ?p ?o FILTER({geof "sfWithin"}(?o, {constant})) }").isNone
-- FROM rebuilds the default graph; the EXISTS guard is section 18.6's.
#guard (planned s!"SELECT ?s ?o FROM <https://example.test/g> WHERE \{ ?s {asWkt} ?o FILTER({geof "sfWithin"}(?o, {constant})) }").isNone
#guard (planned s!"SELECT ?s (EXISTS \{ ?s ?q ?r } AS ?e) WHERE \{ ?s {asWkt} ?o FILTER({geof "sfWithin"}(?o, {constant})) }").isNone

/-! ### The converse table is the evaluator's, not a guess

`converse op` is pinned against `Geo.extFns` on the pair the swap is for: with
the arguments exchanged, the converse operation gives the same answer. -/

private def wkt (s : String) : Term :=
  .literal ⟨⟨s, ⟨wktLiteralIri, by rfl⟩, none, none⟩, by rfl⟩

private def sameAnswer (op : GeoOp) (a b : String) : Bool :=
  extFns (geofNs ++ op.localName) [.term (wkt a), .term (wkt b)] ==
    extFns (geofNs ++ (converse op).localName) [.term (wkt b), .term (wkt a)]

#guard sameAnswer GeoOp.within "POINT(1 1)" square
#guard sameAnswer GeoOp.contains square "POINT(1 1)"
#guard sameAnswer GeoOp.intersects "POINT(0 0)" square
#guard sameAnswer GeoOp.touches "POINT(0 0)" square
#guard sameAnswer GeoOp.equals "POINT(1 1)" "POINT(1 1)"
#guard sameAnswer GeoOp.within "POINT(50 50)" square

end L4Factoidal.Storage.GeoIndexPlan
