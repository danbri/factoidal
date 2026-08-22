/-
L4Factoidal.Geo.Functions — the GeoSPARQL SPARQL extension functions,
ported from `formal/fstar/RDF.Geo.Functions.fst`.

GeoSPARQL 1.1 §9 defines its topology predicates as SPARQL functions
named by IRI (`geof:sfIntersects`, …). SPARQL 1.1 §17.6 already gives
those an extension point, and the Lean evaluator exposes it as an
ordinary field: `EvalEnv.ext : String → List EvalResult → Option
EvalResult`. So this module needs NO change to the evaluator — it
builds a function table that a caller installs:

    { EvalEnv.empty with ext := Geo.extFns }

That is the purity doctrine paying off. The F* side reaches the same
functions through a registry the evaluator consults; here the table is
an argument, so nothing global is mutated and the evaluator stays a
total function of explicit inputs.

CRS RULE, inherited: v0 performs NO coordinate transforms. Two
literals in different CRSes produce a type error rather than a
silently wrong answer computed as if the coordinates were comparable.
-/
import L4Factoidal.Geo.Wkt
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.Geo

open L4Factoidal.SPARQL

/-- The `geof:` function namespace. -/
def geofNs : String := "http://www.opengis.net/def/function/geosparql/"

/-- Pull a WKT value out of an argument: it must be a literal typed
    `geo:wktLiteral` whose lexical form parses. Anything else is a
    type error, per §17.6. -/
def wktArg : EvalResult → Option WktValue
  | .term (.literal l) =>
      if l.val.datatype.val == wktLiteralIri then Wkt.parseLiteral l.val.lexicalForm
      else none
  | _ => none

/-- Apply a general geometry predicate to two parsed literals with
    the CRS guard. A REFUSAL from the predicate (`none`) becomes a
    §17.6 type error, exactly like a bad argument — the evaluator must
    never see a guessed boolean. -/
def geoPredicate (f : Geometry → Geometry → Option Bool)
    (a b : EvalResult) : Option EvalResult := do
  let va ← wktArg a
  let vb ← wktArg b
  if !(sameCrs va.crs vb.crs) then none
  else (f va.geom vb.geom).map EvalResult.bool

/-- The function table. Install as `EvalEnv.ext`. Unregistered IRIs
    fall through to `none`, which the evaluator turns into the §17.6
    type error — never into `false`, which would silently change
    query answers. -/
def extFns (iri : String) (args : List EvalResult) : Option EvalResult :=
  if !(iri.startsWith geofNs) then none
  else
    let name := iri.drop geofNs.length
    match args with
    | [a, b] =>
        if name == "sfEquals" then geoPredicate sfEquals a b
        else if name == "sfWithin" then geoPredicate sfWithin a b
        else if name == "sfContains" then geoPredicate sfContains a b
        else if name == "sfIntersects" then geoPredicate sfIntersects a b
        else if name == "sfDisjoint" then geoPredicate sfDisjoint a b
        else if name == "sfTouches" then geoPredicate sfTouches a b
        else none
    | _ => none

end L4Factoidal.Geo
