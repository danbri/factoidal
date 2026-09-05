/-
L4Factoidal.Storage.LiteralIndexPlan — which SPARQL queries the LGI1 literal
search index may serve, and what a planner may do with its candidates.

Design record: `docs/designissues/2026-09-04-literal-token-index.md`, section
2.4. This module is the DECISION; `Wasm/Ops/StoreHandles.lean` only carries
bytes and rows.

## What the index does, and does not, decide

`LiteralGramIndex.candidates?` returns a SUPERSET of the dictionary terms
whose folded lexical form contains the folded needle
(`LiteralGramIndex.mem_candidatesSpec`). It decides no row. A planner that
uses it restricts the rows it materialises and then evaluates the ORIGINAL,
UNMODIFIED query over them, so the answer is the scan's answer whenever the
restriction drops only rows that cannot appear in a solution.

`plan?` establishes exactly that. It admits a query only when

* the whole WHERE clause is ONE triple pattern `?s <P> ?o` under ONE filter,
  bare or inside one `GRAPH` layer, so a solution EXISTS only if some row of
  `<P>` binds `?o` to a term the filter accepts, and
* a top-level conjunct of that filter is a `CONTAINS` / `STRSTARTS` /
  `STRENDS` over `?o` against a plain string literal of at least
  `gramLength` folded characters.

Everything else is `none` and the caller scans. Matching a shape the index
cannot serve is the only failure mode, so every rejection below is
load-bearing.

## The `STR` trap

`CONTAINS(STR(?o), "water")` is TRUE for an IRI whose text contains "water",
and LGI1 indexes literals only — `LiteralGramIndex.foldedOfTerm` gives a
non-literal no gram. Restricting to candidates alone would therefore DROP
those rows. `Plan.keepNonLiterals` is that fact: a shape which applies `STR`
keeps every row whose object is not a literal, and a shape which does not
drops them, because `CONTAINS(?o, "k")` on an IRI is a type error and
excludes the row anyway. This was missed by the design record's section 2.4
table, which listed the `STR` shapes as admissible with no such qualifier.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.LiteralGramIndex
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.Storage.LiteralIndexPlan

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.LiteralGramIndex

/-- What the planner may do with one admitted query. -/
structure Plan where
  /-- The predicate whose block the restriction applies to. -/
  predicate : WfIri
  /-- The needle, exactly as it was written in the query. -/
  needle : String
  /-- Keep rows whose object is NOT a literal. True for the `STR` shapes; see
  the module banner. -/
  keepNonLiterals : Bool
  deriving Repr, DecidableEq

/-- A plain string literal: no language tag, no direction, and either no
    datatype or `xsd:string`. A typed or tagged needle is refused rather than
    guessed at — the index folds a lexical form, and a needle whose value
    space is not the lexical space would make the fold mean two things. -/
def plainNeedle? (l : WfLiteral) : Option String :=
  if l.val.langTag.isNone && l.val.direction.isNone && l.val.datatype == xsdString then
    some l.val.lexicalForm
  else none

/-- The four object shapes the index serves, and whether the shape applied
    `STR`. `none` is "this expression does not read the object variable in a
    way the index can answer". -/
def objectShape? (v : VarName) : Expr → Option Bool
  | .var w => if w == v then some false else none
  | .lCase e => objectShape? v e
  | .str e => (objectShape? v e).map (fun _ => true)
  | _ => none

/-- One conjunct that admits the index, if the expression carries one.
    `&&` is searched on both sides: `A && B` is true only when both are, so
    either conjunct restricts the rows. `||` is NOT searched — one false
    disjunct excludes nothing — and neither is `!`. -/
def needleIn? (v : VarName) : Expr → Option (String × Bool)
  | .and left right =>
      match needleIn? v left with
      | some found => some found
      | none => needleIn? v right
  | .contains e (.lit k) | .strStarts e (.lit k) | .strEnds e (.lit k) => do
      let applied ← objectShape? v e
      let needle ← plainNeedle? k
      if gramsOfNeedle needle |>.isEmpty then none else some (needle, applied)
  | _ => none

/-- `?s <P> ?o` under one filter: the only pattern shape admitted. The
    variable the filter must read is the OBJECT variable, so a filter on the
    subject gives `none`. -/
def filteredSinglePattern? : QueryPattern → Option (WfIri × VarName × Expr)
  | .filter cond (.bgp [triple]) =>
      match triple.p, triple.o with
      | .iri predicate, .var v => some (predicate, v, cond)
      | _, _ => none
  | _ => none

/-- One optional `GRAPH` layer is stripped. Its name may be an IRI or a
    variable: an IBK4 block holds one predicate across every graph, and the
    body is a non-empty BGP, so a row the filter rejects cannot produce a
    solution under either form. `GRAPH` with an empty body is a different
    question and is not reachable here. -/
def strippedPattern? : QueryPattern → Option (WfIri × VarName × Expr)
  | .graph _ inner => filteredSinglePattern? inner
  | pattern => filteredSinglePattern? pattern

/-- The literal-search plan of one query, or `none` to scan.

    Two whole-query guards beyond the pattern shape. A `FROM` / `FROM NAMED`
    clause rebuilds the default graph (section 13.2), which this restriction
    does not model. And an `EXISTS` in the projection, a GROUP BY key, a
    HAVING condition or an ORDER BY condition is evaluated against the active
    graph (section 18.6), so it reads rows this plan would have dropped. -/
def plan? (query : Query) : Option Plan :=
  if !query.dataset.isEmpty || !query.expressionsOutsidePatternExistsFree then none
  else do
    let (predicate, v, cond) ← strippedPattern? query.pattern
    let (needle, keepNonLiterals) ← needleIn? v cond
    some { predicate, needle, keepNonLiterals }

/-! ## Executable pins

The rejections are what keep the answer the scan's answer, so each one is
pinned here beside the shape it refuses. -/

private def parse (text : String) : Option Query :=
  match parseSparql text with
  | .ok query => some query
  | .error _ => none

private def planned (text : String) : Option Plan :=
  (parse text).bind plan?

private def prefLabel : String := "<http://www.w3.org/2004/02/skos/core#prefLabel>"

#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(LCASE(STR(?o)), \"water\")) }").map
  Plan.needle == some "water"
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(LCASE(STR(?o)), \"water\")) }").map
  Plan.keepNonLiterals == some true
-- No STR: a non-literal object is a type error, so those rows are dropped.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(?o, \"water\")) }").map
  Plan.keepNonLiterals == some false
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(LCASE(?o), \"Water\")) }").map
  Plan.needle == some "Water"
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(STRSTARTS(STR(?o), \"water\")) }").map
  Plan.needle == some "water"
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(STRENDS(STR(?o), \"water\")) }").map
  Plan.needle == some "water"
-- A conjunct of `&&` is enough.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(isLiteral(?o) && CONTAINS(STR(?o), \"water\")) }").map
  Plan.needle == some "water"
-- One GRAPH layer is stripped, named or variable.
#guard (planned s!"SELECT ?s ?o WHERE \{ GRAPH <https://example.test/g> \{ ?s {prefLabel} ?o FILTER(CONTAINS(STR(?o), \"water\")) } }").map
  Plan.needle == some "water"
#guard (planned s!"SELECT ?g ?s WHERE \{ GRAPH ?g \{ ?s {prefLabel} ?o FILTER(CONTAINS(STR(?o), \"water\")) } }").map
  Plan.needle == some "water"

-- Every refusal below falls back to the scan.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(STR(?o), \"ab\")) }").isNone
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(STR(?o), ?needle)) }").isNone
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(REGEX(STR(?o), \"water\")) }").isNone
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(UCASE(STR(?o)), \"WATER\")) }").isNone
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(!CONTAINS(STR(?o), \"water\")) }").isNone
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(STR(?o), \"water\") || isIRI(?o)) }").isNone
-- A filter on a variable the pattern does not bind in object position.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(STR(?s), \"water\")) }").isNone
-- A second triple pattern: the restriction would have to reason about a join.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o . ?s <https://example.test/q> ?z FILTER(CONTAINS(STR(?o), \"water\")) }").isNone
-- No filter at all.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o }").isNone
-- A variable predicate: the plan names no block.
#guard (planned "SELECT ?s ?o WHERE { ?s ?p ?o FILTER(CONTAINS(STR(?o), \"water\")) }").isNone
-- A tagged needle is not a plain string.
#guard (planned s!"SELECT ?s ?o WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(STR(?o), \"water\"@en)) }").isNone
-- FROM rebuilds the default graph; the EXISTS guard is section 18.6's.
#guard (planned s!"SELECT ?s ?o FROM <https://example.test/g> WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(STR(?o), \"water\")) }").isNone
#guard (planned s!"SELECT ?s (EXISTS \{ ?s ?q ?r } AS ?e) WHERE \{ ?s {prefLabel} ?o FILTER(CONTAINS(STR(?o), \"water\")) }").isNone

end L4Factoidal.Storage.LiteralIndexPlan
