/-
L4Factoidal.SPARQL.PlanStreamable — the parse-stream fast-path
recogniser.

Port of `formal/fstar/SPARQL.Plan.Streamable.fst` (301 lines).

## What it is for, in the F\* module's measured words

`factoidal --data gene.ttl` (888,949 triples) answering a one-row
`COUNT(*)` peaked at 731 MiB RSS — the cost of materialising the whole
graph for a point lookup — because the CLI parses every `--data` file
into a term graph BEFORE it looks at the query. The streaming `count`
subcommand answers the same corpus in 44 MiB. This module is the pure
decision that lets a QUERY take that path, when and only when the query
provably does not need the materialised graph.

It is a sibling of the store-level streaming detectors, but it runs
EARLIER: those run after a backend exists and save the second
materialisation; this runs before any backend exists and saves the
first.

## The four shapes it recognises

1. `SELECT (COUNT(*) AS ?v) WHERE { ?s ?p ?o }`
2. `SELECT (COUNT(*) AS ?v) WHERE { GRAPH ?g { ?s ?p ?o } }` — `?g`
   neither projected nor grouped, so one total row over all named
   graphs
3. `ASK { ?s ?p ?o }`
4. either of 1 and 3 with any position bound to a constant

`none` is the fall-through signal: everything else — GROUP BY, HAVING,
FILTER, a multi-pattern BGP, DISTINCT, ORDER BY, VALUES — goes to the
materialise path unchanged.

## Two soundness conditions, carried across verbatim in force

**The domain split.** A plain `?s ?p ?o` queries only the DEFAULT
graph; `GRAPH ?g { ?s ?p ?o }` queries only the UNION OF NAMED graphs.
In N-Quads a line without a graph label is a default-graph triple and a
line with one is a named-graph quad, so the two shapes count DISJOINT
subsets of the document and neither counts every line. `streamInDomain`
is what keeps that honest in the fold.

**Pairwise distinctness on shape 2.** If the graph variable also names
one of the triple positions (`GRAPH ?g { ?g ?p ?o }`), or two positions
are the same variable (`GRAPH ?g { ?s ?p ?s }`), the pattern carries an
implicit equality that a position-by-position bound match does not
honour, and the streamed count would silently OVER-count. Rejecting
those shapes is required for soundness, not style. A `#guard` below
pins each rejection.
-/
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## The decision output -/

/-- Which part of the dataset a plan ranges over. Triple-only input
    formats have only a default graph, so `defaultGraph` is the only
    domain that ever applies there. -/
inductive StreamDomain where
  | defaultGraph
  | anyNamedGraph
  deriving DecidableEq, Repr, Inhabited

/-- What the query wants back. -/
inductive StreamGoal where
  | count (v : VarName)
  | ask
  deriving DecidableEq, Repr, Inhabited

/-- The constants a triple pattern pins, position by position. The F\*
    module reuses `triple_pattern_bound` from the algebra; the Lean
    algebra has no such record, so it is stated here with the same
    three fields. -/
structure StreamBound where
  s : Option Subject := none
  p : Option WfIri := none
  o : Option Term := none
  deriving Repr, Inhabited

structure StreamPlan where
  domain : StreamDomain
  bound  : StreamBound
  goal   : StreamGoal
  offset : Option Nat
  limit  : Option Nat
  deriving Repr, Inhabited

/-! ## Shape detectors -/

/-- The single triple pattern of a one-pattern BGP. -/
def extractSingleTpBgp : QueryPattern → Option TriplePattern
  | .bgp [tp] => some tp
  | _ => none

/-- `(COUNT(*) AS ?v)` or `(COUNT(true) AS ?v)`, exactly one projected
    item, not DISTINCT. -/
def detectCountStarSelect (sel : SelectClause) : Option VarName :=
  match sel with
  | .vars [.expr e v] =>
      match e with
      | .aggregate .count distinct subE =>
          if distinct then none
          else match subE with
               | .var "*" => some v
               | .boolLit true => some v
               | _ => none
      | _ => none
  | _ => none

def patternBoundOfTp (tp : TriplePattern) : StreamBound :=
  { s := match tp.s with
         | .iri i => some (.iri i)
         | .bnode b => some (.bnode b)
         | _ => none
  , p := match tp.p with
         | .iri i => some i
         | _ => none
  , o := match tp.o with
         | .iri i => some (.iri i)
         | .bnode b => some (.bnode b)
         | .literal l => some (.literal l)
         | _ => none }

/-- Modifiers that rule out ANY streaming path whatever the shape.
    GROUP BY, HAVING and VALUES need row materialisation to evaluate;
    DISTINCT and REDUCED need it to deduplicate. ORDER BY is a
    semantic no-op on a single-row answer but is rejected too, matching
    the store-level detector's own conservative call. -/
def commonModifiersOk (q : Query) : Bool :=
  match q with
  | .mk _ _ _ groupBy having modifier postValues _ =>
      groupBy.isNone && having.isEmpty && postValues.isNone &&
      !modifier.distinct && !modifier.reduced && modifier.orderBy.isNone

/-- Shapes 1 and 4: `SELECT (COUNT(*) AS ?v) WHERE { tp }`. -/
def detectCountDefault (q : Query) : Option StreamPlan :=
  match q with
  | .mk (.select sel) _ pattern _ _ modifier _ _ =>
      match detectCountStarSelect sel with
      | none => none
      | some alias =>
          if !commonModifiersOk q then none
          else match extractSingleTpBgp pattern with
               | none => none
               | some tp =>
                   some { domain := .defaultGraph, bound := patternBoundOfTp tp,
                          goal := .count alias, offset := modifier.offset,
                          limit := modifier.limit }
  | _ => none

/-- Shape 2. Requires the four variables pairwise distinct — see the
    module header. -/
def detectCountAnyNamedGraph (q : Query) : Option StreamPlan :=
  match q with
  | .mk (.select sel) _ pattern _ _ modifier _ _ =>
      match detectCountStarSelect sel with
      | none => none
      | some alias =>
          if !commonModifiersOk q then none
          else match pattern with
               | .graph (.var gv) inner =>
                   match extractSingleTpBgp inner with
                   | none => none
                   | some tp =>
                       match tp.s, tp.p, tp.o with
                       | .var sv, .var pv, .var ov =>
                           if sv == gv || pv == gv || ov == gv then none
                           else if sv == pv || sv == ov || pv == ov then none
                           else some { domain := .anyNamedGraph, bound := {},
                                       goal := .count alias,
                                       offset := modifier.offset,
                                       limit := modifier.limit }
                       | _, _, _ => none
               | _ => none
  | _ => none

/-- Shapes 3 and 4: `ASK { tp }`. A bound position is as streamable as
    an unbound one — "does at least one X exist" is the same fold. -/
def detectAskDefault (q : Query) : Option StreamPlan :=
  match q with
  | .mk .ask _ pattern _ _ _ postValues _ =>
      if postValues.isSome then none
      else match extractSingleTpBgp pattern with
           | none => none
           | some tp =>
               some { domain := .defaultGraph, bound := patternBoundOfTp tp,
                      goal := .ask, offset := none, limit := none }
  | _ => none

/-- At most one detector can match: they dispatch on disjoint
    `(form, pattern)` shapes, so the order carries no meaning. -/
def streamableShape (q : Query) : Option StreamPlan :=
  match detectCountDefault q with
  | some p => some p
  | none =>
      match detectCountAnyNamedGraph q with
      | some p => some p
      | none => detectAskDefault q

/-! ## The per-triple fold, generic over source format

The parsers' document walks take a step function and a stop predicate
and know nothing about SPARQL. This module supplies the step, not the
walk. -/

structure StreamState where
  count : Nat := 0
  found : Bool := false
  deriving Repr, Inhabited

def streamInit : StreamState := {}

def tripleMatchesStreamBound (b : StreamBound) (t : Triple) : Bool :=
  (match b.s with | none => true | some s => s == t.s) &&
  (match b.p with | none => true | some p => p == t.p) &&
  (match b.o with | none => true | some o => o == t.o)

/-- Whether a parsed item — a triple plus its optional N-Quads graph
    label — falls in the plan's domain. Triple-only sources always pass
    `none` and only ever run `defaultGraph` plans. -/
def streamInDomain (plan : StreamPlan) (g : Option Iri) : Bool :=
  match plan.domain, g with
  | .defaultGraph, none => true
  | .anyNamedGraph, some _ => true
  | _, _ => false

/-- Called only on items already known in-domain. -/
def streamStep (plan : StreamPlan) (t : Triple) (st : StreamState) : StreamState :=
  if tripleMatchesStreamBound plan.bound t then
    match plan.goal with
    | .count _ => { st with count := st.count + 1 }
    | .ask => { st with found := true }
  else st

/-- Once an ASK plan has found a match, no further input can change the
    answer. A COUNT never stops early. -/
def streamStop (plan : StreamPlan) (st : StreamState) : Bool :=
  match plan.goal with
  | .ask => st.found
  | .count _ => false

def streamCountResult (st : StreamState) : Nat := st.count
def streamAskResult (st : StreamState) : Bool := st.found

/-! ## Build-time checks

Each shape is checked as a MINIMAL PAIR: the query that streams, and
the nearest query that must not. -/

section Checks

private def q (text : String) : Option Query :=
  match parseSparql text none .v11 with
  | .ok x => some x
  | .error _ => none

private def shapeOf (text : String) : Option StreamPlan :=
  (q text).bind streamableShape

/-! ### Shape 1: COUNT(*) over the default graph -/

#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }").isSome
#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }").map (·.domain)
       == some .defaultGraph

/-! A second triple pattern is not this shape. -/

#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o . ?o ?q ?r }").isNone

/-! DISTINCT, GROUP BY, ORDER BY and a FILTER each fall through. -/

#guard (shapeOf "SELECT DISTINCT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }").isNone
#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o } GROUP BY ?s").isNone
#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o } ORDER BY ?c").isNone
#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o FILTER(true) }").isNone
#guard (shapeOf "SELECT (COUNT(DISTINCT *) AS ?c) WHERE { ?s ?p ?o }").isNone

/-! An ordinary SELECT is not a COUNT shape. -/

#guard (shapeOf "SELECT ?s WHERE { ?s ?p ?o }").isNone

/-! ### Shape 4: a bound position streams, and the bound is recorded -/

#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { ?s <http://e/p> ?o }").isSome
#guard ((shapeOf "SELECT (COUNT(*) AS ?c) WHERE { ?s <http://e/p> ?o }").map
         (fun pl => pl.bound.p.isSome && pl.bound.s.isNone)) == some true

/-! ### Shape 2, and the two soundness rejections

`GRAPH ?g { ?s ?p ?o }` streams. Reusing `?g` in a triple position, or
repeating a variable across two positions, carries an implicit equality
a position-by-position match does not honour — so both must fall
through, or the count over-counts. -/

#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }").map
       (·.domain) == some .anyNamedGraph
#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?g ?p ?o } }").isNone
#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?g } }").isNone
#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?s } }").isNone
#guard (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?s ?o } }").isNone

/-! A bound position inside GRAPH is not shape 2 either — the shape
    requires three variables. -/

#guard (shapeOf
  "SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s <http://e/p> ?o } }").isNone

/-! ### Shape 3: ASK -/

#guard (shapeOf "ASK { ?s ?p ?o }").map (·.goal) == some .ask
#guard (shapeOf "ASK { ?s <http://e/p> ?o }").isSome
#guard (shapeOf "ASK { ?s ?p ?o . ?o ?q ?r }").isNone

/-! ### The domain split

A default-graph plan counts only unlabelled items; a named-graph plan
counts only labelled ones. Neither counts every line, which is the
whole point on N-Quads input. -/

private def dgPlan : StreamPlan :=
  (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }").getD
    { domain := .defaultGraph, bound := {}, goal := .ask,
      offset := none, limit := none }
private def ngPlan : StreamPlan :=
  (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }").getD
    { domain := .defaultGraph, bound := {}, goal := .ask,
      offset := none, limit := none }

#guard streamInDomain dgPlan none
#guard !streamInDomain dgPlan (some "http://e/g")
#guard !streamInDomain ngPlan none
#guard streamInDomain ngPlan (some "http://e/g")

/-! ### The fold -/

private def wi (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩
  else ⟨"http://example.org/not-an-iri", by simp [isIri, String.isEmpty]⟩
private def t1 : Triple := ⟨.iri (wi "http://e/a"), wi "http://e/p",
                            .iri (wi "http://e/b")⟩
private def t2 : Triple := ⟨.iri (wi "http://e/a"), wi "http://e/q",
                            .iri (wi "http://e/b")⟩

#guard streamCountResult ([t1, t2, t1].foldl (fun st t => streamStep dgPlan t st)
         streamInit) == 3

private def pPlan : StreamPlan :=
  (shapeOf "SELECT (COUNT(*) AS ?c) WHERE { ?s <http://e/p> ?o }").getD dgPlan

#guard streamCountResult ([t1, t2, t1].foldl (fun st t => streamStep pPlan t st)
         streamInit) == 2

/-! An ASK stops as soon as it finds one; a COUNT never stops. -/

private def askPlan : StreamPlan :=
  (shapeOf "ASK { ?s <http://e/p> ?o }").getD dgPlan

#guard !streamStop askPlan streamInit
#guard streamStop askPlan (streamStep askPlan t1 streamInit)
#guard !streamStop askPlan (streamStep askPlan t2 streamInit)
#guard !streamStop dgPlan (streamStep dgPlan t1 streamInit)
#guard streamAskResult (streamStep askPlan t1 streamInit)

end Checks

end L4Factoidal.SPARQL
