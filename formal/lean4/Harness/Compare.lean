/-
Harness.Compare — PURE comparison of a SPARQL query's actual result
with the expected one, reproducing `bin/w3c-runner/w3c_runner.ml`'s
`run_query_eval_test` rules clause for clause:

  * SELECT: the two solution sequences compare as MULTISETS under a
    blank-node BIJECTION (the F* `solutions_isomorphic_outcome`).
    When the query has ORDER BY the bijection is pinned to row
    position (`select_results_equal_strict ~ordered:true`). Rows
    without any blank node go through the plain multiset match
    (`results_match_with`), exactly like the F* runner — which also
    means row ORDER is not checked for blank-node-free rows, because
    an ORDER BY with ties admits several correct orders and the
    expected file records only one of them.
  * Term comparison is the engine equality `Term.eqb` (language-tag
    case, XMLLiteral c14n) — no numeric leniency.
  * `.csv` expected files are lossy (every value is written as a plain
    string, blank-node labels are not stable), so the CSV comparison
    collapses all blank nodes to one token and compares a plain-string
    expected literal by lexical form only (`term_equal_csv_lenient`).
  * a search that runs out of budget is `budgetExceeded` — reported,
    never read as a pass (#316 in the F* tree).
  * an `rs:ResultSet` Turtle file decodes to rows through
    `rs:solution` / `rs:binding` / `rs:variable` / `rs:value`, with
    `rs:index` ordering the rows when every solution carries one.

Everything here is total and `#guard`-checkable; `Harness/HarnessTests.lean`
pins the behaviour. No `sorry`, no `axiom`, no `native_decide`, no
`partial`.
-/
import L4Factoidal.SPARQL.Results
import Harness.Manifest

open L4Factoidal.RDF
open L4Factoidal.SPARQL

namespace Harness

/-! ## Blank-node bijection -/

/-- expected label ↦ actual label. -/
abbrev BMap := List (String × String)

/-- Extend the bijection with `e ↦ a`, refusing a conflict in either
direction. -/
def bmapExtend (m : BMap) (e a : String) : Option BMap :=
  match m.find? (fun p => p.1 == e) with
  | some p => if p.2 == a then some m else none
  | none   => if m.any (fun p => p.2 == a) then none else some ((e, a) :: m)

/-- A term comparator threading the bijection. -/
abbrev TermCmp := BMap → Term → Term → Option BMap

/-- Strict: blank nodes through the bijection, everything else by
`Term.eqb`; RDF 1.2 triple terms position by position. -/
def termMatchStrict (m : BMap) : Term → Term → Option BMap
  | .bnode e, .bnode a => bmapExtend m e a
  | .tripleTerm s1 p1 o1, .tripleTerm s2 p2 o2 =>
      let ms : Option BMap := match s1, s2 with
        | .bnode e, .bnode a => bmapExtend m e a
        | .iri i1,  .iri i2  => if i1 == i2 then some m else none
        | _,        _        => none
      match ms with
      | none    => none
      | some m1 => if p1 == p2 then termMatchStrict m1 o1 o2 else none
  | t1, t2 => if t1.eqb t2 then some m else none

/-- CSV-lenient (`term_equal_csv_lenient`): any blank node matches any
blank node; an expected plain `xsd:string` literal matches any literal
with the same lexical form (CSV dropped the datatype). -/
def termMatchCsv (m : BMap) : Term → Term → Option BMap
  | .bnode _, .bnode _ => some m
  | .literal e, .literal a =>
      if e.val.datatype == xsdString && e.val.langTag.isNone then
        (if e.val.lexicalForm == a.val.lexicalForm then some m else none)
      else if (Term.literal e).eqb (.literal a) then some m else none
  | t1, t2 => if t1.eqb t2 then some m else none

/-! ## Rows -/

/-- Both rows bind exactly the same variables. -/
def domainsEqual (e a : Binding) : Bool :=
  e.all (fun b => (a.lookup b.1).isSome) && a.all (fun b => (e.lookup b.1).isSome)

/-- One expected row against one actual row under the current
bijection; the extended bijection on success. -/
def rowMatch (cmp : TermCmp) (m : BMap) (e a : Binding) : Option BMap :=
  if !domainsEqual e a then none
  else e.foldl (fun acc b =>
    match acc with
    | none    => none
    | some m1 =>
        match a.lookup b.1 with
        | none   => none
        | some t => cmp m1 b.2 t) (some m)

/-- Position-pinned comparison (ORDER BY present). -/
def matchOrdered (cmp : TermCmp) : BMap → List Binding → List Binding → Option BMap
  | m, [],      []      => some m
  | m, e :: es, a :: as =>
      match rowMatch cmp m e a with
      | some m1 => matchOrdered cmp m1 es as
      | none    => none
  | _, _, _ => none

/-- Remove the first element satisfying `p`; `none` when there is none. -/
def removeFirst (p : Binding → Bool) : List Binding → Option (List Binding)
  | []        => none
  | a :: rest => if p a then some rest else (removeFirst p rest).map (a :: ·)

/-- Multiset match with no cross-row state (`results_match_with`):
every expected row consumes the first actual row it matches. Correct
whenever the comparator does not depend on the bijection — i.e. for
blank-node-free rows and for the CSV-lenient comparator. -/
def matchGreedy (cmp : TermCmp) : List Binding → List Binding → Bool
  | [],      []     => true
  | [],      _ :: _ => false
  | e :: es, actual =>
      match removeFirst (fun a => (rowMatch cmp [] e a).isSome) actual with
      | some rest => matchGreedy cmp es rest
      | none      => false

/-- Outcome of a budgeted search. -/
inductive MatchRes where
  | found (m : BMap)
  | notFound
  | exceeded
  deriving Repr

mutual

/-- Backtracking multiset match under ONE bijection across all rows
(the F* `solutions_isomorphic_outcome` for unordered results). `fuel`
bounds the recursion structurally; `budget` is the total-work budget,
threaded through and returned, so an exhaustive failure cannot run
for ever — it reports `exceeded`. -/
def matchBack (cmp : TermCmp) : Nat → Nat → BMap → List Binding → List Binding → MatchRes × Nat
  | 0,        _,          _, _,       _      => (.exceeded, 0)
  | _,        0,          _, _,       _      => (.exceeded, 0)
  | _,        budget + 1, m, [],      []     => (.found m, budget)
  | _,        budget + 1, _, [],      _ :: _ => (.notFound, budget)
  | fuel + 1, budget + 1, m, e :: es, actual => tryCands cmp fuel budget m e es [] actual

/-- Try each remaining actual row as the partner of `e`; `seen` holds
the rows already skipped (kept for the recursive call). -/
def tryCands (cmp : TermCmp) : Nat → Nat → BMap → Binding → List Binding → List Binding →
    List Binding → MatchRes × Nat
  | 0,        _,          _, _, _,  _,    _         => (.exceeded, 0)
  | _,        0,          _, _, _,  _,    _         => (.exceeded, 0)
  | _,        budget + 1, _, _, _,  _,    []        => (.notFound, budget)
  | fuel + 1, budget + 1, m, e, es, seen, a :: rest =>
      match rowMatch cmp m e a with
      | some m1 =>
          match matchBack cmp fuel budget m1 es (seen.reverse ++ rest) with
          | (.found m2, b) => (.found m2, b)
          | (.exceeded, b) => (.exceeded, b)
          | (.notFound, b) => tryCands cmp fuel b m e es (a :: seen) rest
      | none => tryCands cmp fuel budget m e es (a :: seen) rest

end

/-- Does any term of any row contain a blank node? -/
def termHasBnode : Term → Bool
  | .bnode _          => true
  | .tripleTerm s _ o => (match s with | .bnode _ => true | _ => false) || termHasBnode o
  | _                 => false

def rowsHaveBnode (rows : List Binding) : Bool :=
  rows.any (fun mu => mu.any (fun b => termHasBnode b.2))

/-- Three-way outcome, the shape of `IsoOutcome`: a give-up is its
own answer, never a pass. -/
inductive CmpOutcome where
  | equal
  | notEqual
  | budgetExceeded
  deriving DecidableEq, Repr

/-- Total-work budget for the bijection search. W3C evaluation tests
with blank nodes in their results have a handful of rows; this is far
above them and far below "hangs the run". -/
def compareBudget : Nat := 200000

/-- THE SELECT comparison (port of the `.srx/.srj/.tsv/.csv` branch of
`run_query_eval_test`). `ordered` = the query has ORDER BY; `csv` =
the expected file was `.csv`. -/
def compareSelectRows (ordered csv : Bool) (expected actual : List Binding) : CmpOutcome :=
  if csv then
    (if matchGreedy termMatchCsv expected actual then .equal else .notEqual)
  else if rowsHaveBnode expected || rowsHaveBnode actual then
    if ordered then
      (match matchOrdered termMatchStrict [] expected actual with
       | some _ => .equal
       | none   => .notEqual)
    else
      match (matchBack termMatchStrict compareBudget compareBudget [] expected actual).1 with
      | .found _  => .equal
      | .notFound => .notEqual
      | .exceeded => .budgetExceeded
  else
    (if matchGreedy termMatchStrict expected actual then .equal else .notEqual)

/-! ## `rs:ResultSet` — SELECT results written as Turtle

Some sparql11 tests (`aggregates/agg-empty-group-count-graph`,
`bindings/graph`) ship their expected rows in the DAWG result-set
vocabulary. Port of the decoder inside `run_query_eval_test`. -/

def rsNs : String := "http://www.w3.org/2001/sw/DataAccess/tests/result-set#"

/-- The subject typed `rs:ResultSet`, if the graph has one. -/
def rsResultSetSubject (g : Graph) : Option Subject :=
  (g.find? (fun t =>
    t.p.val == rdfType &&
    (match t.o with
     | .iri i => i.val == rsNs ++ "ResultSet"
     | _      => false))).map (·.s)

def isRsResultSet (g : Graph) : Bool := (rsResultSetSubject g).isSome

/-- The lexical form of a literal object, if the term is one. -/
def literalLex : Term → Option String
  | .literal l => some l.val.lexicalForm
  | _          => none

/-- One `rs:solution` node → (its `rs:index`, its row). -/
def rsDecodeSolution (g : Graph) (sol : Subject) : Option Nat × Binding :=
  let idx : Option Nat :=
    (findObject? g sol (rsNs ++ "index")).bind literalLex |>.bind String.toNat?
  let row : Binding :=
    (findObjects g sol (rsNs ++ "binding")).filterMap (fun bnd =>
      match subjectOfTerm bnd with
      | none   => none
      | some b =>
          match (findObject? g b (rsNs ++ "variable")).bind literalLex,
                findObject? g b (rsNs ++ "value") with
          | some v, some t => some (v, t)
          | _,      _      => none)
  (idx, row)

/-- Stable insertion sort on the index. -/
def insertByIndex (x : Nat × Binding) : List (Nat × Binding) → List (Nat × Binding)
  | []        => [x]
  | y :: rest => if x.1 < y.1 then x :: y :: rest else y :: insertByIndex x rest

def sortByIndex (rows : List (Nat × Binding)) : List (Nat × Binding) :=
  rows.foldl (fun acc r => insertByIndex r acc) []

/-- Decode the result set: (`rs:resultVariable`s, rows). Rows come in
`rs:index` order when every solution carries an index, else in graph
order. -/
def decodeRsResultSet (g : Graph) : Option (List VarName × List Binding) :=
  match rsResultSetSubject g with
  | none    => none
  | some rs =>
      let vars := (findObjects g rs (rsNs ++ "resultVariable")).filterMap literalLex
      let sols := (findObjects g rs (rsNs ++ "solution")).filterMap subjectOfTerm
      let decoded := sols.map (rsDecodeSolution g)
      let indexed := decoded.filterMap (fun r => r.1.map (fun i => (i, r.2)))
      let rows :=
        if !decoded.isEmpty && indexed.length == decoded.length then
          (sortByIndex indexed).map Prod.snd
        else decoded.map Prod.snd
      some (vars, rows)

/-- Render a row for a FAIL line. -/
def termShow : Term → String
  | .iri i     => "<" ++ i.val ++ ">"
  | .bnode b   => "_:" ++ b
  | .literal l =>
      "\"" ++ l.val.lexicalForm ++ "\"" ++
      (match l.val.langTag with | some t => "@" ++ t | none => "") ++
      (if l.val.langTag.isNone && l.val.datatype != xsdString then "^^<" ++ l.val.datatype.val ++ ">" else "")
  | .tripleTerm _ _ _ => "<<( … )>>"

def rowShow (mu : Binding) : String :=
  String.intercalate ", " (mu.map (fun b => "?" ++ b.1 ++ "=" ++ termShow b.2))

/-- The expected rows that no actual row matches one-to-one (the
F* runner's `UNMATCHED` list), for the FAIL line. -/
def unmatchedRows (cmp : TermCmp) : List Binding → List Binding → List Binding
  | [],      _      => []
  | e :: es, actual =>
      match removeFirst (fun a => (rowMatch cmp [] e a).isSome) actual with
      | some rest => unmatchedRows cmp es rest
      | none      => e :: unmatchedRows cmp es actual

end Harness
