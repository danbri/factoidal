/-
L4Factoidal.Testing.Props — the INVARIANTS the property probe checks
on every generated case, as pure functions `Case → Option String`
(`none` = holds; `some msg` = the violation, with enough detail to
reproduce it from the seed alone).

Each invariant names the statement it instantiates. Where a theorem
in the tree already proves the law (`evalBgp_mono`,
`distinctSolutions_idem`, `sortSolutions_perm`, …) the probe is not a
second proof — it is a check that the EXECUTED code and the proved
statement are the same thing on concrete inputs (a theorem about
`sortSolutions` says nothing if the evaluator calls something else),
and it reaches the laws nobody has proved yet (join commutativity,
the parse∘serialise round trips, RDFC relabelling invariance).

Pure and total; `L4Factoidal/Testing/GenTests.lean` pins a few of
them on fixed seeds. No `sorry`, no `axiom`, no `native_decide`, no
`partial`.
-/
import L4Factoidal.Testing.Gen
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.ResultsXml
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.SPARQL.ResultsCsvTsv
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.RDF.Canonical

namespace L4Factoidal.Testing

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Syntax

/-! ## Multiset helpers -/

def removeFirstBy (p : α → Bool) : List α → Option (List α)
  | []        => none
  | a :: rest => if p a then some rest else (removeFirstBy p rest).map (a :: ·)

/-- Multiset equality under an equivalence `eq`. -/
def multisetEqBy (eq : α → α → Bool) : List α → List α → Bool
  | [],      []     => true
  | [],      _ :: _ => false
  | x :: xs, ys     =>
      match removeFirstBy (eq x) ys with
      | some ys' => multisetEqBy eq xs ys'
      | none     => false

/-- Every element of `xs` occurs in `ys` (as a set). -/
def subsetBy (eq : α → α → Bool) (xs ys : List α) : Bool :=
  xs.all (fun x => ys.any (eq x))

/-! ## Rendering for failure messages -/

def termText (t : Term) : String :=
  match Term.toNTriples .rdf11 t with
  | .ok s    => s
  | .error e => "<<error: " ++ e ++ ">>"

def rowText (mu : Binding) : String :=
  "[" ++ String.intercalate ", " (mu.map (fun (v, t) => "?" ++ v ++ "=" ++ termText t)) ++ "]"

def rowsText (rows : List Binding) : String :=
  String.intercalate " " (rows.map rowText)

/-! ## The evaluated pieces of a case -/

/-- The environment the probe evaluates under: a fixed NOW, no
services, no extension functions. -/
def probeEnv : EvalEnv := { now := some "2026-08-22T00:00:00Z" }

def Case.omegaA (c : Case) : SolutionSeq := evalBgp (toBgp c.bgpA) c.graph
def Case.omegaB (c : Case) : SolutionSeq := evalBgp (toBgp c.bgpB) c.graph

def Case.cond (c : Case) (mu : Binding) : Bool :=
  ebvOrFalse (Expr.evalIn probeEnv mu c.expr.toExpr)

def Case.dataset (c : Case) : Dataset := { default := c.graph, named := [] }

/-! ## Invariants

Each returns `none` when it holds. -/

/-- `evalBgp_mono` (SPARQL/Invariants.lean) instance: adding a triple
never loses a BGP answer. -/
def propBgpMono (c : Case) : Option String :=
  let before := c.omegaA
  let after  := evalBgp (toBgp c.bgpA) (c.graph.add c.extra)
  if subsetBy (· == ·) before after then none
  else some s!"lost rows after adding {termText c.extra.s.toTerm} <{c.extra.p.val}> {termText c.extra.o}: before {rowsText before}; after {rowsText after}"

/-- Join(Ω1, Ω2) = Join(Ω2, Ω1) as multisets of observationally-equal
rows (§18.5 defines Join as a set comprehension symmetric in its
arguments; the merged rows may list their pairs in a different
order, hence `Binding.equiv`). -/
def propJoinComm (c : Case) : Option String :=
  let ab := join c.omegaA c.omegaB
  let ba := join c.omegaB c.omegaA
  if multisetEqBy Binding.equiv ab ba then none
  else some s!"Join(A,B) = {rowsText ab} but Join(B,A) = {rowsText ba}"

/-- Union(Ω1, Ω2) is the concatenation, and commutative as a multiset. -/
def propUnionAppend (c : Case) : Option String :=
  let u := union c.omegaA c.omegaB
  if u != c.omegaA ++ c.omegaB then some s!"Union is not append: {rowsText u}"
  else if !multisetEqBy (· == ·) u (union c.omegaB c.omegaA) then
    some s!"Union not commutative as a multiset: {rowsText u}"
  else none

/-- Minus(Ω1, Ω2) ⊆ Ω1 (`mem_of_mem_minus`). -/
def propMinusSubset (c : Case) : Option String :=
  let m := minus c.omegaA c.omegaB
  if subsetBy (· == ·) m c.omegaA then none
  else some s!"Minus produced a row not in its left input: {rowsText m} vs {rowsText c.omegaA}"

/-- Filter(expr, Ω) ⊆ Ω (`filterSeq_sound`). -/
def propFilterSubset (c : Case) : Option String :=
  let f := filterSeq c.cond c.omegaA
  if subsetBy (· == ·) f c.omegaA then none
  else some s!"Filter produced a row not in its input: {rowsText f}"

/-- Distinct is idempotent (`distinctSolutions_idem`). -/
def propDistinctIdem (c : Case) : Option String :=
  let d := distinctSolutions (c.omegaA ++ c.omegaB)
  if distinctSolutions d == d then none
  else some s!"Distinct not idempotent on {rowsText (c.omegaA ++ c.omegaB)}"

/-- ORDER BY is a permutation (`sortSolutions_perm`), checked on the
comparator the evaluator really uses (`compareOnConditions`). -/
def propOrderByPerm (c : Case) : Option String :=
  let conds : List OrderCondition := [.asc (.var "x"), .desc (.var "y"), .asc (.var "z")]
  let input := c.omegaA ++ c.omegaB
  let sorted := sortSolutions (compareOnConditions probeEnv probeEnv.activeGraph conds) input
  if multisetEqBy (· == ·) sorted input then none
  else some s!"ORDER BY is not a permutation: input {rowsText input}; output {rowsText sorted}"

/-- Graph → N-Triples → Graph is the identity as a set of triples. -/
def propNTriplesRoundTrip (c : Case) : Option String :=
  match parseNTriples c.graphText .rdf11 with
  | .error e => some s!"N-Triples re-parse failed: {e.msg} (offset {e.pos})"
  | .ok g    =>
      if Graph.setEqB g c.graph && g.length == c.graph.length then none
      else some s!"N-Triples round trip changed the graph: got {g.length} triples, had {c.graph.length}"

/-- The same N-Triples text read by the Turtle parser (N-Triples is a
Turtle subset — RDF 1.1 N-Triples §1). -/
def propTurtleRoundTrip (c : Case) : Option String :=
  match parseTurtle c.graphText none .rdf11 with
  | .error e => some s!"Turtle re-parse failed: {e.msg} (offset {e.pos})"
  | .ok g    =>
      if Graph.setEqB g c.graph && g.length == c.graph.length then none
      else some s!"Turtle round trip changed the graph: got {g.length} triples, had {c.graph.length}"

/-- The SELECT-shaped result the results-format round trips use:
the BGP rows with their variable header. -/
def Case.result (c : Case) : QueryResult :=
  .bindings (collectVarsInOrder c.omegaA) c.omegaA

/-- Rows equal position by position, up to binding-pair order. -/
def rowsEquivOrdered : List Binding → List Binding → Bool
  | [],      []      => true
  | a :: as, b :: bs => a.equiv b && rowsEquivOrdered as bs
  | _,       _       => false

def roundTripBindings (label : String) (c : Case)
    (parsed : Except ResultsError QueryResult) : Option String :=
  match parsed, c.result with
  | .error e, _ => some s!"{label} re-parse failed: {e}"
  | .ok (.bindings vs rows), .bindings vs0 rows0 =>
      if vs != vs0 then some s!"{label} changed the variable list: {vs0} → {vs}"
      else if rowsEquivOrdered rows rows0 then none
      else some s!"{label} changed the rows: had {rowsText rows0}; got {rowsText rows}"
  | .ok (.boolean _), _ => some s!"{label} re-parsed a SELECT result as a boolean"
  | _, .boolean _ => some s!"{label}: internal — case result is boolean"

def propSrxRoundTrip (c : Case) : Option String :=
  roundTripBindings "SRX" c (parseSrx c.result.toSrx)

def propSrjRoundTrip (c : Case) : Option String :=
  roundTripBindings "SRJ" c (parseSrj c.result.toSrj)

/-- CSV and TSV round trips are stated for a result with at least one
variable. A zero-column result (`SELECT *` over a pattern binding
nothing) serialises to an empty header line, which RFC 4180 (one field
per record, possibly empty) and the CSV/TSV format (§2: "the header
line lists the variable names") read differently: the Lean parser
rejects the empty header as "empty input". Spec-ambiguous; recorded
in the design note, not decided here. -/
def Case.hasVars (c : Case) : Bool :=
  match c.result with
  | .bindings vs _ => !vs.isEmpty
  | .boolean _     => false

def propTsvRoundTrip (c : Case) : Option String :=
  if !c.hasVars then none else
  match c.result.toTsv with
  | .error e => some s!"TSV serialise failed: {e}"
  | .ok text => roundTripBindings "TSV" c (parseTsv text)

/-- CSV is lossy by design (§2 of the CSV/TSV format: every value is a
string, blank-node labels unstable), so the round trip is checked
with the harness's CSV-lenient term rule. -/
def propCsvRoundTrip (c : Case) : Option String :=
  if !c.hasVars then none else
  match c.result.toCsv with
  | .error e => some s!"CSV serialise failed: {e}"
  | .ok text =>
    match parseCsv text, c.result with
    | .error e, _ => some s!"CSV re-parse failed: {e}"
    | .ok (.bindings vs rows), .bindings vs0 rows0 =>
        let cellOk (a b : Option Term) : Bool :=
          match a, b with
          | none, none => true
          -- The harness rule takes the CSV-file side as `expected`
          -- (plain strings) and the engine side as `actual`.
          | some x, some y => Term.eqbCsvLenient y x
          | _, _ => false
        let rowOk (r0 r : Binding) : Bool := vs0.all (fun v => cellOk (r0.lookup v) (r.lookup v))
        if vs != vs0 then some s!"CSV changed the variable list: {vs0} → {vs}"
        else if rows.length != rows0.length then
          some s!"CSV changed the row count: had {rows0.length}, got {rows.length}"
        else if (List.zipWith rowOk rows0 rows).all id then none
        else some s!"CSV changed the rows: had {rowsText rows0}; got {rowsText rows}"
    | .ok (.boolean _), _ => some "CSV re-parsed a SELECT result as a boolean"
    | _, .boolean _ => some "CSV: internal — case result is boolean"

/-- RDFC-1.0 canonical form is invariant under blank-node relabelling
(RDFC-1.0 §1: the output identifies the dataset up to blank-node
labels). -/
def propRdfcRelabel (c : Case) : Option String :=
  let ds := c.dataset
  let ds' := ds.renameBnodes (fun b => "z" ++ b)
  let a := ds.canonicalNQuads .sha256
  let b := ds'.canonicalNQuads .sha256
  if a == b then none
  else some s!"canonical N-Quads changed under relabelling:\n{a}--- vs ---\n{b}"

/-- Isomorphism is reflexive and invariant under relabelling. -/
def propIsoReflexive (c : Case) : Option String :=
  if Graph.isomorphic? c.graph c.graph then none
  else some "graph not isomorphic to itself"

def propIsoRelabel (c : Case) : Option String :=
  let g' := c.graph.renameBnodes (fun b => "q" ++ b)
  if Graph.isomorphic? c.graph g' then none
  else some "graph not isomorphic to its blank-node relabelling"

/-- The generated query text is accepted by the Lean SPARQL parser
(every generated string is grammatical SPARQL 1.1). -/
def propQueryParses (c : Case) : Option String :=
  match parseSparql c.queryText none with
  | .ok _    => none
  | .error e => some s!"Lean parser rejected generated query: {e.msg} (offset {e.pos})"

/-- The query evaluates, and a SELECT with DISTINCT yields no two
equivalent rows (`distinctSolutions_represents`). -/
def propDistinctNoDup (c : Case) : Option String :=
  match parseSparql c.queryText none with
  | .error _ => none   -- reported by `propQueryParses`
  | .ok q =>
    match q.form with
    | .select _ =>
        if !q.modifier.distinct then none
        else
          let rows := (evalSelect probeEnv c.dataset q).2
          let rec hasDup : List Binding → Bool
            | []        => false
            | r :: rest => rest.any (fun x => r.equiv x) || hasDup rest
          if hasDup rows then some s!"SELECT DISTINCT returned equivalent rows: {rowsText rows}"
          else none
    | _ => none

/-- The whole list, named. The probe runs every entry on every seed. -/
def allProps : List (String × (Case → Option String)) :=
  [ ("bgp_mono",            propBgpMono),
    ("join_comm",           propJoinComm),
    ("union_append",        propUnionAppend),
    ("minus_subset",        propMinusSubset),
    ("filter_subset",       propFilterSubset),
    ("distinct_idem",       propDistinctIdem),
    ("orderby_perm",        propOrderByPerm),
    ("ntriples_roundtrip",  propNTriplesRoundTrip),
    ("turtle_roundtrip",    propTurtleRoundTrip),
    ("srx_roundtrip",       propSrxRoundTrip),
    ("srj_roundtrip",       propSrjRoundTrip),
    ("csv_roundtrip",       propCsvRoundTrip),
    ("tsv_roundtrip",       propTsvRoundTrip),
    ("rdfc_relabel",        propRdfcRelabel),
    ("iso_reflexive",       propIsoReflexive),
    ("iso_relabel",         propIsoRelabel),
    ("query_parses",        propQueryParses),
    ("distinct_no_dup",     propDistinctNoDup) ]

end L4Factoidal.Testing
