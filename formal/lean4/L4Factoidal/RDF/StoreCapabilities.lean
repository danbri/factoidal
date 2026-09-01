/-
L4Factoidal.RDF.StoreCapabilities — the store capability seam.

Port of `formal/fstar/RDF.Store.Capabilities.fst` (504 lines).

## What the seam is for

A SPARQL evaluator has to reach several different physical stores: an
in-memory index, a COTTAS file on disk, an HDT file, a federation of
several, a COTTAS base with an update delta laid over it. Before this
seam, the planner asked WHICH KIND of store it held and branched — six
separate dispatchers, each matching on the same backend tag.

`StoreCaps` replaces the tag with a record of functions. Every backend
already had the entry points; the record is the one indirection that
takes the place of `match backend with`. A new backend adds a builder,
not a new arm in six places.

## Which parts of the F\* module are here, and which are not

The F\* module deliberately carries ONLY the types, the in-memory
builder and the union combinator, and keeps two more builders in
sibling modules so this one stays free of file and memory-map calls.
This port keeps that split: the COTTAS-on-disk builder
(`RDF.Store.Capabilities.Cottas`) and the delta overlay
(`RDF.Store.Capabilities.Delta`) are NOT here, because both depend on
modules the Lean tree has not ported yet (`RDF.CottasStore` and
`RDF.Store.Columnar.DeltaMerge`).

## The two fields that are `Option`, and why they differ

`distinctPredicates` and `solveSelective` are both optional, and they
mean OPPOSITE things to a caller.

`distinctPredicates` is a pure fast path. `none` means the backend has
no cheap way to enumerate its predicates, and the caller falls back to
reading rows. Missing it costs time. Note the DOUBLE option: `some f`
means the backend can try, and `f ()` returns an option again because
whether it works is a per-corpus fact discovered only when the
dictionary pages are read. `none` from `f ()` means "tried, could not
do it cheaply this time" and never "this store has no predicates".

`solveSelective` STANDS IN for `solve`. A caller that reads `none` for
one member of a composed capability and skips that member drops rows,
which is a wrong answer rather than a slow one. Every composition below
accounts for every member explicitly, and `unionCaps` always advertises
`some` with the per-member fallback inside.
-/
import L4Factoidal.SPARQL.Algebra
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.OWL.RLClosureIndexed

namespace L4Factoidal.RDF

open L4Factoidal.SPARQL (PatternBound patternBoundAll boundMatches tripleMatchesBound)

/-! ## What a store advertises -/

/-- The policy questions the planner used to answer by knowing the
backend's kind. -/
structure StoreCapsFlags where
  /-- Named graphs, or a default graph only? A single HDT 1.0 file is
  triples-only; COTTAS carries a graph column. -/
  supportsNamedGraphs : Bool
  /-- Is there a durable write path? In-memory and COTTAS-plus-delta:
  yes. HDT and a bare COTTAS base: no. -/
  supportsUpdate : Bool
  /-- Can it answer a bounded COUNT-star or ASK without materialising
  rows? -/
  streamingShapes : Bool
  /-- Is `estimate` exact, or a join-order hint that may approximate?
  The in-memory index is exact; the on-disk reader approximates when
  bounds are present. -/
  estimateIsExact : Bool
  /-- Can it tell "genuinely empty" from "column I could not decode"?
  Only a columnar on-disk reader can. -/
  canReportDecodeFail : Bool
  deriving Repr, DecidableEq, Inhabited

/-! ## The read seam -/

/-- Every backend realises this record. Each field is an entry point
that backend already had. -/
structure StoreCaps where
  flags : StoreCapsFlags
  /-- Bounds in, matched triples out. The result is the backend's own
  already-decoded triples: the evaluator never sees rows, cells or
  dictionary ids. -/
  solve : PatternBound → List Triple
  /-- LIMIT pushdown. A backend with real pushdown stops early; the
  default realisation is `capsTakeN n (solve b)`. -/
  solveLimited : PatternBound → Nat → List Triple
  /-- Join-order estimate. May approximate exactly when
  `flags.estimateIsExact` is false. -/
  estimate : PatternBound → Nat
  /-- Exact count for a result-producing caller (COUNT-star, per-graph
  GROUP BY). For the in-memory store this IS `estimate`. -/
  countExact : PatternBound → Nat
  /-- Predicate-presence short circuit. -/
  predicatePresent : WfIri → Bool
  /-- Did a read touch a column this reader could not decode? -/
  decodeFailure : Unit → Bool
  /-- Cheap DISTINCT-predicate enumeration; see the header for what
  each layer of the double option means. -/
  distinctPredicates : Option (Unit → Option (List WfIri))
  /-- Column-need-aware sibling of `solve`, returning the SAME rows in
  the SAME order for any `ColNeed`. -/
  solveSelective : Option (PatternBound → ColNeed → List Triple)

/-! ## The write seam

Only a read-write backend builds this. A read-only backend advertises
`supportsUpdate := false` and carries `none`: it never allocates a
delta log, and the in-memory store never runs a rename protocol. -/

structure StoreWriteCaps where
  /-- Apply one committed UPDATE request's operations and return the
  post-update READ seam. For COTTAS-plus-delta this appends and syncs a
  batch and returns base-plus-delta; for the in-memory store it rebuilds
  the index. It is in `IO` because durability is I/O — the BYTES it
  writes are specified in `Storage.DeltaLog`, not here. -/
  applyDelta : List Storage.DeltaEntry → IO StoreCaps
  /-- Optional planner input: exact count of delta entries matching a
  bound. `none` just after a compaction, so a store with no delta pays
  nothing. -/
  deltaStats : Option (PatternBound → Nat)

/-- A store is its read seam plus, when read-write, its write seam.
The invariant the builders maintain: `write` is `some` exactly when
`read.flags.supportsUpdate` is true. -/
structure Store where
  read : StoreCaps
  write : Option StoreWriteCaps

/-- The invariant stated as a predicate, so a builder can be checked
against it rather than trusted. -/
def Store.wellFormed (st : Store) : Bool :=
  st.read.flags.supportsUpdate == st.write.isSome

/-! ## Truncation

The F\* module keeps a local copy of the canonical `list_take_n`
because it sits BELOW the module that owns it and cannot import
upward. Lean's `List.take` is that function, so this is a name, not a
copy. -/

def capsTakeN (n : Nat) (xs : List α) : List α := xs.take n

/-! ## The union combinator

A read-only federation over a list of read seams. It mirrors the
per-field arithmetic the six tag dispatchers did for a union backend,
without a union-shaped constructor. -/

def unionSolve (members : List StoreCaps) (b : PatternBound) : List Triple :=
  members.flatMap (fun m => m.solve b)

def unionEstimate (members : List StoreCaps) (b : PatternBound) : Nat :=
  members.foldl (fun acc m => acc + m.estimate b) 0

def unionCountExact (members : List StoreCaps) (b : PatternBound) : Nat :=
  members.foldl (fun acc m => acc + m.countExact b) 0

def unionPredicatePresent (members : List StoreCaps) (pred : WfIri) : Bool :=
  members.any (fun m => m.predicatePresent pred)

def unionDecodeFailure (members : List StoreCaps) : Bool :=
  members.any (fun m => m.decodeFailure ())

/-! ### Real per-member LIMIT pushdown

The naive form — solve every member in full, then truncate — returns
the SAME list. It is not the same COST. A member with real on-disk
pushdown would be made to decode its entire result before the union
threw most of it away, which defeats the one path that exists to avoid
that. So each member is asked for only its REMAINING budget, and the
walk stops before touching a later member at all once the budget is
spent. -/

def unionSolveLimitedAcc : List StoreCaps → PatternBound → Nat → List Triple → Nat →
    List Triple
  | [], _, _, accRev, _ => accRev
  | m :: rest, b, limit, accRev, accLen =>
      if accLen ≥ limit then accRev
      else
        let part := m.solveLimited b (limit - accLen)
        unionSolveLimitedAcc rest b limit (part.reverse ++ accRev) (accLen + part.length)

def unionSolveLimited (members : List StoreCaps) (b : PatternBound) (limit : Nat) :
    List Triple :=
  if limit == 0 then []
  else capsTakeN limit (unionSolveLimitedAcc members b limit [] 0).reverse

/-! ### DISTINCT predicates across a union

The union's predicate set is the union of its members' sets, so the
capability composes — but only when every member is accounted for. Per
member, in order:

* advertises the capability and it succeeds → contribute its predicates;
* advertises it and it fails → the whole union is `none`, and the caller
  falls back;
* does not advertise it but is EMPTY → contributes nothing. This case is
  the one that matters in practice: a command line that loads only
  on-disk data still carries an always-present empty in-memory member,
  and treating that member as a blanket `none` made the fast path
  unreachable;
* does not advertise it and is non-empty → the whole union is `none`.

The emptiness probe runs inside the closure, so it costs one count on an
in-memory member only when a caller actually asks. -/

def capsIriDedupe (l : List WfIri) : List WfIri :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def unionDistinctPredicatesAcc : List WfIri → List StoreCaps → Option (List WfIri)
  | acc, [] => some (capsIriDedupe acc)
  | acc, m :: rest =>
      match m.distinctPredicates with
      | some f =>
          match f () with
          | some ps => unionDistinctPredicatesAcc (acc ++ ps) rest
          | none    => none
      | none =>
          if m.countExact patternBoundAll == 0 then unionDistinctPredicatesAcc acc rest
          else none

/-! ### Selective solve across a union

Always `some`, never a blanket `none`: each member falls back to its own
plain `solve` when it has no accelerated realisation. This mirrors
`unionSolve` exactly, choosing the accelerated call where one exists. -/

def unionSolveSelective (members : List StoreCaps) (b : PatternBound) (need : ColNeed) :
    List Triple :=
  members.flatMap (fun m =>
    match m.solveSelective with
    | some f => f b need
    | none   => m.solve b)

def unionCaps (members : List StoreCaps) : StoreCaps :=
  { flags :=
      { supportsNamedGraphs := true
      , supportsUpdate := false          -- read-side federation only
      , streamingShapes := true
        -- a sum of possibly-inexact members is not claimed exact
      , estimateIsExact := false
      , canReportDecodeFail := true }
  , solve := fun b => unionSolve members b
  , solveLimited := fun b n => unionSolveLimited members b n
  , estimate := fun b => unionEstimate members b
  , countExact := fun b => unionCountExact members b
  , predicatePresent := fun pred => unionPredicatePresent members pred
  , decodeFailure := fun _ => unionDecodeFailure members
  , distinctPredicates := some (fun _ => unionDistinctPredicatesAcc [] members)
  , solveSelective := some (fun b need => unionSolveSelective members b need) }

/-! ## The in-memory builder

Wraps the indexed in-memory graph. Zero new logic: every field is a
call the tag dispatcher already made. -/

/-- An OWL in-memory index hashes object terms structurally, while the SPARQL
    matcher uses `Term.eqb`: language tags compare case-insensitively and
    `rdf:XMLLiteral` values compare after canonical XML.  An object in either
    class cannot safely select one exact hash bucket, because an equivalent
    stored spelling may live in another bucket.  This asks only whether the
    exact object access path is a *complete* candidate set; the normal matcher
    always remains the semantic authority. -/
def exactObjectIndexKeySafe : Term → Bool
  | .iri _ | .bnode _ => true
  | .literal literal =>
      literal.val.langTag.isNone && literal.val.datatype != rdfXMLLiteral
  | .tripleTerm _ _ _ => false

/-- Matching triples for a bound, read off the index. The index's own
    access paths are used only when their structural keys are complete for
    SPARQL term equality; otherwise a broader predicate/subject candidate set
    is selected before `tripleMatchesBound` applies `Term.eqb`. -/
def igSearch (i : OWL.RL.Index) (b : PatternBound) : List Triple :=
  let candidates :=
    match b.s, b.p, b.o with
    | some s, some p, _ => i.withSubjPred s p
    | _,      some p, some o =>
        if exactObjectIndexKeySafe o then i.withPredObj p o else i.withPred p
    | some s, _,      _ => i.withSubj s
    | _,      some p, _ => i.withPred p
    | _,      _,      some o =>
        if exactObjectIndexKeySafe o then i.withObj o else i.toGraph
    | _,      _,      _ => i.toGraph
  tripleMatchesBound b candidates

def igEstimate (i : OWL.RL.Index) (b : PatternBound) : Nat := (igSearch i b).length

def capsOfIndexed (i : OWL.RL.Index) : StoreCaps :=
  { flags :=
      { supportsNamedGraphs := true
      , supportsUpdate := true           -- rebuilt by re-indexing
      , streamingShapes := true
      , estimateIsExact := true
      , canReportDecodeFail := false }
  , solve := fun b => igSearch i b
  , solveLimited := fun b n => capsTakeN n (igSearch i b)
  , estimate := fun b => igEstimate i b
    -- the in-memory estimate is already exact
  , countExact := fun b => igEstimate i b
  , predicatePresent := fun pred => igEstimate i { p := some pred } > 0
  , decodeFailure := fun _ => false
    -- no dictionary-page shortcut exists in memory, and rows are
    -- already in memory, so the ordinary GROUP BY path is cheap enough
  , distinctPredicates := none
    -- nothing to defer: there is no column-decode cost in memory
  , solveSelective := none }

/-! ## Datasets

A `StoreCaps` is already graph-scoped: the in-memory builder wraps ONE
graph's content. What was missing at the seam was a way to ask for "the
capability record of the graph named G" or "every graph name this
dataset carries" without stepping back through the backend tag. -/

structure DatasetCaps where
  default : StoreCaps
  named : List (Iri × StoreCaps)

/-- The capability record for a named graph, or `none` when the dataset
carries no graph by that name. -/
def datasetCapsLookupNamed (name : Iri) : List (Iri × StoreCaps) → Option StoreCaps
  | [] => none
  | (n, caps) :: rest =>
      if n == name then some caps else datasetCapsLookupNamed name rest

/-- Every named-graph IRI this composition carries. -/
def datasetCapsListGraphs (named : List (Iri × StoreCaps)) : List Iri :=
  named.map Prod.fst

/-! ## Residual, stated rather than left implicit

Every field above is TRIPLE-shaped: the bound pins subject, predicate
and object, and has no graph position. There is no quad-native
`solveQuad` that pushes an unbound GRAPH variable into ONE seam call
spanning every graph. `GRAPH ?g { ?s ?p ?o }` therefore enumerates
`named` and calls `solve` once per graph. A COTTAS store carries the
graph as a first-class column and COULD answer that in one walk. That
is real unimplemented work, the same residual the F\* module records. -/

/-! ## Build-time checks -/

section Checks

open L4Factoidal.SPARQL

/-- A fixture IRI. The `else` arm is unreachable for every literal
below and exists only so the helper is total without a proof argument
at each call site. -/
private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def iriT (s : String) : Term := .iri (iriW s)
private def iriS (s : String) : Subject := .iri (iriW s)
private def iriP (s : String) : WfIri := iriW s

private def a : Triple := ⟨iriS "http://e.org/a", iriP "http://e.org/p", iriT "http://e.org/1"⟩
private def b2 : Triple := ⟨iriS "http://e.org/b", iriP "http://e.org/p", iriT "http://e.org/2"⟩
private def c : Triple := ⟨iriS "http://e.org/c", iriP "http://e.org/q", iriT "http://e.org/3"⟩
private def langEn : Term := .literal (Literal.langString "xyz" "en")
private def langEN : Term := .literal (Literal.langString "xyz" "EN")
private def lang1 : Triple := ⟨iriS "http://e.org/lang1", iriP "http://e.org/lang", langEn⟩
private def lang2 : Triple := ⟨iriS "http://e.org/lang2", iriP "http://e.org/lang", langEN⟩

private def capsA : StoreCaps := capsOfIndexed (OWL.RL.Index.ofGraph [a, b2])
private def capsB : StoreCaps := capsOfIndexed (OWL.RL.Index.ofGraph [c])
private def capsEmpty : StoreCaps := capsOfIndexed (OWL.RL.Index.ofGraph [])
private def capsLang : StoreCaps := capsOfIndexed (OWL.RL.Index.ofGraph [lang1, lang2])

/-! ### The in-memory builder answers bounds -/

#guard (capsA.solve patternBoundAll).length == 2
#guard (capsA.solve { p := some (iriP "http://e.org/p") }).length == 2
#guard (capsA.solve { p := some (iriP "http://e.org/q") }).length == 0
#guard capsA.solve { s := some (iriS "http://e.org/a") } == [a]
#guard capsA.solve { s := some (iriS "http://e.org/a"), o := some (iriT "http://e.org/2") } == []
#guard capsA.predicatePresent (iriP "http://e.org/p")
#guard !capsA.predicatePresent (iriP "http://e.org/q")
-- A structural hash bucket is not complete for language-tag equality; the
-- predicate bucket plus `Term.eqb` returns both W3C-equivalent spellings.
#guard !exactObjectIndexKeySafe langEn
#guard (capsLang.solve { p := some (iriP "http://e.org/lang"), o := some langEn }).length == 2

/-! ### The union is the concatenation, in member order -/

#guard (unionCaps [capsA, capsB]).solve patternBoundAll == [a, b2, c]
#guard (unionCaps [capsA, capsB]).countExact patternBoundAll == 3
#guard (unionCaps []).solve patternBoundAll == []
#guard (unionCaps [capsA, capsB]).predicatePresent (iriP "http://e.org/q")

/-! ### LIMIT pushdown truncates to exactly the limit, in order

The second check is the one that matters: a limit that the FIRST member
alone can fill must not reach the second member at all. It is checked by
result rather than by instrumentation, so it pins the answer; the
early-exit branch is what makes the cost right. -/

#guard (unionCaps [capsA, capsB]).solveLimited patternBoundAll 2 == [a, b2]
#guard (unionCaps [capsA, capsB]).solveLimited patternBoundAll 1 == [a]
#guard (unionCaps [capsA, capsB]).solveLimited patternBoundAll 0 == []
#guard (unionCaps [capsA, capsB]).solveLimited patternBoundAll 99 == [a, b2, c]

/-! ### Selective solve returns the same rows as plain solve

This is the property the field's contract rests on: narrowing `ColNeed`
changes which positions are cheaply decoded, never which rows come
back. -/

private def sameAsSolve (caps : StoreCaps) (b : PatternBound) (need : ColNeed) : Bool :=
  match caps.solveSelective with
  | none   => true                       -- no accelerated realisation to check
  | some f => f b need == caps.solve b

#guard sameAsSolve (unionCaps [capsA, capsB]) patternBoundAll colNeedAll
#guard sameAsSolve (unionCaps [capsA, capsB]) patternBoundAll colNeedNone
#guard sameAsSolve (unionCaps [capsA, capsB]) { p := some (iriP "http://e.org/p") }
         { s := true, p := false, o := false }

/-! ### DISTINCT predicates: the empty-member rule

The in-memory builder does not advertise the capability. A union of two
non-empty in-memory members therefore cannot enumerate cheaply and must
say so. A union whose non-advertising members are all EMPTY can: the
empty ones contribute nothing, which is why the blanket refusal was
wrong. -/

private def askDistinct (caps : StoreCaps) : Option (Option (List WfIri)) :=
  caps.distinctPredicates.map (fun f => f ())

#guard askDistinct (unionCaps [capsA, capsB]) == some none
#guard askDistinct (unionCaps [capsEmpty, capsEmpty]) == some (some [])
#guard askDistinct (unionCaps []) == some (some [])

/-! ### Dedupe keeps a shared predicate once -/

#guard capsIriDedupe [iriP "http://e.org/p", iriP "http://e.org/q", iriP "http://e.org/p"]
         == [iriP "http://e.org/p", iriP "http://e.org/q"]

/-! ### Dataset lookup and enumeration -/

private def ds : DatasetCaps :=
  { default := capsA, named := [("http://e.org/g1", capsB), ("http://e.org/g2", capsEmpty)] }

#guard (datasetCapsLookupNamed "http://e.org/g1" ds.named).isSome
#guard (datasetCapsLookupNamed "http://e.org/missing" ds.named).isNone
#guard datasetCapsListGraphs ds.named == ["http://e.org/g1", "http://e.org/g2"]
#guard (match datasetCapsLookupNamed "http://e.org/g1" ds.named with
        | some caps => caps.solve patternBoundAll == [c]
        | none      => false)

/-! ### The read-only union is well formed as a store -/

#guard Store.wellFormed { read := unionCaps [capsA, capsB], write := none }
#guard !Store.wellFormed { read := capsOfIndexed (OWL.RL.Index.ofGraph []), write := none }

end Checks

end L4Factoidal.RDF
