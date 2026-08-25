/-
L4Factoidal.Cottas.Ballyhoo — the eager-load COTTAS dataset store.

Port of `formal/fstar/Parser.BallyhooCOTTAS.fst` (241 lines): the native
model of a COTTAS-style columnar quad backend — artifact summaries, the
dictionary-reference encoding of a bound triple pattern, and the pure
functions that sit on top of a store's lookup operations.

## The `assume val`s become a RECORD OF FUNCTIONS

The F\* module declares an abstract `cottas_handle` and eleven
`assume val`s over it: open, close, summary, named graphs, four
encoders, four decoders, and `search`. Each is realised in OCaml glue.

Lean's port has no `assume val` and no axiom. The eleven operations
become fields of `StoreOps`, supplied by whoever builds the store. This
is the SAME move `RDF.StoreCapabilities` already made for the backend
tag: what was an opaque handle plus a set of assumed operations becomes
a record the caller fills in, and every function here is total and pure
in that record.

Two things follow, and both are improvements rather than costs:

* The derived functions are ordinary definitions with ordinary
  equations, so they can be REASONED about. The F\* module's own
  comments record that three of them (`cottas_estimate`,
  `cottas_predicate_present_in_graph`,
  `cottas_graph_candidates_for_predicate`) were lifted OUT of glue
  precisely so their relationship to `search` would be stated rather
  than implicit. Here that relationship is definitional:
  `estimate ops ds b = (ops.search ds b).length`, and the theorems below
  prove what the F\* comments assert in prose.
* A test can supply a `StoreOps` built from a list of quads, with no
  file and no glue. The pins at the bottom do exactly that, so the
  module's behaviour is checked rather than described.

Actual file and mmap I/O stays where it belongs — outside this module,
in whatever builds the `StoreOps`.

## The three-state graph bound

`GraphBound` is three explicit states, NOT an `Option GraphRef`. The F\*
module records why: the optional form conflated "no constraint on the
graph column" with "the caller means the default graph", and for the
on-disk backend that conflation let a plain basic graph pattern over the
default graph union in every named graph's rows as well.

`unbound` is kept because the eager-load path has it, and is marked here
as the F\* module marks it: the on-disk backend does not produce it.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.Cottas.Ballyhoo

open L4Factoidal.RDF

/-! ## Artifact summaries

Descriptive metadata about a COTTAS file: how it is encoded, how many
rows, how the dictionary is sized. Nothing here decides a query; it is
what a `--describe` reads. -/

inductive Encoding where
  | plain
  | dictionary
  | rle
  | delta
deriving DecidableEq, Repr, Inhabited

inductive ColumnKind where
  | subject
  | predicate
  | object
  | graph
deriving DecidableEq, Repr, Inhabited

structure ColumnSummary where
  kind      : ColumnKind
  numValues : Nat
  nullCount : Nat
  encoding  : Encoding
deriving DecidableEq, Repr, Inhabited

structure DictionarySummary where
  numTerms     : Nat
  numGraphs    : Nat
  bytesStrings : Nat
deriving DecidableEq, Repr, Inhabited

structure RowGroupSummary where
  index   : Nat
  numRows : Nat
  columns : List ColumnSummary
deriving DecidableEq, Repr, Inhabited

structure ArtifactSummary where
  path         : String
  numQuads     : Nat
  numRowGroups : Nat
  dictionary   : Option DictionarySummary := none
  rowGroups    : List RowGroupSummary := []
deriving DecidableEq, Repr, Inhabited

/-! ## Dictionary references -/

abbrev TermRef := Nat
abbrev GraphRef := Nat

/-- The graph-column constraint on a query pattern. Three states, and
the reason is in the module header: an `Option GraphRef` conflates "no
constraint" with "the default graph". -/
inductive GraphBound where
  /-- No constraint: a default-graph row and a named-graph row both
  match. The on-disk backend never produces this; the eager-load path
  below does. -/
  | unbound
  /-- The row must be a default-graph row. -/
  | default
  /-- The row must belong to the named graph with this dictionary
  reference. -/
  | named (r : GraphRef)
deriving DecidableEq, Repr, Inhabited

/-- A query pattern with every bound position already encoded to a
dictionary reference. `none` in a term position means unbound. -/
structure BoundQp where
  s : Option TermRef := none
  p : Option TermRef := none
  o : Option TermRef := none
  g : GraphBound := .unbound
deriving DecidableEq, Repr, Inhabited

/-- One matching row, still in dictionary references. -/
structure QpRow where
  s : Option TermRef
  p : Option TermRef
  o : Option TermRef
  g : Option GraphRef
deriving DecidableEq, Repr, Inhabited

/-! ## The store and its operations -/

/-- What a COTTAS artifact is, from this module's point of view: a path,
an optional summary, and an opaque identity the operations recognise.
The F\* `cottas_handle` is an `assume type`; here the identity is a
`Nat`, so a caller with several open artifacts can tell them apart and a
test can build one with no file at all. -/
structure DatasetStore where
  artifactPath : String
  summary      : Option ArtifactSummary := none
  handle       : Nat := 0
deriving DecidableEq, Repr, Inhabited

structure NamedGraphStore where
  name    : Iri
  ref     : GraphRef
  dataset : DatasetStore
deriving DecidableEq, Repr, Inhabited

/-- The eleven operations the F\* module assumes. A backend supplies
them; nothing in this module assumes them. -/
structure StoreOps where
  summary        : DatasetStore → Option ArtifactSummary
  namedGraphs    : DatasetStore → List NamedGraphStore
  encodeSubject  : DatasetStore → Subject → Option TermRef
  encodePredicate : DatasetStore → WfIri → Option TermRef
  encodeObject   : DatasetStore → Term → Option TermRef
  encodeGraphName : DatasetStore → Iri → Option GraphRef
  decodeSubject  : DatasetStore → TermRef → Option Subject
  decodePredicate : DatasetStore → TermRef → Option WfIri
  decodeObject   : DatasetStore → TermRef → Option Term
  decodeGraphName : DatasetStore → GraphRef → Option Iri
  search         : DatasetStore → BoundQp → List QpRow

/-! ### The decoders return `Option`, and the F\* ones do not

`cottas_decode_subject : … -> Tot subject` is total in F\* because its
OCaml realisation raises on an unknown reference and F\* cannot see that.
A reference that is not in the dictionary has no subject, so the honest
Lean type says so. `rowToQuad` below therefore DROPS a row it cannot
decode, exactly as it already drops a row with an unbound position. -/

/-! ## Derived operations

Every function below is pure in `ops`. The F\* module lifted the first
three out of OCaml glue (issue #448 wave 2) so their relationship to
`search` would be stated; here that relationship is the definition. -/

def lookupNamedGraph (ops : StoreOps) (ds : DatasetStore) (name : Iri) :
    Option NamedGraphStore :=
  (ops.namedGraphs ds).find? (fun ng => ng.name == name)

/-- The estimate IS an exact count. The F\* comment records that its
OCaml realisation was `List.length (cottas_search ds bound)` all along,
and that the invariant lived only in the glue. -/
def estimate (ops : StoreOps) (ds : DatasetStore) (b : BoundQp) : Nat :=
  (ops.search ds b).length

/-- A predicate is present in a named graph when it encodes to a known
reference AND at least one row in that graph matches it. -/
def predicatePresentInGraph (ops : StoreOps) (ng : NamedGraphStore)
    (pred : WfIri) : Bool :=
  match ops.encodePredicate ng.dataset pred with
  | none => false
  | some predRef =>
      estimate ops ng.dataset { p := some predRef, g := .named ng.ref } > 0

def graphCandidatesForPredicate (ops : StoreOps) (ds : DatasetStore)
    (pred : WfIri) : List NamedGraphStore :=
  (ops.namedGraphs ds).filter (fun ng => predicatePresentInGraph ops ng pred)

/-- Encode a triple pattern's bound positions.

The graph slot keeps the F\* behaviour of the eager-load path, and the
F\* comment on it is kept too: no graph IRI given, OR a graph IRI this
corpus's dictionary does not know, both mean "no constraint" rather than
"definitively empty". That is the dead-code path — the live on-disk
backend does not build its bound this way — and reproducing it without
saying so would hide a known sharp edge. -/
def buildBoundQp (ops : StoreOps) (ds : DatasetStore)
    (s : Option Subject) (p : Option WfIri) (o : Option Term)
    (g : Option Iri) : BoundQp :=
  { s := s.bind (ops.encodeSubject ds)
  , p := p.bind (ops.encodePredicate ds)
  , o := o.bind (ops.encodeObject ds)
  , g := match g with
         | none => .unbound
         | some gv => match ops.encodeGraphName ds gv with
                      | none => .unbound
                      | some r => .named r }

/-- One row back to a quad. A row with an unbound position, or one whose
reference the dictionary cannot decode, yields nothing. -/
def rowToQuad (ops : StoreOps) (ds : DatasetStore) (row : QpRow) :
    Option (Triple × Option Iri) :=
  match row.s, row.p, row.o with
  | some sr, some pr, some orf =>
      match ops.decodeSubject ds sr, ops.decodePredicate ds pr,
            ops.decodeObject ds orf with
      | some sv, some pv, some ov =>
          some ({ s := sv, p := pv, o := ov },
                row.g.bind (ops.decodeGraphName ds))
      | _, _, _ => none
  | _, _, _ => none

def rowsToQuads (ops : StoreOps) (ds : DatasetStore) (rows : List QpRow) :
    List (Triple × Option Iri) :=
  rows.filterMap (rowToQuad ops ds)

/-! ## What the derived operations satisfy

The F\* module states these three relationships in COMMENTS, as the
reason the functions were lifted out of glue. Here they are theorems. -/

/-- The estimate is exact, not a heuristic. -/
theorem estimate_eq_search_length (ops : StoreOps) (ds : DatasetStore)
    (b : BoundQp) : estimate ops ds b = (ops.search ds b).length := rfl

/-- Presence means a row really exists: the search for that predicate in
that graph is non-empty. -/
theorem predicatePresent_iff (ops : StoreOps) (ng : NamedGraphStore)
    (pred : WfIri) :
    predicatePresentInGraph ops ng pred = true ↔
      ∃ predRef, ops.encodePredicate ng.dataset pred = some predRef ∧
        (ops.search ng.dataset { p := some predRef, g := .named ng.ref }) ≠ [] := by
  simp only [predicatePresentInGraph]
  cases h : ops.encodePredicate ng.dataset pred with
  | none => simp
  | some predRef =>
      simp only [estimate, decide_eq_true_eq, gt_iff_lt, List.length_pos_iff]
      constructor
      · intro hne; exact ⟨predRef, rfl, hne⟩
      · rintro ⟨r, hr, hne⟩
        simp only [Option.some.injEq] at hr
        subst hr
        exact hne

/-- Every candidate graph really carries the predicate. A caller that
skipped a graph this returns would drop rows. -/
theorem graphCandidates_present (ops : StoreOps) (ds : DatasetStore)
    (pred : WfIri) :
    ∀ ng ∈ graphCandidatesForPredicate ops ds pred,
      predicatePresentInGraph ops ng pred = true := by
  intro ng hng
  simp only [graphCandidatesForPredicate, List.mem_filter] at hng
  exact hng.2

/-- And no graph that carries it is left out. Together with the previous
theorem this says the filter is exact in both directions. -/
theorem graphCandidates_complete (ops : StoreOps) (ds : DatasetStore)
    (pred : WfIri) :
    ∀ ng ∈ ops.namedGraphs ds, predicatePresentInGraph ops ng pred = true →
      ng ∈ graphCandidatesForPredicate ops ds pred := by
  intro ng hmem hpres
  simp only [graphCandidatesForPredicate, List.mem_filter]
  exact ⟨hmem, hpres⟩

/-- A looked-up named graph carries the name it was looked up by. -/
theorem lookupNamedGraph_name (ops : StoreOps) (ds : DatasetStore) (name : Iri)
    {ng : NamedGraphStore} (h : lookupNamedGraph ops ds name = some ng) :
    ng.name = name := by
  simp only [lookupNamedGraph] at h
  have := List.find?_some h
  simpa using this

/-- `rowsToQuads` never invents a quad: every quad it returns comes from
a row of the input. -/
theorem rowsToQuads_from_rows (ops : StoreOps) (ds : DatasetStore)
    (rows : List QpRow) :
    ∀ q ∈ rowsToQuads ops ds rows, ∃ row ∈ rows, rowToQuad ops ds row = some q := by
  intro q hq
  simpa [rowsToQuads, List.mem_filterMap] using hq

/-! ## Pinned behaviour

A store built from a list of quads, with no file and no glue. Every pin
below states a positive count, because a `StoreOps` whose `search`
always returned `[]` would satisfy any pin phrased as "nothing wrong
came back". -/

section Pins

private def iriOf (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def terms : List Term :=
  [.iri (iriOf "http://example/a"), .iri (iriOf "http://example/b"),
   .iri (iriOf "http://example/p"), .iri (iriOf "http://example/q")]

private def graphs : List Iri := ["http://example/g1", "http://example/g2"]

private def refOfTerm (t : Term) : Option TermRef := terms.idxOf? t
private def refOfGraph (n : Iri) : Option GraphRef := graphs.idxOf? n

/-- Four quads: `a p b` in g1, `a q b` in g1, `a p b` in g2, and one in
the default graph. -/
private def quads : List (QpRow) :=
  [ { s := refOfTerm (.iri (iriOf "http://example/a"))
    , p := refOfTerm (.iri (iriOf "http://example/p"))
    , o := refOfTerm (.iri (iriOf "http://example/b"))
    , g := refOfGraph "http://example/g1" }
  , { s := refOfTerm (.iri (iriOf "http://example/a"))
    , p := refOfTerm (.iri (iriOf "http://example/q"))
    , o := refOfTerm (.iri (iriOf "http://example/b"))
    , g := refOfGraph "http://example/g1" }
  , { s := refOfTerm (.iri (iriOf "http://example/a"))
    , p := refOfTerm (.iri (iriOf "http://example/p"))
    , o := refOfTerm (.iri (iriOf "http://example/b"))
    , g := refOfGraph "http://example/g2" }
  , { s := refOfTerm (.iri (iriOf "http://example/a"))
    , p := refOfTerm (.iri (iriOf "http://example/p"))
    , o := refOfTerm (.iri (iriOf "http://example/b"))
    , g := none } ]

private def matchesBound (b : BoundQp) (r : QpRow) : Bool :=
  (b.s.isNone || b.s == r.s) && (b.p.isNone || b.p == r.p)
    && (b.o.isNone || b.o == r.o)
    && (match b.g with
        | .unbound => true
        | .default => r.g.isNone
        | .named x => r.g == some x)

private def testOps : StoreOps :=
  { summary := fun ds => ds.summary
  , namedGraphs := fun ds =>
      graphs.zipIdx.map (fun (n, i) => { name := n, ref := i, dataset := ds })
  , encodeSubject := fun _ s => refOfTerm s.toTerm
  , encodePredicate := fun _ p => refOfTerm (.iri p)
  , encodeObject := fun _ o => refOfTerm o
  , encodeGraphName := fun _ n => refOfGraph n
  , decodeSubject := fun _ r => (terms[r]?).bind Term.toSubject?
  , decodePredicate := fun _ r =>
      match terms[r]? with | some (.iri i) => some i | _ => none
  , decodeObject := fun _ r => terms[r]?
  , decodeGraphName := fun _ r => graphs[r]?
  , search := fun _ b => quads.filter (matchesBound b) }

private def testDs : DatasetStore := { artifactPath := "mem:test" }

/-! Four rows in the artifact, so a pin that counts is not counting
nothing. -/
#guard (testOps.search testDs {}).length == 4

/-! The estimate is the count. -/
#guard estimate testOps testDs {} == 4

/-! `p` appears in both named graphs; `q` only in the first. This is the
pin that would fail if `predicatePresentInGraph` ignored the graph
bound. -/
#guard (graphCandidatesForPredicate testOps testDs
          (iriOf "http://example/p")).length == 2
#guard (graphCandidatesForPredicate testOps testDs
          (iriOf "http://example/q")).length == 1

/-! A predicate the dictionary does not know is present nowhere. -/
#guard (graphCandidatesForPredicate testOps testDs
          (iriOf "http://example/absent")).isEmpty

/-! The three graph-bound states differ, which is the whole reason the
bound is not an `Option`. Unbound sees all four rows, `default` sees the
one with no graph, and `named` sees that graph's rows. -/
#guard (testOps.search testDs { g := .unbound }).length == 4
#guard (testOps.search testDs { g := .default }).length == 1
#guard (testOps.search testDs { g := .named 0 }).length == 2

/-! A round trip: encode a triple pattern, search, decode. -/
#guard (rowsToQuads testOps testDs
          (testOps.search testDs
            (buildBoundQp testOps testDs
              (some (.iri (iriOf "http://example/a")))
              (some (iriOf "http://example/p")) none none))).length == 3

/-! And the decoded quads carry the right predicate. -/
#guard (rowsToQuads testOps testDs
          (testOps.search testDs
            (buildBoundQp testOps testDs none
              (some (iriOf "http://example/q")) none none))).all
        (fun q => q.1.p == iriOf "http://example/q")

/-! Looking a named graph up by name gives that graph. -/
#guard match lookupNamedGraph testOps testDs "http://example/g2" with
       | some ng => ng.name == "http://example/g2" && ng.ref == 1
       | none    => false

#guard (lookupNamedGraph testOps testDs "http://example/absent").isNone

/-! The documented sharp edge, pinned so it cannot be mistaken for a
bug later: an UNKNOWN graph IRI encodes to `unbound`, not to an empty
result. The F\* module records the same behaviour on the same path. -/
#guard (buildBoundQp testOps testDs none none none
          (some "http://example/absent")).g == GraphBound.unbound

end Pins

end L4Factoidal.Cottas.Ballyhoo
