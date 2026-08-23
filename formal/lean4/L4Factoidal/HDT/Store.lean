/-
L4Factoidal.HDT.Store — the HDT store boundary.

Port of `formal/fstar/Parser.BallyhooHDT.fst` (352 lines): the layer
between a SPARQL backend and the three verified HDT reader stages,
`HDT/Container.lean`, `HDT/Dictionary.lean` and `HDT/Triples.lean`.

## What this module retired, in the F\* tree and here

The F\* header records it: this file used to shell out to an external
`hdtSearch` CLI through 555 lines of unverified OCaml
(`ballyhoo_hdt_runtime.sh`, the #253 debt). Stage 4 deleted that
runtime and made every function ordinary total F\* over stages 1–3.

The Lean port keeps that shape and goes one step further on I/O: the F\*
reader still reaches file bytes through `Parquet.Footer`'s byte-range
primitive, while `HDT/Container.lean`'s `readInventory` reads the file
once with `IO.FS.readBinFile` and everything after it is a pure
function of the resulting `ByteArray`. So `openGraphStore` is the only
`IO` in the whole HDT stack, and `search`, `estimate`, `encode*` and
`decode*` are pure.

## The access-path decision

Two alternatives, matching what the triples stage offers: a bound
subject takes the select-jump straight to its `(predicate, object)`
pairs; everything else — unbound, bound predicate only, bound object
only, bound predicate and object — enumerates and filters afterwards.
The F\* module notes this is an HDT-shaped sibling of the COTTAS
`access_path`, deliberately not a generalisation of it, and the two
stay separate here for the same reason.

## Decode has no failure channel, by contract

Every id reaching `decodeSubject` / `decodePredicate` / `decodeObject`
came from a successful encode or from a navigation result, so the
failure branches are unreachable in practice. They still need a total
value, because the interface these functions replaced was
`Tot subject` / `Tot wf_iri` / `Tot rdf_term`, not an option. The
sentinels are carried across unchanged — `urn:factoidal:hdt-decode-error`
and a `hdt-decode-error` blank node — so a decode failure is VISIBLE in
the output rather than silently dropped, and a `#guard` pins each.
-/
import L4Factoidal.HDT.Triples
import L4Factoidal.RDF.Graph

namespace L4Factoidal.HDT

open L4Factoidal.RDF

/-! ## Summaries -/

inductive BallyhooOrder where
  | spo | sop | pso | pos | osp | ops
  deriving DecidableEq, Repr, Inhabited

structure DictionarySummary where
  numSharedSubjectObject : Nat
  numSubjects   : Nat
  numPredicates : Nat
  numObjects    : Nat
  sizeStrings   : Nat
  deriving Repr, Inhabited

structure TriplesSummary where
  numTriples : Nat
  order      : BallyhooOrder
  deriving Repr, Inhabited

structure Statistics where
  hdtSize      : Nat
  originalSize : Nat
  deriving Repr, Inhabited

structure ArtifactSummary where
  sourceIri  : Option Iri
  dictionary : DictionarySummary
  triples    : TriplesSummary
  statistics : Statistics
  deriving Repr, Inhabited

structure CorpusGraphBinding where
  graphName    : Iri
  artifactPath : String
  deriving Repr, Inhabited

/-! ## The store -/

abbrev TermRef := Nat

structure TpRow where
  s : Option TermRef
  p : Option TermRef
  o : Option TermRef
  deriving Repr, DecidableEq, Inhabited

structure BoundTp where
  s : Option TermRef := none
  p : Option TermRef := none
  o : Option TermRef := none
  deriving Repr, DecidableEq, Inhabited

/-- The decoded file bytes plus the two inventories, all parsed once at
    open time. Every call below is a pure function of this record: no
    mutable state, no external handle. -/
structure GraphStore where
  graphName    : Option Iri
  artifactPath : String
  summary      : Option ArtifactSummary
  bytes        : Bytes
  inventory    : Inventory
  triples      : TriplesInfo

/-- `none` on any structural failure — wrong cookie, CRC mismatch,
    truncation, a non-PFC dictionary section — the same loud-`none`
    contract the two stages document. -/
def openGraphStore (graphName : Option Iri) (artifactPath : System.FilePath)
    (summary : Option ArtifactSummary) : IO (Option GraphStore) := do
  match ← readInventory artifactPath with
  | none => return none
  | some (bytes, inv) =>
      match readTriples bytes inv with
      | none => return none
      | some tri =>
          return some { graphName := graphName,
                        artifactPath := artifactPath.toString,
                        summary := summary, bytes := bytes,
                        inventory := inv, triples := tri }

/-- Nothing to release: the store is immutable data. -/
def closeGraphStore (_ : GraphStore) : Unit := ()

def graphSummary (gs : GraphStore) : Option ArtifactSummary := gs.summary

/-! ## Encoding: term to id -/

def encodeSubject (gs : GraphStore) (subj : Subject) : Option TermRef :=
  termToId gs.bytes gs.inventory .subject subj.toTerm

def encodePredicate (gs : GraphStore) (p : WfIri) : Option TermRef :=
  termToId gs.bytes gs.inventory .predicate (.iri p)

def encodeObject (gs : GraphStore) (o : Term) : Option TermRef :=
  termToId gs.bytes gs.inventory .object o

/-! ## Decoding: id to term

The sentinels below make a decode failure visible in the output. Id 0
is not a valid HDT id, so it is refused before the dictionary is even
consulted. -/

def decodeErrorIri : WfIri :=
  ⟨"urn:factoidal:hdt-decode-error", by simp [isIri, String.isEmpty]⟩

def decodeErrorSubject : Subject := .bnode "hdt-decode-error"
def decodeErrorObject : Term := .bnode "hdt-decode-error"

def decodeTerm (gs : GraphStore) (role : Role) (id : TermRef) :
    Option Term :=
  if id == 0 then none
  else idToTerm gs.bytes gs.inventory role id

def decodeSubject (gs : GraphStore) (id : TermRef) : Subject :=
  match decodeTerm gs .subject id with
  | none => decodeErrorSubject
  | some t => match t.toSubject? with
              | some s => s
              | none => decodeErrorSubject

def decodePredicate (gs : GraphStore) (id : TermRef) : WfIri :=
  match decodeTerm gs .predicate id with
  | some (.iri i) => i
  | _ => decodeErrorIri

def decodeObject (gs : GraphStore) (id : TermRef) : Term :=
  match decodeTerm gs .object id with
  | some t => t
  | none => decodeErrorObject

/-! ## The access path -/

inductive HdtAccessPath where
  | boundSubject (sid : Nat)
  | fullScan
  deriving DecidableEq, Repr, Inhabited

def chooseAccessPath (bound : BoundTp) : HdtAccessPath :=
  match bound.s with
  | none => .fullScan
  | some sid => if sid > 0 then .boundSubject sid else .fullScan

def resolveAccessPath (gs : GraphStore) : HdtAccessPath →
    Option (List IdTriple)
  | .fullScan => enumerateAll gs.bytes gs.triples
  | .boundSubject sid =>
      (triplesForSubject gs.bytes gs.triples sid).map (fun pairs =>
        pairs.map (fun (p, o) => ({ s := sid, p := p, o := o } : IdTriple)))

def idTripleMatches (bound : BoundTp) (t : IdTriple) : Bool :=
  (match bound.s with | none => true | some sid => t.s == sid) &&
  (match bound.p with | none => true | some pid => t.p == pid) &&
  (match bound.o with | none => true | some oid => t.o == oid)

def idTripleToRow (t : IdTriple) : TpRow :=
  { s := some t.s, p := some t.p, o := some t.o }

/-! ## Indexed triple-pattern access -/

def search (gs : GraphStore) (bound : BoundTp) : List TpRow :=
  match resolveAccessPath gs (chooseAccessPath bound) with
  | none => []
  | some triples => (triples.filter (idTripleMatches bound)).map idTripleToRow

def estimate (gs : GraphStore) (bound : BoundTp) : Nat := (search gs bound).length

def predicatePresent (gs : GraphStore) (pred : WfIri) : Bool :=
  match encodePredicate gs pred with
  | none => false
  | some pid => !(search gs { p := some pid }).isEmpty

/-- HDT is a single-graph format in this program's scope, so there is
    no per-graph predicate hint to filter by and every binding stays a
    candidate. The F\* module records that this used to be an
    `assume val` whose only OCaml realisation was already the identity
    regardless of the hint, so no I/O boundary was ever crossed here. -/
def namedCandidateGraphs (bindings : List CorpusGraphBinding)
    (_predicateHint : Option WfIri) : List CorpusGraphBinding := bindings

/-! ## The SPARQL-backend bridge -/

def buildBoundTp (gs : GraphStore) (s : Option Subject) (p : Option WfIri)
    (o : Option Term) : BoundTp :=
  { s := s.bind (encodeSubject gs)
  , p := p.bind (encodePredicate gs)
  , o := o.bind (encodeObject gs) }

def rowToTriple (gs : GraphStore) (row : TpRow) : Option Triple :=
  match row.s, row.p, row.o with
  | some sr, some pr, some orf =>
      some { s := decodeSubject gs sr, p := decodePredicate gs pr,
             o := decodeObject gs orf }
  | _, _, _ => none

def rowsToTriples (gs : GraphStore) (rows : List TpRow) : List Triple :=
  rows.filterMap (rowToTriple gs)

def searchTriples (gs : GraphStore) (s : Option Subject) (p : Option WfIri)
    (o : Option Term) : List Triple :=
  rowsToTriples gs (search gs (buildBoundTp gs s p o))

/-! ## Build-time checks

Opening a store is `IO`, so the fixtures below cover the pure parts:
the access-path decision, the id-triple filter, and the decode
sentinels. `lake exe l4hdt` exercises the whole stack against the
vendored `.hdt` files, and `tools/hdt-tree-differential.sh` compares
its output with the F\* probe's field by field. -/

/-! ### The access-path decision

A bound subject jumps; everything else scans. Id 0 is not a valid HDT
id, so a bound subject of 0 falls back rather than jumping to a
nonexistent row. -/

#guard chooseAccessPath {} == .fullScan
#guard chooseAccessPath { s := some 3 } == .boundSubject 3
#guard chooseAccessPath { s := some 0 } == .fullScan
#guard chooseAccessPath { p := some 2 } == .fullScan
#guard chooseAccessPath { p := some 2, o := some 5 } == .fullScan
#guard chooseAccessPath { s := some 3, p := some 2 } == .boundSubject 3

/-! ### The post-hoc filter

The jump narrows by subject; the filter must still apply every bound
position, because a subject-jump result carries every predicate and
object of that subject. -/

private def t123 : IdTriple := { s := 1, p := 2, o := 3 }

#guard idTripleMatches {} t123
#guard idTripleMatches { s := some 1 } t123
#guard idTripleMatches { s := some 1, p := some 2, o := some 3 } t123
#guard !idTripleMatches { s := some 2 } t123
#guard !idTripleMatches { p := some 9 } t123
#guard !idTripleMatches { o := some 9 } t123
#guard !idTripleMatches { s := some 1, p := some 2, o := some 4 } t123

#guard idTripleToRow t123 == { s := some 1, p := some 2, o := some 3 }

/-! ### A row missing any position yields no triple

`rowToTriple` needs all three. A partial row is dropped rather than
completed with a sentinel — the sentinels are for a decode that was
ATTEMPTED and failed, not for an absent position. -/

#guard (rowsToTriples ⟨none, "", none, ByteArray.empty, default, default⟩
         [{ s := some 1, p := none, o := some 3 }]).length == 0

/-! ### The decode sentinels are distinguishable

A failure is visible in the output. All three sentinels differ from
each other and from any real term. -/

#guard decodeErrorIri.val == "urn:factoidal:hdt-decode-error"
#guard decodeErrorSubject != Subject.bnode "b0"
#guard decodeErrorObject != Term.iri decodeErrorIri
#guard decodeErrorSubject.toTerm == decodeErrorObject

/-! An empty store decodes nothing, and id 0 is refused before the
    dictionary is consulted. -/

private def emptyStore : GraphStore :=
  ⟨none, "", none, ByteArray.empty, default, default⟩

#guard (decodeTerm emptyStore .subject 0).isNone
#guard decodeSubject emptyStore 0 == decodeErrorSubject
#guard decodePredicate emptyStore 7 == decodeErrorIri
#guard decodeObject emptyStore 7 == decodeErrorObject

/-! ### Candidate graphs pass through unchanged -/

#guard (namedCandidateGraphs [⟨"http://e/g", "a.hdt"⟩] none).length == 1
#guard (namedCandidateGraphs [⟨"http://e/g", "a.hdt"⟩]
         (some decodeErrorIri)).length == 1
#guard (namedCandidateGraphs [] none).length == 0

end L4Factoidal.HDT
