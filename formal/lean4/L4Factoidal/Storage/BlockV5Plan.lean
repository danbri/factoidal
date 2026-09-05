/-
L4Factoidal.Storage.BlockV5Plan — the manifest-facing view of one IBK5 block.

Three values of an SBM10 entry are computed from the block and are computed
the SAME way by the packer that writes them and by the activation check that
re-runs them (`docs/designissues/2026-09-05-wire-version-10-scale.md`
sections 6.1 and 6.2, and the rule that encoder admission equals decoder
admission):

* the LGI2 literal index and the GBI1 geometry index, which are built over an
  `Array Term` VIEW of the PTD2 dictionary. An out-of-line literal has no
  lexical form in the block, so it can carry no gram and no bounding box; its
  dictionary slot is replaced by a blank node, which `LiteralGramIndex` and
  `GeoBBoxIndex` both index as nothing, and its POSITION is carried in the
  LGI2 opaque list instead. `LiteralGramIndex.candidatesOpaque?` then returns
  every opaque position for every needle it can serve, which is what keeps the
  candidate list a superset of the matching terms.
* the two zone maps, the smallest and the largest subject (or object) key of
  the block truncated to `ShardManifest.zoneBytes` bytes.

Truncating each key BEFORE the comparison and truncating the smallest key
AFTER it give the same bytes: `lexLe` is preserved by taking a prefix of a
fixed length (`ShardManifestTheorems.lexLe_take`), so the prefix of the
smallest key is a smallest prefix. The fold below truncates first, which is
what keeps a 64 KiB inline literal out of the accumulator.

This module holds no byte layout of its own. It exists because two callers —
`Storage/PackStream.lean` and `Storage/GenerationVerify.lean` — must not each
have their own copy of these rules (iron rule 7 of CLAUDE.md).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.IndexedBlockWireV5
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.LiteralGramIndex
import L4Factoidal.Storage.GeoBBoxIndex

namespace L4Factoidal.Storage.BlockV5Plan

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.TermWireV2
open L4Factoidal.Storage.IndexedBlockWireV5
open L4Factoidal.Storage.IndexedBlockWireV4 (IdQuad)
open L4Factoidal.Storage.ShardManifest (zoneBytes lexLe)

/-! ## The `Array Term` view the two candidate-filter indexes are built over -/

/-- What an out-of-line literal's dictionary slot becomes in the index view.
    A blank node carries no gram (`LiteralGramIndex.foldedOfTerm` gives `[]`
    for every non-literal) and no geometry, and it is not counted by
    `literalCount`, which is the report of how many GRAMMED literals the
    dictionary holds. The position is carried by the opaque list instead. -/
def opaqueSlot : Term := .bnode ""

/-- The PTD2 dictionary as the index builders read it: every inline term as
    it is, every out-of-line literal as `opaqueSlot`. Same size and same
    positions as the dictionary, because the indexes address dictionary
    positions. -/
def inlineDictView (dict : Array WireTerm) : Array Term :=
  dict.map fun w => match w with
    | .inline t => t
    | .blob _ => opaqueSlot

/-- The dictionary positions of the out-of-line literals, ascending and
    distinct. This is LGI2's opaque list. -/
def opaquePositions (dict : Array WireTerm) : List Nat :=
  (dict.toList.zipIdx.filterMap fun (w, i) =>
    match w with
    | .blob _ => some i
    | .inline _ => none)

/-- The LGI2 index of one block: the gram index of the inline view, carrying
    the opaque positions. -/
def literalIndexOf (block : QuadBlock) : LiteralGramIndex.Index :=
  { LiteralGramIndex.build (inlineDictView block.dict) with
    opaqueIds := opaquePositions block.dict }

/-- The GBI1 index of one block. A blob geometry is absent from it by
    construction — its WKT is not in the block — which is why every caller
    that turns a GBI1 candidate set into rows must union the block's opaque
    positions into the candidates first. -/
def geoIndexOf (block : QuadBlock) : GeoBBoxIndex.Index :=
  GeoBBoxIndex.build (inlineDictView block.dict)

/-! ## Zone maps -/

private def zoneGo (dict : Array WireTerm) :
    List Nat → List UInt8 → List UInt8 → Option (List UInt8 × List UInt8)
  | [], lo, hi => some (lo, hi)
  | id :: rest, lo, hi => do
      let term ← dict[id]?
      let key ← keyBytes term
      let bound := key.take zoneBytes
      zoneGo dict rest (if lexLe bound lo then bound else lo)
        (if lexLe hi bound then bound else hi)

/-- The zone bounds over a list of dictionary positions: the smallest and the
    largest key, each truncated to `zoneBytes` bytes.

    `none` for an empty list, which no admitted block produces, and for a
    position whose key cannot be computed, which `IndexedBlockWireV5.supported`
    refuses. The caller reports either as a refusal rather than writing a zone
    map that excludes rows the block holds. -/
def zoneOfIds (dict : Array WireTerm) : List Nat → Option (List UInt8 × List UInt8)
  | [] => none
  | id :: rest => do
      let term ← dict[id]?
      let key ← keyBytes term
      let bound := key.take zoneBytes
      zoneGo dict rest bound bound

/-- The SBM10 subject zone map of a block. -/
def subjectZone? (block : QuadBlock) : Option (List UInt8 × List UInt8) :=
  zoneOfIds block.dict (block.rows.toList.map IdQuad.s)

/-- The SBM10 object zone map of a block. -/
def objectZone? (block : QuadBlock) : Option (List UInt8 × List UInt8) :=
  zoneOfIds block.dict (block.rows.toList.map IdQuad.o)

/-! ## Build-time checks -/

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩

private def bigLexical : String := String.ofList (List.replicate 70000 'a')

private def sampleQuads : List (Option GraphRef × Triple) :=
  [(none, { s := alice, p := pName, o := .literal (Literal.string "hello") }),
   (none, { s := bob, p := pName, o := .literal (Literal.string bigLexical) })]

private def sample : QuadBlock := fromRdfQuads specHash sampleQuads

-- The out-of-line literal is one opaque position and is not grammed.
#guard (opaquePositions sample.dict).length == 1
#guard (literalIndexOf sample).opaqueIds == opaquePositions sample.dict
#guard (literalIndexOf sample).literalCount == 1
#guard (literalIndexOf sample).dictCount == sample.dict.size
#guard (geoIndexOf sample).dictCount == sample.dict.size

-- Both zone maps exist, are ordered, and are inside the bound.
#guard (subjectZone? sample).isSome
#guard (objectZone? sample).isSome
#guard ((subjectZone? sample).map ShardManifest.zoneAdmitted) == some true
#guard ((objectZone? sample).map ShardManifest.zoneAdmitted) == some true

-- Every row's own key is inside the block's bounds.
#guard ((subjectZone? sample).map fun zone =>
  (subjectKeys sample).map fun keys =>
    keys.all fun key => ShardManifest.zoneMayContain zone key) == some (some true)
#guard ((objectZone? sample).map fun zone =>
  (objectKeys sample).map fun keys =>
    keys.all fun key => ShardManifest.zoneMayContain zone key) == some (some true)

end L4Factoidal.Storage.BlockV5Plan
