/-
L4Factoidal.Storage.TermLocalIndex — pure term-to-local-ID lookup meaning.

This is the semantic core for the future TLI1 companion object. IBK3 local
TermIds are never used as global RDF identities: a lookup begins with an RDF
term and returns an ID only after complete structural equality confirms the
matching dictionary entry. The eventual wire format will page these canonical
entries; this module deliberately fixes their order and lookup result first.
-/
import L4Factoidal.Storage.PagedTermDictionary

namespace L4Factoidal.Storage.TermLocalIndex

open L4Factoidal.RDF
open L4Factoidal.Storage.BlockWireV0
open L4Factoidal.Storage.PagedTermDictionary

structure Entry where
  /-- Existing canonical RDF term bytes, retained so a wire index does not
      define a rival spelling of RDF terms. -/
  key : List UInt8
  term : Term
  localId : Nat
  deriving DecidableEq, Repr

private def lessBytes : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | left :: leftRest, right :: rightRest =>
      if left < right then true
      else if left == right then lessBytes leftRest rightRest
      else false

private def before (left right : Entry) : Bool :=
  lessBytes left.key right.key

private def entriesGo : Nat → List Term → List Entry
  | _, [] => []
  | localId, term :: rest =>
      { key := serializeTerm term, term, localId } :: entriesGo (localId + 1) rest

/-- Canonical entries, lexicographically sorted by the established term
    serialization. IDs remain the original PTD1 dictionary positions. -/
def entriesOf (terms : Array Term) : Array Entry :=
  (entriesGo 0 terms.toList).toArray.qsort before

private def lowerBoundGo (entries : Array Entry) (key : List UInt8) (low high : Nat) : Nat → Nat
  | 0 => low
  | fuel + 1 =>
      if low >= high then low
      else
        let middle := low + (high - low) / 2
        match entries[middle]? with
        | none => low
        | some entry =>
            if lessBytes entry.key key then
              lowerBoundGo entries key (middle + 1) high fuel
            else lowerBoundGo entries key low middle fuel

/-- Total canonical lookup. A byte-equal candidate is still checked as an RDF
    term; this remains correct if a future codec or host has a representation
    defect, and records the non-negotiable identity boundary for hash indexes.
    `none` means the term is absent, not that an untrusted local ID is zero. -/
def lookup? (entries : Array Entry) (wanted : Term) : Option Nat :=
  let key := serializeTerm wanted
  let index := lowerBoundGo entries key 0 entries.size (entries.size + 1)
  match entries[index]? with
  | some entry => if entry.key == key && entry.term == wanted then some entry.localId else none
  | none => none

/-- The direct dictionary lookup is the reference contract for a TLI1 decoder
    and range reader. -/
def agreesWithDictionary (terms : Array Term) (wanted : Term) : Bool :=
  lookup? (entriesOf terms) wanted == findTermId? terms wanted

private def ex : WfIri := ⟨"https://example.test/a", by decide⟩
private def ex2 : WfIri := ⟨"https://example.test/b", by decide⟩
private def sample : Array Term := #[.iri ex2, .bnode "b", .iri ex]

#guard lookup? (entriesOf sample) (.iri ex2) == some 0
#guard lookup? (entriesOf sample) (.bnode "b") == some 1
#guard lookup? (entriesOf sample) (.iri ex) == some 2
#guard lookup? (entriesOf sample) (.bnode "missing") == none
#guard agreesWithDictionary sample (.iri ex)
#guard agreesWithDictionary sample (.bnode "missing")

end L4Factoidal.Storage.TermLocalIndex
