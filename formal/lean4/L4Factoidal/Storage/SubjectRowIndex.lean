/-
L4Factoidal.Storage.SubjectRowIndex — total meaning of a predicate-local
subject posting index.

IBK3 keeps source-order ID rows.  A large predicate artifact consequently
needs a subject-to-row access structure before a small driving relation can
join into it without materialising every triple.  This module defines that
structure independently of a wire format.  A later immutable IBK successor
must encode this exact mapping and establish its decode/encode contract before
the query host uses it.

Offsets in a posting list are source-row offsets.  `lookup` restores ascending
source order, so the index does not change the observable physical row order.
-/
import Std.Data.HashMap
import L4Factoidal.Storage.IndexedBlock

namespace L4Factoidal.Storage.SubjectRowIndex

open L4Factoidal.Storage.IndexedBlock

/-- A total in-memory form of the future persisted subject posting index.
    Posting lists accumulate in reverse order so loading remains constant-time
    per row; `lookup` reverses only the selected subject's list. -/
structure Index where
  postings : Std.HashMap TermId (List Nat)

private def addOffset (postings : Std.HashMap TermId (List Nat)) (subject offset : Nat) :
    Std.HashMap TermId (List Nat) :=
  postings.insert subject (offset :: postings.getD subject [])

/-- Tail-recursive construction over source-order rows. -/
private def buildGo : Nat → List IdTriple → Std.HashMap TermId (List Nat) →
    Std.HashMap TermId (List Nat)
  | _, [], postings => postings
  | offset, row :: rest, postings =>
      buildGo (offset + 1) rest (addOffset postings row.s offset)

/-- Build postings for every subject in a predicate-local block. -/
def build (rows : Array IdTriple) : Index :=
  { postings := buildGo 0 rows.toList ∅ }

/-- Source-order row offsets for one subject.  An absent subject is an empty
    posting list, rather than a malformed access request. -/
def lookup (index : Index) (subject : TermId) : List Nat :=
  (index.postings.getD subject []).reverse

/-- The reference meaning of a subject lookup, stated directly over source
    rows.  This is also the oracle used by byte-codec and range-host tests. -/
def expectedOffsets (rows : Array IdTriple) (subject : TermId) : List Nat :=
  rows.toList.zipIdx.filterMap fun (row, offset) =>
    if row.s == subject then some offset else none

/-- Obtain only the original rows named by a subject posting.  Invalid offsets
    cannot be manufactured by `build`; a future byte decoder must reject them
    before calling this function. -/
def rowsForSubject (rows : Array IdTriple) (index : Index) (subject : TermId) : List IdTriple :=
  (lookup index subject).filterMap fun offset => rows[offset]?

end L4Factoidal.Storage.SubjectRowIndex
